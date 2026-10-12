package com.example.myapplication

import android.content.Context
import android.content.SharedPreferences
import java.time.LocalDate
import kotlinx.coroutines.flow.MutableStateFlow
import kotlinx.coroutines.flow.StateFlow
import kotlinx.coroutines.flow.asStateFlow

/**
 * Durable, observable record of authors positively liked by the 星球号 task today.
 *
 * Entries retain both the canonical key used by accessibility deduplication and the original display
 * name shown to the user. Older key-only entries remain readable and are upgraded when seen again.
 */
object PlanetLikeProgressStore {
    private const val PREFS_NAME = "planet_content_like_progress"
    private const val KEY_PREFIX = "authors_"
    private const val ENTRY_SEPARATOR = '\u001F'

    private data class AuthorEntry(val key: String, val displayName: String)

    private var prefs: SharedPreferences? = null
    private val _todayAuthorNames = MutableStateFlow<List<String>>(emptyList())
    val todayAuthorNames: StateFlow<List<String>> = _todayAuthorNames.asStateFlow()

    @Synchronized
    fun init(context: Context) {
        if (prefs == null) {
            prefs = context.applicationContext.getSharedPreferences(PREFS_NAME, Context.MODE_PRIVATE)
        }
        refreshToday()
    }

    @Synchronized
    fun refreshToday() {
        val store = prefs ?: return
        val today = currentEpochDay()
        val activeKey = storageKey(today)
        removeStaleKeys(store, activeKey)
        publishToday(readEntries(store, activeKey))
    }

    /** Returns a detached set safe for the service to merge into its per-attempt consumed authors. */
    @Synchronized
    fun authorKeysForDay(epochDay: Long): Set<String> {
        val store = prefs ?: return emptySet()
        val key = storageKey(epochDay)
        removeStaleKeys(store, key)
        val entries = readEntries(store, key)
        if (epochDay == currentEpochDay()) publishToday(entries)
        return entries.mapTo(linkedSetOf()) { it.key }
    }

    /** Persists one verified author and returns the number of unique authors stored for that day. */
    @Synchronized
    fun recordVerifiedAuthor(epochDay: Long, canonicalKey: String, displayName: String): Int {
        val store = prefs ?: return 0
        val key = storageKey(epochDay)
        val entries = readEntries(store, key).associateByTo(linkedMapOf()) { it.key }
        entries[canonicalKey] = AuthorEntry(
            key = canonicalKey,
            displayName = displayName.replace(ENTRY_SEPARATOR, ' ').trim().ifEmpty { canonicalKey },
        )
        val encoded = entries.values.mapTo(linkedSetOf(), ::encode)
        store.edit().putStringSet(key, encoded).apply()
        if (epochDay == currentEpochDay()) publishToday(entries.values)
        return entries.size
    }

    fun currentEpochDay(): Long = LocalDate.now().toEpochDay()

    private fun storageKey(epochDay: Long): String = "$KEY_PREFIX$epochDay"

    private fun readEntries(store: SharedPreferences, key: String): List<AuthorEntry> {
        val rawEntries = store.getStringSet(key, emptySet()).orEmpty().toSet()
        val entries = rawEntries.mapNotNull(::decode).distinctBy { it.key }
        val encodedEntries = entries.mapTo(linkedSetOf(), ::encode)
        // Upgrade legacy key-only values immediately. Their original capitalization is unavailable,
        // so the canonical key is the honest display fallback until a future verified write replaces it.
        if (rawEntries != encodedEntries) {
            store.edit().putStringSet(key, encodedEntries).apply()
        }
        return entries
    }

    private fun encode(entry: AuthorEntry): String =
        "${entry.key}$ENTRY_SEPARATOR${entry.displayName}"

    private fun decode(raw: String): AuthorEntry? {
        val separator = raw.indexOf(ENTRY_SEPARATOR)
        val canonicalKey = if (separator >= 0) raw.substring(0, separator) else raw
        if (canonicalKey.isBlank()) return null
        val displayName = if (separator >= 0) raw.substring(separator + 1) else canonicalKey
        return AuthorEntry(canonicalKey, displayName.ifBlank { canonicalKey })
    }

    private fun publishToday(entries: Collection<AuthorEntry>) {
        _todayAuthorNames.value = entries
            .sortedWith(compareBy(String.CASE_INSENSITIVE_ORDER) { it.displayName })
            .map { it.displayName }
    }

    private fun removeStaleKeys(store: SharedPreferences, activeKey: String) {
        val staleKeys = store.all.keys.filter { it.startsWith(KEY_PREFIX) && it != activeKey }
        if (staleKeys.isEmpty()) return
        store.edit().apply { staleKeys.forEach { remove(it) } }.apply()
    }
}

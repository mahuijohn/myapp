package com.example.myapplication

import android.content.Context
import kotlinx.coroutines.flow.MutableStateFlow
import kotlinx.coroutines.flow.StateFlow
import kotlinx.coroutines.flow.asStateFlow

/**
 * User-editable automation settings, shared between the UI and [LauncherAccessibilityService].
 *
 * Backed by SharedPreferences so the lists survive restarts, and exposed as [StateFlow]s so the editor
 * and the service always agree without either having to poll.
 *
 * Two lists, and the whitelist wins:
 * - **skip** entries mean "do not press this", matched against a task's button and title;
 * - **whitelist** entries mean "run this anyway", matched against a task's title and description, and
 *   they override both the skip list and the built-in one. That is what lets a task like
 *   浏览能量大富翁15s run even though its 去完成 button would otherwise be skipped.
 */
object AutomationSettings {

    private const val PREFS_NAME = "automation_settings"
    private const val KEY_SKIP_TEXTS = "skip_texts"
    private const val KEY_WHITELIST_TEXTS = "whitelist_texts"

    /** Tasks worth doing even when their button looks skippable. */
    const val DEFAULT_WHITELIST = "浏览能量大富翁"

    /** Anything in this set of characters separates one entry from the next. */
    private val SEPARATORS = Regex("[\\n\\r,，;；、\\s]+")

    private var prefs: android.content.SharedPreferences? = null

    private val _skipTextsRaw = MutableStateFlow("")
    private val _skipTexts = MutableStateFlow<List<String>>(emptyList())
    private val _whitelistTextsRaw = MutableStateFlow("")
    private val _whitelistTexts = MutableStateFlow<List<String>>(emptyList())

    /** Exactly what the user typed, so the editors can show it back unchanged. */
    val skipTextsRaw: StateFlow<String> = _skipTextsRaw.asStateFlow()
    val whitelistTextsRaw: StateFlow<String> = _whitelistTextsRaw.asStateFlow()

    /** The parsed entries the service matches against. */
    val skipTexts: StateFlow<List<String>> = _skipTexts.asStateFlow()
    val whitelistTexts: StateFlow<List<String>> = _whitelistTexts.asStateFlow()

    /** Safe to call more than once; both the activity and the service do. */
    fun init(context: Context) {
        if (prefs != null) return
        val store = context.applicationContext.getSharedPreferences(PREFS_NAME, Context.MODE_PRIVATE)
        prefs = store
        setSkipTextsRaw(store.getString(KEY_SKIP_TEXTS, "").orEmpty(), persist = false)
        // The default only applies until the user saves something of their own, including a blank.
        setWhitelistTextsRaw(
            store.getString(KEY_WHITELIST_TEXTS, DEFAULT_WHITELIST).orEmpty(),
            persist = false
        )
    }

    fun setSkipTextsRaw(raw: String, persist: Boolean = true) {
        _skipTextsRaw.value = raw
        _skipTexts.value = parse(raw)
        if (persist) prefs?.edit()?.putString(KEY_SKIP_TEXTS, raw)?.apply()
    }

    fun setWhitelistTextsRaw(raw: String, persist: Boolean = true) {
        _whitelistTextsRaw.value = raw
        _whitelistTexts.value = parse(raw)
        if (persist) prefs?.edit()?.putString(KEY_WHITELIST_TEXTS, raw)?.apply()
    }

    /** Whether any of [fields] contains one of the user's skip entries. */
    fun matchesSkip(vararg fields: String): Boolean = matches(_skipTexts.value, fields)

    /** Whether any of [fields] contains a whitelist entry, i.e. run this task regardless. */
    fun matchesWhitelist(vararg fields: String): Boolean = matches(_whitelistTexts.value, fields)

    private fun matches(entries: List<String>, fields: Array<out String>): Boolean {
        if (entries.isEmpty()) return false
        return entries.any { entry -> fields.any { it.contains(entry, ignoreCase = true) } }
    }

    private fun parse(raw: String): List<String> =
        raw.split(SEPARATORS).map { it.trim() }.filter { it.isNotEmpty() }
}

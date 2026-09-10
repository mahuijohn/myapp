package com.example.myapplication

import android.graphics.Bitmap
import android.util.Log
import kotlinx.coroutines.flow.MutableStateFlow
import kotlinx.coroutines.flow.StateFlow
import kotlinx.coroutines.flow.asStateFlow
import java.text.SimpleDateFormat
import java.util.Date
import java.util.Locale

/**
 * Process-wide, append-only log shared between [LauncherAccessibilityService] and the UI.
 *
 * Entries have stable IDs so an asynchronous failure screenshot can update the same row that
 * requested it. Screenshots stay in memory only and a small retention cap prevents repeated failures
 * from keeping full screen images alive for the rest of the process.
 */
object AutomationLog {

    private const val TAG = "AutomationLog"
    private const val MAX_ENTRIES = 1000
    private const val MAX_READY_SCREENSHOTS = 3

    /** Styling category for a log line. */
    enum class Kind {
        INFO,
        SECTION,
        RUN,
        RUN_END,
        ERROR,
    }

    /** Optional visual diagnostic attached to one failure row. */
    sealed class ScreenshotState {
        data object Pending : ScreenshotState()
        data class Ready(val bitmap: Bitmap) : ScreenshotState()
        data class Unavailable(val reason: String) : ScreenshotState()
        data object Released : ScreenshotState()
    }

    /** Immutable rectangle snapshot safe to retain after an accessibility node is recycled. */
    data class BoundsSnapshot(
        val left: Int,
        val top: Int,
        val right: Int,
        val bottom: Int,
    ) {
        fun shortString(): String = "[$left,$top][$right,$bottom]"
    }

    data class DumpNode(
        val depth: Int,
        val className: String,
        val text: String,
        val contentDescription: String,
        val viewId: String,
        val clickable: Boolean,
        val bounds: BoundsSnapshot,
    )

    /** Structured accessibility hierarchy attached to one compact log entry. */
    data class WindowDump(
        val reason: String,
        val windowPackage: String,
        val rootBounds: BoundsSnapshot,
        val nodes: List<DumpNode>,
        val truncated: Boolean,
    )

    data class Entry(
        val id: Long,
        val timestamp: String,
        val message: String,
        val kind: Kind,
        val screenshot: ScreenshotState? = null,
        val windowDump: WindowDump? = null,
    )

    private val timeFormat = SimpleDateFormat("HH:mm:ss.SSS", Locale.US)
    private val _entries = MutableStateFlow<List<Entry>>(emptyList())

    /** Live view of the log, oldest entry first. */
    val entries: StateFlow<List<Entry>> = _entries.asStateFlow()

    private val _activeMode = MutableStateFlow<AutomationMode?>(null)
    val activeMode: StateFlow<AutomationMode?> = _activeMode.asStateFlow()

    private val _showLogRequests = MutableStateFlow(0)
    val showLogRequests: StateFlow<Int> = _showLogRequests.asStateFlow()

    private var runCount = 0
    private var nextEntryId = 1L

    fun requestShowLog() {
        _showLogRequests.value = _showLogRequests.value + 1
    }

    @Synchronized
    fun startRun(label: String) {
        runCount++
        add("RUN #$runCount · $label", Kind.RUN)
    }

    @Synchronized
    fun endRun(message: String) {
        add(message, Kind.RUN_END)
    }

    /** Appends an ordinary line, inferring error styling for familiar terminal wording. */
    @Synchronized
    fun append(message: String) {
        add(message, if (looksLikeFailure(message)) Kind.ERROR else Kind.INFO)
    }

    @Synchronized
    fun appendSection(title: String) {
        add(title, Kind.SECTION)
    }

    /** Adds one compact log row whose full hierarchy is opened on the dump detail page. */
    @Synchronized
    fun appendWindowDump(dump: WindowDump): Long {
        val suffix = if (dump.truncated) ", truncated" else ""
        return add(
            message = "Node dump: ${dump.reason} (${dump.nodes.size} nodes$suffix)",
            kind = Kind.INFO,
            windowDump = dump,
        ).id
    }

    /** Adds the failure row immediately so the later screenshot stays at the failure point. */
    @Synchronized
    fun beginTaskFailure(title: String, reason: String): Long =
        add(
            message = "Task failed: '$title' — $reason",
            kind = Kind.ERROR,
            screenshot = ScreenshotState.Pending,
        ).id

    /** Replaces a pending attachment and enforces the in-memory image retention limit. */
    @Synchronized
    fun completeScreenshot(entryId: Long, bitmap: Bitmap): Boolean {
        var updated = false
        var next = _entries.value.map { entry ->
            if (entry.id == entryId && entry.screenshot == ScreenshotState.Pending) {
                updated = true
                entry.copy(screenshot = ScreenshotState.Ready(bitmap))
            } else {
                entry
            }
        }
        if (!updated) return false

        val readyIndexes = next.indices.filter { next[it].screenshot is ScreenshotState.Ready }
        val releaseCount = (readyIndexes.size - MAX_READY_SCREENSHOTS).coerceAtLeast(0)
        if (releaseCount > 0) {
            val releaseIndexes = readyIndexes.take(releaseCount).toSet()
            next = next.mapIndexed { index, entry ->
                if (index in releaseIndexes) entry.copy(screenshot = ScreenshotState.Released) else entry
            }
        }
        _entries.value = next
        return true
    }

    @Synchronized
    fun failScreenshot(entryId: Long, reason: String) {
        _entries.value = _entries.value.map { entry ->
            if (entry.id == entryId && entry.screenshot == ScreenshotState.Pending) {
                entry.copy(screenshot = ScreenshotState.Unavailable(reason))
            } else {
                entry
            }
        }
    }

    /** Plain-text representation used by the explicit Copy all action. */
    fun plainText(entriesSnapshot: List<Entry>): String =
        entriesSnapshot.joinToString("\n") { entry ->
            val attachment = when (entry.screenshot) {
                is ScreenshotState.Pending -> " [screenshot pending]"
                is ScreenshotState.Ready -> " [screenshot attached]"
                is ScreenshotState.Unavailable ->
                    " [screenshot unavailable: ${entry.screenshot.reason}]"
                ScreenshotState.Released -> " [screenshot released]"
                null -> ""
            }
            val dump = entry.windowDump?.let { "\n${windowDumpPlainText(it)}" }.orEmpty()
            "${entry.timestamp} ${entry.message}$attachment$dump"
        }

    fun windowDumpPlainText(dump: WindowDump): String = buildString {
        appendLine("  reason: ${dump.reason}")
        appendLine("  window: ${dump.windowPackage}")
        appendLine("  root: ${dump.rootBounds.shortString()}")
        appendLine("  nodes: ${dump.nodes.size}${if (dump.truncated) " (truncated)" else ""}")
        dump.nodes.forEachIndexed { index, node ->
            append("  ")
            append("  ".repeat(node.depth.coerceAtMost(12)))
            append("#${index + 1} ${node.className}")
            append(" ${node.bounds.shortString()}")
            if (node.clickable) append(" clickable")
            appendLine()
            if (node.text.isNotEmpty()) appendLine("      text: ${node.text}")
            if (node.contentDescription.isNotEmpty()) {
                appendLine("      description: ${node.contentDescription}")
            }
            if (node.viewId.isNotEmpty()) appendLine("      id: ${node.viewId}")
        }
    }.trimEnd()

    @Synchronized
    fun clear() {
        // Dropping references lets the retained software bitmaps be reclaimed safely by the runtime.
        _entries.value = emptyList()
        runCount = 0
    }

    fun setActiveMode(mode: AutomationMode?) {
        _activeMode.value = mode
    }

    private fun add(
        message: String,
        kind: Kind,
        screenshot: ScreenshotState? = null,
        windowDump: WindowDump? = null,
    ): Entry {
        Log.d(TAG, message)
        val entry = Entry(
            id = nextEntryId++,
            timestamp = timeFormat.format(Date()),
            message = message,
            kind = kind,
            screenshot = screenshot,
            windowDump = windowDump,
        )
        val next = _entries.value + entry
        _entries.value = if (next.size > MAX_ENTRIES) next.takeLast(MAX_ENTRIES) else next
        return entry
    }

    private fun looksLikeFailure(message: String): Boolean =
        message.contains("Failed", ignoreCase = true) ||
                message.contains("could not", ignoreCase = true) ||
                message.startsWith("Stopped by")
}

package com.example.myapplication

import android.accessibilityservice.AccessibilityService
import android.accessibilityservice.AccessibilityServiceInfo
import android.accessibilityservice.GestureDescription
import android.app.ActivityManager
import android.app.NotificationChannel
import android.app.NotificationManager
import android.app.PendingIntent
import android.content.ComponentName
import android.content.Context
import android.content.Intent
import android.content.pm.PackageManager
import android.content.res.ColorStateList
import android.provider.Settings
import android.graphics.Bitmap
import android.graphics.Color
import android.graphics.Path
import android.graphics.PixelFormat
import android.graphics.Rect
import android.graphics.drawable.GradientDrawable
import android.graphics.drawable.RippleDrawable
import android.os.Build
import android.os.Handler
import android.os.Looper
import android.os.Process
import android.os.SystemClock
import android.util.Log
import android.view.Display
import android.view.Gravity
import android.view.KeyEvent
import android.view.MotionEvent
import android.view.View
import android.view.ViewConfiguration
import android.view.WindowInsets
import android.view.WindowManager
import android.view.accessibility.AccessibilityEvent
import android.view.accessibility.AccessibilityNodeInfo
import android.widget.ImageButton
import android.widget.ImageView
import android.widget.LinearLayout
import android.widget.Toast
import android.Manifest
import androidx.core.content.ContextCompat
import androidx.core.app.NotificationCompat
import java.util.concurrent.Executors
import java.util.concurrent.atomic.AtomicBoolean
import kotlin.math.abs
import kotlin.math.max
import kotlin.math.roundToInt
import kotlin.random.Random

class LauncherAccessibilityService : AccessibilityService() {
    /** Data-driven interaction for a task that opens a WeChat mini-program landing page. */
    private data class NormalizedRect(
        val left: Float,
        val top: Float,
        val right: Float,
        val bottom: Float,
    )

    private data class MiniProgramPromptSpec(
        /** Required fragments of the native WeChat launch-dialog title. */
        val markers: List<String>,
        val positiveText: String,
    )

    private data class MiniProgramTaskSpec(
        val id: String,
        val taskTitle: Regex,
        val ctaText: Regex,
        val ctaDescription: String,
        val ctaFallback: NormalizedRect,
        val expectedPackages: Set<String> = setOf(WECHAT_PACKAGE),
        val prompt: MiniProgramPromptSpec? = null,
    )

    private var notificationShown = false
    private val NOTIF_CHANNEL_ID = "automation_channel"
    private val NOTIF_ID = 1001
    private val mainHandler = Handler(Looper.getMainLooper())
    private val screenshotExecutor = Executors.newSingleThreadExecutor()
    private var screenshotInFlight = false
    /** The manual dump overlay is opt-in and starts hidden after every service/process start. */
    private var dumpToolRequested = false
    private var dumpToolView: View? = null
    private val windowManager: WindowManager by lazy {
        getSystemService(Context.WINDOW_SERVICE) as WindowManager
    }
    private enum class UnlikeUnfollowState {
        IDLE,
        SETTLING_LIST,
        VERIFYING_DETAIL,
        UNLIKING,
        VERIFYING_UNLIKE,
        RETURNING,
        WAITING_FOR_LIST_REFRESH,
    }

    private enum class UnlikeUnfollowWaypoint(val displayName: String) {
        LIKED_LIST("我赞过的"),
        PROFILE_HOME("profile home"),
        MINE_PAGE("我的"),
        BOTTOM_HOME("Ctrip home"),
        UNKNOWN("unknown/deep page"),
    }

    private var unlikeUnfollowState = UnlikeUnfollowState.IDLE
    private var selectedLikedCardTitle: String? = null
    /** A card is never opened twice during one run; an uncertain toggle must not become a re-like. */
    private val attemptedLikedCards = mutableSetOf<String>()
    private var unlikeSucceededCount = 0
    private var unlikeAmbiguousCount = 0
    private var unlikeUnsupportedCount = 0
    private var unlikeListScrolls = 0
    /** Consecutive accepted swipes that left the same all-attempted viewport visible. */
    private var unlikeNoMoveScrolls = 0
    private var unlikeLastVisibleSignature: Set<String> = emptySet()
    private var targetPackageName: String? = null
    private var targetLabel: String? = null
    private var activeAutomationMode: AutomationMode? = null
    /** Invalidates delayed callbacks from an earlier Unlike & Unfollow diagnostic run. */
    private var unlikeUnfollowToken = 0L
    private val actionLog = mutableListOf<String>()
    private var shouldClickElement = false
    // If true, a manual user action was detected and automation should stop for current package
    private var manualInterruptionDetected = false
    // track last observed package to detect back gestures (package changed from target)
    private var lastObservedPackage: String? = null
    private var clickAttempts = 0
    private var currentDelayMs = 500L
    private val maxClickAttempts = 8

    // Multi-package support: list of packages that match the target label and current index
    private var targetPackages: List<String> = emptyList()
    private var currentTargetIndex = 0
    private val overallResults = mutableListOf<String>()

    // Guards so the 我的 flow starts exactly once per launched app, and so a burst of chooser events
    // cannot produce a burst of chooser clicks.
    private var mineFlowStarted = false
    private var lastChooserClickAt = 0L
    /** Startup-only recovery; it never records task completion. */
    private var startupRecoveryActive = false
    private var startupBackPresses = 0
    private var startupUnknownSignature: Set<String> = emptySet()
    private var startupUnknownHits = 0
    private var startupUnreadablePolls = 0
    // One node dump per run is plenty; it exists to explain a missed selection, not to spam.
    private var chooserDumped = false
    /** Captured once on the initial verified task-list entry, before claims or task execution. */
    private var initialTaskListDumped = false

    // --- task loop state ---
    /** Titles already attempted, so re-scrolling the list cannot run a task twice. */
    private val processedTasks = mutableSetOf<String>()
    private var tasksStarted = 0
    private var taskScrolls = 0
    /** Page content at the previous scroll, used to tell "the list moved" from "it did not". */
    private var lastPageSignature: Set<String> = emptySet()
    /** True while a task has us in another app, so leaving is not read as a user interruption. */
    private var expectingExternalApp = false
    /**
     * Packages a task took us through, to be closed when it ends. A set rather than one value because
     * a task can chain through more than one app.
     */
    private val taskApps = mutableSetOf<String>()
    /** Async Recents cleanup must finish before the current task can be marked done. */
    private var taskAppCleanupInProgress = false
    private var taskAppCleanupToken = 0L
    /** Non-target package being sampled; it must remain stable before it is treated as a task app. */
    private var externalTaskCandidate: String? = null
    private var externalTaskCandidateHits = 0
    /** Set while a browser prompt is handing an ordinary task off to another installed app. */
    private var externalTaskCandidateSinceMs = 0L
    private var externalHandoffSourcePackage: String? = null
    private var externalHandoffDeadlineMs = 0L
    private var externalHandoffClickAtMs = 0L
    private var externalHandoffTargetCandidate: String? = null
    private var externalHandoffTargetHits = 0
    /** Set only after a real external package is observed repeatedly, never for a transient overlay. */
    private var confirmedExternalTaskApp: String? = null
    /** True only while a task is running, so the launcher is never recorded as a task app. */
    private var capturingTaskApps = false
    /** Active data-driven WeChat mini-program watcher, independent of generic app confirmation. */
    private var activeMiniProgramSpec: MiniProgramTaskSpec? = null
    private var miniProgramWatchToken = 0L
    private var miniProgramObservedPackage: String? = null
    private var miniProgramDumpCaptured = false
    private var miniProgramWatchFinished = false
    private var miniProgramCtaTapped = false
    private var miniProgramPromptObserved = false
    private var miniProgramPromptFinished = false

    // Clicks spent on the navigation step currently in flight, so a step whose tap does not register
    // can be retried a bounded number of times.
    private var stepClicksIndex = -1
    private var stepClicks = 0
    private enum class TaskEntryStepState { IDLE, ACTIVE, COMPLETE, FAILED }
    private var taskEntryStepState = TaskEntryStepState.IDLE
    private var taskEntryStepDeadlineMs = 0L

    // --- run bookkeeping, for the stall watchdog and the closing summary ---
    private var runActive = false
    private var runStartedAt = 0L
    private var watchdogDeadline = 0L
    private var currentTaskTitle: String? = null
    /** Dedicated interaction state for titles matching 关注…星球号. */
    private enum class PlanetFollowState { IDLE, WAITING_FOR_CONTROL, RETURNING }
    private var planetFollowState = PlanetFollowState.IDLE
    private var planetFollowDeadlineMs = 0L
    /** Dedicated in-app flow for 点击浏览任意上榜酒店. */
    private enum class HotelRankingState { IDLE, WAITING_FOR_DATA, VERIFYING_NAVIGATION, RETURNING }
    private var hotelRankingState = HotelRankingState.IDLE
    private var hotelRankingDeadlineMs = 0L
    private var hotelRankingSourceSignature: Set<String> = emptySet()
    private var hotelRankingMarkerText: String? = null
    private var hotelRankingNavigationHits = 0
    private var hotelRankingTapAttempt = 0
    private var hotelRankingVerificationPolls = 0
    private var hotelRankingDiagnosticsDumped = false
    /** Dedicated in-app flow for 天天领现金-浏览笔记. */
    private enum class DailyCashNoteState {
        IDLE, WAITING_FOR_DESTINATION, WAITING_FOR_SCROLL, FINDING_CARD,
        VERIFYING_NOTE, DWELLING, RETURNING
    }
    private var dailyCashNoteState = DailyCashNoteState.IDLE
    private var dailyCashNoteDeadlineMs = 0L
    private var dailyCashDestinationHits = 0
    private var dailyCashScrollAnchorTop: Int? = null
    private var dailyCashNavigationSignature: Set<String> = emptySet()
    private var dailyCashNavigationHits = 0
    private var dailyCashDwellSeconds = 0
    private var dailyCashDiagnosticsDumped = false
    /** Invalidates callbacks from a completed/stopped task or an earlier run. */
    private var dailyCashTaskToken = 0L
    private val taskResults = mutableListOf<Pair<String, String>>()
    private val skippedTasks = mutableSetOf<String>()
    /** Completion phases keep the final claim and its mandatory refreshed-list rescan distinct. */
    private enum class TaskLoopPhase { SCANNING, CLAIMING, RESCANNING, FINISHED }

    private var taskLoopPhase = TaskLoopPhase.SCANNING
    /** Number of tasks already started when the current post-claim rescan began. */
    private var postClaimRescanBaseline = 0
    private var finalClaimPasses = 0
    /** Timestamp of the latest toast/event saying that 一键领 has nothing available. */
    private var lastNoClaimRewardAt = 0L
    /** Titles left alone because their button is on the ignore list. */
    private val ignoredTasks = mutableSetOf<String>()
    private val closedApps = mutableListOf<String>()

    /** Default launcher, which must never be killed after HOME brings it to the front. */
    private val launcherPackage: String? by lazy {
        try {
            packageManager.resolveActivity(
                Intent(Intent.ACTION_MAIN).addCategory(Intent.CATEGORY_HOME),
                PackageManager.ResolveInfoFlags.of(PackageManager.MATCH_DEFAULT_ONLY.toLong())
            )?.activityInfo?.packageName
        } catch (_: Exception) {
            null
        }
    }

    /**
     * True only while the accessibility framework has this service bound.
     *
     * `startService(...)` from the app will happily create and run this service even when the user
     * has not enabled it under Settings > Accessibility. In that state there is no accessibility
     * connection, so `rootInActiveWindow` and `windows` are always empty and every node lookup
     * fails silently. Tracking the real connection lets us say so instead of retrying blindly.
     */
    private var serviceConnected = false

    override fun onServiceConnected() {
        super.onServiceConnected()
        serviceConnected = true
        AutomationSettings.init(this)
        serviceInfo = AccessibilityServiceInfo().apply {
            eventTypes = AccessibilityEvent.TYPE_WINDOW_STATE_CHANGED or
                    AccessibilityEvent.TYPE_WINDOW_CONTENT_CHANGED or
                    AccessibilityEvent.TYPE_VIEW_CLICKED or
                    // Toasts such as “暂无可领取奖励~” are reported as notification-state events.
                    AccessibilityEvent.TYPE_NOTIFICATION_STATE_CHANGED
            feedbackType = AccessibilityServiceInfo.FEEDBACK_GENERIC
            // FLAG_INCLUDE_NOT_IMPORTANT_VIEWS matters for system pickers: the icon rows of the
            // "dual apps" chooser are often flagged as not important for accessibility and would
            // otherwise be invisible to node searches.
            flags = AccessibilityServiceInfo.FLAG_REPORT_VIEW_IDS or
                    AccessibilityServiceInfo.FLAG_RETRIEVE_INTERACTIVE_WINDOWS or
                    AccessibilityServiceInfo.FLAG_INCLUDE_NOT_IMPORTANT_VIEWS or
                    AccessibilityServiceInfo.FLAG_REQUEST_FILTER_KEY_EVENTS
        }
        logProgress("Accessibility service connected")
        if (dumpToolRequested) showDumpTool()
    }

    override fun onUnbind(intent: Intent?): Boolean {
        serviceConnected = false
        dumpToolRequested = false
        hideDumpTool()
        resetUnlikeUnfollowManualState()
        logProgress("Accessibility service disconnected")
        return super.onUnbind(intent)
    }

    override fun onDestroy() {
        startupRecoveryActive = false
        unlikeUnfollowToken++
        dumpToolRequested = false
        hideDumpTool()
        resetUnlikeUnfollowManualState()
        if (runActive || activeAutomationMode != null) {
            runActive = false
            activeAutomationMode = null
            AutomationLog.setActiveMode(null)
        }
        mainHandler.removeCallbacksAndMessages(null)
        screenshotExecutor.shutdownNow()
        super.onDestroy()
    }

    /**
     * All window roots currently readable, topmost first.
     *
     * `rootInActiveWindow` on its own is not enough: it only returns the window the framework
     * considers *active*, and a system dialog such as the dual-app picker frequently is not that
     * window, so the call returns null while the dialog is plainly on screen. Walking [getWindows]
     * (enabled by FLAG_RETRIEVE_INTERACTIVE_WINDOWS) covers those cases.
     */
    private fun currentRoots(): List<AccessibilityNodeInfo> {
        val roots = mutableListOf<AccessibilityNodeInfo>()
        // Our own windows are never a target. The Logging screen echoes every step name back, so its
        // text contains the very strings the flow searches for — without this filter a step can match
        // its own log line and "click" that instead of the app.
        fun addable(node: AccessibilityNodeInfo): Boolean =
            node.packageName?.toString() != packageName
        try { rootInActiveWindow?.takeIf { addable(it) }?.let { roots.add(it) } } catch (_: Exception) {}
        try {
            val ws = windows ?: emptyList()
            // Topmost window first so a dialog wins over the activity behind it.
            for (w in ws.sortedByDescending { runCatching { it.layer }.getOrDefault(0) }) {
                val r = try { w.root } catch (_: Exception) { null } ?: continue
                if (addable(r) && roots.none { it == r }) roots.add(r)
            }
        } catch (_: Exception) {}
        return roots
    }

    /**
     * Best root for searching in-app content: the target app's own window when it is readable,
     * otherwise the front-most window. Used everywhere in place of bare `rootInActiveWindow`.
     */
    /** The target app's readable window, even when a transient system overlay is layered above it. */
    private fun targetAppRoot(): AccessibilityNodeInfo? {
        val target = targetPackageName ?: return null
        return currentRoots().firstOrNull { it.packageName?.toString() == target }
    }

    private fun appRoot(): AccessibilityNodeInfo? {
        val roots = currentRoots()
        return roots.firstOrNull { it.packageName?.toString() == targetPackageName } ?: roots.firstOrNull()
    }

    /** Package of the front-most readable window, or null when no window content is available. */
    private fun foregroundPackage(): String? =
        currentRoots().firstNotNullOfOrNull { it.packageName?.toString() }

    /** Whether the user has enabled this service under Settings > Accessibility. */
    private fun isAccessibilityServiceEnabled(): Boolean {
        return try {
            val enabled = Settings.Secure.getString(
                contentResolver, Settings.Secure.ENABLED_ACCESSIBILITY_SERVICES
            ) ?: return false
            val component = ComponentName(this, LauncherAccessibilityService::class.java)
            enabled.split(':').any {
                val entry = it.trim()
                entry.equals(component.flattenToString(), ignoreCase = true) ||
                        entry.equals(component.flattenToShortString(), ignoreCase = true)
            }
        } catch (_: Exception) {
            false
        }
    }

    /** Adds the opt-in accessibility overlay without requesting draw-over-other-apps permission. */
    private fun showDumpTool() {
        if (dumpToolView != null) return
        if (!serviceConnected) {
            AutomationLog.append(
                "Dump tool unavailable: enable the accessibility service, then tap Start Dump again"
            )
            runCatching {
                Toast.makeText(
                    applicationContext,
                    "Enable the accessibility service before starting Dump",
                    Toast.LENGTH_LONG,
                ).show()
            }
            return
        }

        val container = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER
            setPadding(
                dpToPx(DUMP_TOOL_CARD_PADDING_HORIZONTAL_DP),
                dpToPx(DUMP_TOOL_CARD_PADDING_VERTICAL_DP),
                dpToPx(DUMP_TOOL_CARD_PADDING_HORIZONTAL_DP),
                dpToPx(DUMP_TOOL_CARD_PADDING_VERTICAL_DP),
            )
            background = GradientDrawable(
                GradientDrawable.Orientation.TL_BR,
                intArrayOf(0xF22E3448.toInt(), 0xF21B1E2B.toInt()),
            ).apply {
                cornerRadius = dpToPx(DUMP_TOOL_CARD_RADIUS_DP).toFloat()
                setStroke(dpToPx(DUMP_TOOL_STROKE_DP), 0x3DFFFFFF)
            }
            elevation = dpToPx(DUMP_TOOL_ELEVATION_DP).toFloat()
            clipToOutline = true
        }

        fun iconBackground(accentColor: Int): RippleDrawable {
            val content = GradientDrawable().apply {
                shape = GradientDrawable.RECTANGLE
                cornerRadius = dpToPx(DUMP_TOOL_BUTTON_RADIUS_DP).toFloat()
                setColor(accentColor)
            }
            val mask = GradientDrawable().apply {
                shape = GradientDrawable.RECTANGLE
                cornerRadius = dpToPx(DUMP_TOOL_BUTTON_RADIUS_DP).toFloat()
                setColor(Color.WHITE)
            }
            return RippleDrawable(
                ColorStateList.valueOf(0x66FFFFFF),
                content,
                mask,
            )
        }

        fun iconButton(
            iconRes: Int,
            descriptionRes: Int,
            accentColor: Int,
            onClick: () -> Unit,
        ): ImageButton = ImageButton(this).apply {
            setImageResource(iconRes)
            imageTintList = ColorStateList.valueOf(Color.WHITE)
            contentDescription = getString(descriptionRes)
            tooltipText = contentDescription
            importantForAccessibility = View.IMPORTANT_FOR_ACCESSIBILITY_YES
            scaleType = ImageView.ScaleType.CENTER
            setPadding(
                dpToPx(DUMP_TOOL_ICON_PADDING_DP),
                dpToPx(DUMP_TOOL_ICON_PADDING_DP),
                dpToPx(DUMP_TOOL_ICON_PADDING_DP),
                dpToPx(DUMP_TOOL_ICON_PADDING_DP),
            )
            background = iconBackground(accentColor)
            isClickable = true
            isFocusable = true
            setOnClickListener { onClick() }
        }

        val closeButton = iconButton(
            iconRes = R.drawable.ic_close_24,
            descriptionRes = R.string.dump_tool_close,
            accentColor = 0x40FF5F73,
        ) {
            dumpToolRequested = false
            hideDumpTool()
            AutomationLog.append("Floating dump tool closed")
        }
        val dumpButton = iconButton(
            iconRes = R.drawable.ic_dump_24,
            descriptionRes = R.string.dump_tool_capture,
            accentColor = 0x405C8DFF,
        ) {
            captureManualWindowDump()
        }
        val buttonSize = dpToPx(DUMP_TOOL_BUTTON_SIZE_DP)
        container.addView(
            closeButton,
            LinearLayout.LayoutParams(buttonSize, buttonSize),
        )
        container.addView(
            dumpButton,
            LinearLayout.LayoutParams(buttonSize, buttonSize).apply {
                marginStart = dpToPx(DUMP_TOOL_BUTTON_GAP_DP)
            },
        )

        val params = WindowManager.LayoutParams(
            WindowManager.LayoutParams.WRAP_CONTENT,
            WindowManager.LayoutParams.WRAP_CONTENT,
            WindowManager.LayoutParams.TYPE_ACCESSIBILITY_OVERLAY,
            WindowManager.LayoutParams.FLAG_NOT_FOCUSABLE or
                    WindowManager.LayoutParams.FLAG_NOT_TOUCH_MODAL,
            PixelFormat.TRANSLUCENT,
        ).apply {
            gravity = Gravity.TOP or Gravity.END
            x = dpToPx(DUMP_TOOL_MARGIN_DP)
            y = dpToPx(DUMP_TOOL_TOP_DP)
        }

        fun clampAndUpdate(proposedEndOffset: Int, proposedTopOffset: Int) {
            if (container.width <= 0 || container.height <= 0) return
            val metrics = windowManager.currentWindowMetrics
            val insets = metrics.windowInsets.getInsetsIgnoringVisibility(
                WindowInsets.Type.systemBars() or WindowInsets.Type.displayCutout()
            )
            val edgeMargin = dpToPx(DUMP_TOOL_EDGE_MARGIN_DP)
            val minX = insets.right + edgeMargin
            val maxX = (metrics.bounds.width() - insets.left - container.width - edgeMargin)
                .coerceAtLeast(minX)
            val minY = insets.top + edgeMargin
            val maxY = (metrics.bounds.height() - insets.bottom - container.height - edgeMargin)
                .coerceAtLeast(minY)
            val nextX = proposedEndOffset.coerceIn(minX, maxX)
            val nextY = proposedTopOffset.coerceIn(minY, maxY)
            if (params.x == nextX && params.y == nextY) return
            params.x = nextX
            params.y = nextY
            if (dumpToolView === container && container.isAttachedToWindow) {
                runCatching { windowManager.updateViewLayout(container, params) }
                    .onFailure { Log.w(TAG, "Could not move dump tool", it) }
            }
        }

        val touchSlop = ViewConfiguration.get(this).scaledTouchSlop
        val touchSlopSquared = touchSlop * touchSlop
        var activePointerId = MotionEvent.INVALID_POINTER_ID
        var downRawX = 0f
        var downRawY = 0f
        var startParamX = 0
        var startParamY = 0
        var dragging = false
        val dragTouchListener = View.OnTouchListener { touched, event ->
            when (event.actionMasked) {
                MotionEvent.ACTION_DOWN -> {
                    activePointerId = event.getPointerId(0)
                    downRawX = event.getRawX(0)
                    downRawY = event.getRawY(0)
                    startParamX = params.x
                    startParamY = params.y
                    dragging = false
                    if (touched === closeButton || touched === dumpButton) touched.isPressed = true
                    true
                }
                MotionEvent.ACTION_MOVE -> {
                    val pointerIndex = event.findPointerIndex(activePointerId)
                    if (pointerIndex >= 0) {
                        val deltaX = event.getRawX(pointerIndex) - downRawX
                        val deltaY = event.getRawY(pointerIndex) - downRawY
                        if (!dragging &&
                            deltaX * deltaX + deltaY * deltaY > touchSlopSquared.toFloat()
                        ) {
                            dragging = true
                            touched.isPressed = false
                        }
                        if (dragging) {
                            // TOP|END stores distance from the right edge, so horizontal delta reverses.
                            clampAndUpdate(
                                startParamX - deltaX.roundToInt(),
                                startParamY + deltaY.roundToInt(),
                            )
                        }
                    }
                    true
                }
                MotionEvent.ACTION_UP -> {
                    val wasDragging = dragging
                    touched.isPressed = false
                    activePointerId = MotionEvent.INVALID_POINTER_ID
                    dragging = false
                    if (!wasDragging && (touched === closeButton || touched === dumpButton)) {
                        touched.performClick()
                    }
                    true
                }
                MotionEvent.ACTION_POINTER_UP -> {
                    val pointerIndex = event.actionIndex
                    if (event.getPointerId(pointerIndex) == activePointerId) {
                        touched.isPressed = false
                        activePointerId = MotionEvent.INVALID_POINTER_ID
                        dragging = false
                    }
                    true
                }
                MotionEvent.ACTION_CANCEL -> {
                    touched.isPressed = false
                    activePointerId = MotionEvent.INVALID_POINTER_ID
                    dragging = false
                    true
                }
                else -> true
            }
        }
        container.setOnTouchListener(dragTouchListener)
        closeButton.setOnTouchListener(dragTouchListener)
        dumpButton.setOnTouchListener(dragTouchListener)
        container.addOnLayoutChangeListener { _, _, _, _, _, _, _, _, _ ->
            container.post { clampAndUpdate(params.x, params.y) }
        }

        try {
            windowManager.addView(container, params)
            dumpToolView = container
            container.post { clampAndUpdate(params.x, params.y) }
            AutomationLog.append("Floating dump tool shown (drag to move)")
        } catch (e: Exception) {
            Log.e(TAG, "Could not show dump tool", e)
            dumpToolView = null
            AutomationLog.append("Dump tool failed to open: ${e.message ?: e.javaClass.simpleName}")
        }
    }

    private fun hideDumpTool() {
        val view = dumpToolView ?: return
        dumpToolView = null
        runCatching { windowManager.removeViewImmediate(view) }
            .onFailure { Log.w(TAG, "Could not remove dump tool", it) }
    }

    /** Captures the app beneath the overlay and leaves both that app and the automation untouched. */
    private fun captureManualWindowDump() {
        val foreground = foregroundPackage()
        val target = targetPackageName
        val root = if (runActive && target != null && foreground == target) {
            targetAppRoot()
        } else {
            currentRoots().firstOrNull()
        }
        if (root == null) {
            AutomationLog.append("Manual dump failed: no readable foreground window")
            runCatching {
                Toast.makeText(applicationContext, "No readable window to dump", Toast.LENGTH_SHORT)
                    .show()
            }
            return
        }

        val rootPackage = root.packageName?.toString() ?: "unknown"
        val detailTitle = selectedLikedCardTitle?.takeIf {
            runActive && activeAutomationMode == AutomationMode.UNLIKE_UNFOLLOW &&
                    unlikeUnfollowState != UnlikeUnfollowState.IDLE &&
                    rootPackage == targetPackageName
        }
        val reason = if (detailTitle != null) {
            "Unlike & Unfollow manual detail: $detailTitle"
        } else {
            "Manual floating dump: $rootPackage"
        }
        dumpWindowForDiagnostics(
            root,
            reason,
            force = true,
            maxNodes = MANUAL_DUMP_MAX_NODES,
        )
        AutomationLog.append("Manual dump appended to Logging: $reason")
        runCatching {
            Toast.makeText(applicationContext, "Dump appended to Logging", Toast.LENGTH_SHORT).show()
        }
    }

    private fun resetUnlikeUnfollowManualState() {
        unlikeUnfollowState = UnlikeUnfollowState.IDLE
        selectedLikedCardTitle = null
        attemptedLikedCards.clear()
        unlikeSucceededCount = 0
        unlikeAmbiguousCount = 0
        unlikeUnsupportedCount = 0
        unlikeListScrolls = 0
        unlikeNoMoveScrolls = 0
        unlikeLastVisibleSignature = emptySet()
    }

    private fun dpToPx(value: Int): Int =
        (value * resources.displayMetrics.density).toInt().coerceAtLeast(1)

    // Record a performed action: kept for the per-app summary and mirrored into the live log so the
    // user can watch progress on the Logging screen instead of being interrupted by toasts/dialogs.
    private fun recordAction(message: String) {
        actionLog.add(message)
        logProgress(message)
    }

    /**
     * Logs a line and counts it as progress.
     *
     * Every meaningful thing the run does writes to the log, so "something was logged" is a good proxy
     * for "the run is still moving" — which is what the stall watchdog needs. The one legitimate
     * silence is the deliberate stay inside a task app, and that pushes the deadline out explicitly.
     */
    private fun logProgress(message: String) {
        noteProgress()
        AutomationLog.append(message)
    }

    private fun logProgressSection(title: String) {
        noteProgress()
        AutomationLog.appendSection(title)
    }

    /** Pushes the stall deadline out, optionally by an extra expected wait. */
    private fun noteProgress(extraMs: Long = 0L) {
        watchdogDeadline = SystemClock.uptimeMillis() + STALL_TIMEOUT_MS + extraMs
    }

    private val watchdogTick = object : Runnable {
        override fun run() {
            if (!runActive) return
            if (SystemClock.uptimeMillis() > watchdogDeadline) {
                onRunStalled()
                return
            }
            mainHandler.postDelayed(this, WATCHDOG_TICK_MS)
        }
    }

    private fun startWatchdog() {
        runActive = true
        runStartedAt = SystemClock.uptimeMillis()
        noteProgress()
        mainHandler.removeCallbacks(watchdogTick)
        mainHandler.postDelayed(watchdogTick, WATCHDOG_TICK_MS)
    }

    /**
     * Ends a run that has stopped making progress: close whatever a task opened, then come back and
     * report. Without this a task app that never yields, or a screen the flow cannot read, would leave
     * the run parked in another app indefinitely.
     */
    private fun onRunStalled() {
        if (!runActive) return
        runActive = false
        val where = foregroundPackage()
        logProgress("No progress for ${STALL_TIMEOUT_MS / 1000}s (foreground: $where) — stopping")
        // Stops every callback the flow has queued.
        manualInterruptionDetected = true
        capturingTaskApps = false
        val finishStalledRun: () -> Unit = {
            if (where != null && where != targetPackageName && where != packageName) {
                try { performGlobalAction(GLOBAL_ACTION_HOME) } catch (_: Exception) {}
            }
            mainHandler.postDelayed({
                killTaskApps()
                finishTaskWithResult("Stopped: no progress for ${STALL_TIMEOUT_MS / 1000}s")
            }, KILL_DELAY_MS)
        }
        if (currentTaskTitle != null) {
            failCurrentTaskWithScreenshot(
                "stalled after ${STALL_TIMEOUT_MS / 1000}s",
                finishStalledRun
            )
        } else {
            finishStalledRun()
        }
    }

    private fun resetMiniProgramSession() {
        miniProgramWatchToken++
        activeMiniProgramSpec = null
        miniProgramObservedPackage = null
        miniProgramDumpCaptured = false
        miniProgramWatchFinished = false
        miniProgramCtaTapped = false
        miniProgramPromptObserved = false
        miniProgramPromptFinished = false
    }

    /** Records how the task currently in flight ended and clears any task-specific callback state. */
    private fun markCurrentTaskDone(outcome: String) {
        // No callback from a previous Recents pass may mutate the next task. Keep taskApps until the
        // verified task-page return so a failure path can still close the external app it opened.
        taskAppCleanupToken++
        taskAppCleanupInProgress = false
        capturingTaskApps = false
        val title = currentTaskTitle
        val miniProgramSpec = activeMiniProgramSpec
        if (miniProgramSpec != null) {
            if (!miniProgramWatchFinished) {
                val visiblePackages = currentRoots()
                    .mapNotNull { it.packageName?.toString() }
                    .distinct()
                logProgress(
                    "Mini-program '${miniProgramSpec.id}' watcher ended before its page was handled; " +
                            "event package: ${miniProgramObservedPackage ?: "none"}, readable windows: " +
                            visiblePackages.ifEmpty { listOf("none") }.joinToString(", ")
                )
            }
            resetMiniProgramSession()
        }
        currentTaskTitle = null
        planetFollowState = PlanetFollowState.IDLE
        planetFollowDeadlineMs = 0L
        hotelRankingState = HotelRankingState.IDLE
        hotelRankingDeadlineMs = 0L
        hotelRankingSourceSignature = emptySet()
        hotelRankingMarkerText = null
        hotelRankingNavigationHits = 0
        hotelRankingTapAttempt = 0
        hotelRankingVerificationPolls = 0
        hotelRankingDiagnosticsDumped = false
        dailyCashNoteState = DailyCashNoteState.IDLE
        dailyCashNoteDeadlineMs = 0L
        dailyCashDestinationHits = 0
        dailyCashScrollAnchorTop = null
        dailyCashNavigationSignature = emptySet()
        dailyCashNavigationHits = 0
        dailyCashDwellSeconds = 0
        dailyCashDiagnosticsDumped = false
        dailyCashTaskToken++
        clearExternalHandoffState()
        if (title != null) taskResults.add(title to outcome)
    }

    /** Captures the failure screen before [afterCapture] navigates away from it. */
    private fun failCurrentTaskWithScreenshot(reason: String, afterCapture: () -> Unit) {
        val title = currentTaskTitle
        if (title == null) {
            afterCapture()
            return
        }
        noteProgress(FAILURE_SCREENSHOT_TIMEOUT_MS)
        val entryId = AutomationLog.beginTaskFailure(title, reason)
        markCurrentTaskDone(reason)
        captureFailureScreenshot(entryId, afterCapture)
    }

    private fun captureFailureScreenshot(entryId: Long, continuation: () -> Unit) {
        if (!serviceConnected) {
            AutomationLog.failScreenshot(entryId, "accessibility service is not connected")
            continuation()
            return
        }
        if (screenshotInFlight) {
            AutomationLog.failScreenshot(entryId, "another screenshot is already being captured")
            continuation()
            return
        }

        screenshotInFlight = true
        val completed = AtomicBoolean(false)
        lateinit var timeout: Runnable

        fun finish(bitmap: Bitmap?, error: String?) {
            mainHandler.post {
                if (!completed.compareAndSet(false, true)) {
                    bitmap?.recycle()
                    return@post
                }
                mainHandler.removeCallbacks(timeout)
                screenshotInFlight = false
                if (bitmap != null) {
                    if (!AutomationLog.completeScreenshot(entryId, bitmap)) bitmap.recycle()
                } else {
                    AutomationLog.failScreenshot(entryId, error ?: "capture failed")
                }
                continuation()
            }
        }

        timeout = Runnable {
            if (completed.compareAndSet(false, true)) {
                screenshotInFlight = false
                AutomationLog.failScreenshot(entryId, "capture timed out")
                continuation()
            }
        }
        mainHandler.postDelayed(timeout, FAILURE_SCREENSHOT_TIMEOUT_MS)

        try {
            takeScreenshot(
                Display.DEFAULT_DISPLAY,
                screenshotExecutor,
                object : AccessibilityService.TakeScreenshotCallback {
                    override fun onSuccess(screenshot: AccessibilityService.ScreenshotResult) {
                        val bitmap = runCatching { copyAndScaleScreenshot(screenshot) }.getOrNull()
                        finish(bitmap, if (bitmap == null) "screen buffer could not be copied" else null)
                    }

                    override fun onFailure(errorCode: Int) {
                        finish(null, "Android capture error $errorCode")
                    }
                }
            )
        } catch (error: Throwable) {
            finish(null, error.message ?: error.javaClass.simpleName)
        }
    }

    /** Converts the native screenshot buffer to a bounded software bitmap safe to retain in Compose. */
    private fun copyAndScaleScreenshot(screenshot: AccessibilityService.ScreenshotResult): Bitmap? {
        val buffer = screenshot.hardwareBuffer
        try {
            val hardware = Bitmap.wrapHardwareBuffer(buffer, screenshot.colorSpace) ?: return null
            val software = try {
                hardware.copy(Bitmap.Config.ARGB_8888, false)
            } finally {
                hardware.recycle()
            } ?: return null
            val longest = maxOf(software.width, software.height)
            if (longest <= FAILURE_SCREENSHOT_MAX_EDGE_PX) return software
            val scale = FAILURE_SCREENSHOT_MAX_EDGE_PX.toFloat() / longest
            val scaled = Bitmap.createScaledBitmap(
                software,
                (software.width * scale).toInt().coerceAtLeast(1),
                (software.height * scale).toInt().coerceAtLeast(1),
                true
            )
            if (scaled !== software) software.recycle()
            return scaled
        } finally {
            buffer.close()
        }
    }

    private fun logRunSummary() {
        AutomationLog.appendSection("Summary")
        AutomationLog.append("Run time: ${formatDuration(SystemClock.uptimeMillis() - runStartedAt)}")
        val completed = taskResults.count { it.second == TASK_OUTCOME_DONE }
        AutomationLog.append("Tasks started: $tasksStarted, completed: $completed")
        if (skippedTasks.isNotEmpty()) {
            AutomationLog.append("Already finished, skipped: ${skippedTasks.size}")
        }
        if (ignoredTasks.isNotEmpty()) {
            AutomationLog.append("Not supported, left alone: ${ignoredTasks.size}")
        }
        taskResults.forEach { (title, outcome) -> AutomationLog.append("  • $title — $outcome") }
        if (closedApps.isNotEmpty()) {
            AutomationLog.append("Apps closed: ${closedApps.joinToString(", ")}")
        }
    }

    private fun formatDuration(ms: Long): String {
        val totalSeconds = ms / 1000
        val minutes = totalSeconds / 60
        val seconds = totalSeconds % 60
        return if (minutes > 0) "${minutes}m ${seconds}s" else "${seconds}s"
    }

    /**
     * Brings our own app back to the front on the Logging tab, so the summary is waiting for the user
     * rather than buried behind whatever the run left on screen.
     */
    private fun showLogInApp(completionMessage: String? = null) {
        AutomationLog.requestShowLog()
        try {
            startActivity(
                Intent(this, MainActivity::class.java).apply {
                    action = MainActivity.ACTION_SHOW_AUTOMATION_LOG
                    completionMessage?.let {
                        putExtra(MainActivity.EXTRA_COMPLETION_TOAST, it)
                    }
                    addFlags(
                        Intent.FLAG_ACTIVITY_NEW_TASK or
                                Intent.FLAG_ACTIVITY_CLEAR_TOP or
                                Intent.FLAG_ACTIVITY_SINGLE_TOP
                    )
                }
            )
        } catch (e: Exception) {
            Log.e(TAG, "could not show the log", e)
            completionMessage?.let {
                runCatching {
                    Toast.makeText(applicationContext, it, Toast.LENGTH_LONG).show()
                }
            }
        }
    }

    /**
     * A short pause before a synthetic click, so actions are not chained back-to-back.
     *
     * This used to sleep 1.2–3s before *every* click, which is where most of the run's dead time came
     * from: a step whose target was already on screen still cost seconds. Worse, it blocks the
     * service's main thread, so accessibility events queued up behind it. The spacing between steps is
     * already handled by the scheduled gaps, so all that is needed here is a little jitter.
     */
    private fun jitterBeforeClick(minMs: Long = CLICK_JITTER_MIN_MS, maxMs: Long = CLICK_JITTER_MAX_MS) {
        try {
            SystemClock.sleep(Random.nextLong(from = minMs, until = maxMs))
        } catch (_: Exception) {}
    }

    // Only treat a manual interruption when: the user performed a back gesture (we detect this as
    // a window state change leaving the target package) or when the user pressed volume down.
    private fun checkForManualInterruption(event: AccessibilityEvent?, prevPkg: String?): Boolean {
        if (event == null || !shouldClickElement || manualInterruptionDetected) return false
        // A task is expected to leave Ctrip and may traverse a browser before its real destination.
        // Volume Down / Stop remain available; package changes during this bounded phase are not BACK.
        if (expectingExternalApp && currentTaskTitle != null && runActive) return false
        val pkg = event.packageName?.toString()
        // Detect a likely user 'back' gesture: a window state changed and the previous package was the target,
        // and now the package is different (user navigated away). This heuristic avoids stopping for other clicks.
        if (event.eventType == AccessibilityEvent.TYPE_WINDOW_STATE_CHANGED) {
            if (prevPkg != null && prevPkg == targetPackageName && pkg != null && pkg != targetPackageName) {
                manualInterruptionDetected = true
                shouldClickElement = false
                finishTaskWithResult("Stopped by user BACK gesture (switched to $pkg). Actions: ${actionLog.joinToString(" -> ")}")
                return true
            }
        }
        return false
    }

    override fun onAccessibilityEvent(event: AccessibilityEvent?) {
        event ?: return
        // Buttons in TYPE_ACCESSIBILITY_OVERLAY belong to this package. They are controls, not app
        // navigation, and must never poison foreground tracking or look like a user BACK action.
        if (event.packageName?.toString() == packageName) return
        val reportedText = (
                event.text.map { it.toString() } +
                        listOfNotNull(event.contentDescription?.toString())
                ).joinToString(" ")
        if (runActive && NO_CLAIM_REWARD_TEXTS.any { reportedText.contains(it) }) {
            lastNoClaimRewardAt = SystemClock.uptimeMillis()
        }
        val prevPkg = lastObservedPackage
        // early check for manual interruption and abort current package if detected
        if (checkForManualInterruption(event, prevPkg)) return
        val pkg = event.packageName?.toString()
        // WeChat mini-program transitions can leave Ctrip's readable window ranked first. The active
        // data-driven spec limits event tracking to its expected package instead of accepting any app.
        val miniProgramSpec = activeMiniProgramSpec
        if (miniProgramSpec != null && pkg in miniProgramSpec.expectedPackages) {
            miniProgramObservedPackage = pkg
            val prompt = miniProgramSpec.prompt
            if (miniProgramCtaTapped && !miniProgramPromptFinished && prompt != null) {
                val eventClass = event.className?.toString().orEmpty()
                val promptVisible = prompt.markers.any { reportedText.contains(it) } ||
                        eventClass.contains("Dialog", ignoreCase = true)
                if (promptVisible && !miniProgramPromptObserved) {
                    miniProgramPromptObserved = true
                    logProgress("Observed the '${miniProgramSpec.id}' mini-program prompt")
                }
            }
        }
        // Window changes are infrequent and are the single most useful signal when diagnosing a run,
        // so surface them in the log while a task is active.
        if (targetLabel != null && event.eventType == AccessibilityEvent.TYPE_WINDOW_STATE_CHANGED && pkg != prevPkg) {
            logProgress("Window changed → $pkg")
            // A task can hop through several apps; record each so all of them get closed.
            if (pkg != null) noteTaskApp(pkg)
        }
        if (pkg == targetPackageName && shouldClickElement) {
            when (event.eventType) {
                AccessibilityEvent.TYPE_WINDOW_STATE_CHANGED ->
                    mainHandler.postDelayed({ searchAndClickElement() }, randomDelay(800, 1400))
                AccessibilityEvent.TYPE_WINDOW_CONTENT_CHANGED ->
                    if (clickAttempts < maxClickAttempts) mainHandler.postDelayed({ searchAndClickElement() }, currentDelayMs + randomDelay(100, 400))
            }
        } else {
            if (shouldClickElement && targetLabel != null) {
                // A different window is in front: it may be the app chooser shown for dual apps.
                mainHandler.postDelayed({ handleAppChooserIfPresent() }, 300)
            }
        }
        // update lastObservedPackage for next event
        lastObservedPackage = pkg
    }

    override fun onInterrupt() {}

    override fun onKeyEvent(event: KeyEvent?): Boolean {
        try {
            if (event != null && event.keyCode == KeyEvent.KEYCODE_VOLUME_DOWN && event.action == KeyEvent.ACTION_DOWN) {
                manualInterruptionDetected = true
                shouldClickElement = false
                finishTaskWithResult("Stopped by user pressing Volume Down. Actions: ${actionLog.joinToString(" -> ")}")
                return false
            }
        } catch (_: Exception) {}
        return super.onKeyEvent(event)
    }

    override fun onStartCommand(intent: Intent?, flags: Int, startId: Int): Int {
        intent?.let {
            when (it.action) {
                ACTION_SHOW_DUMP_TOOL -> {
                    dumpToolRequested = true
                    showDumpTool()
                }
                ACTION_HIDE_DUMP_TOOL -> {
                    dumpToolRequested = false
                    hideDumpTool()
                }
                ACTION_START_AUTOMATION -> {
                    val label = it.getStringExtra(EXTRA_TARGET_LABEL) ?: return@let
                    val mode = AutomationMode.fromWireValue(
                        it.getStringExtra(EXTRA_AUTOMATION_MODE)
                    ) ?: run {
                        AutomationLog.append("Failed: unknown automation mode")
                        return@let
                    }
                    if (runActive) {
                        logProgress(
                            "Ignored ${mode.displayName} start: " +
                                    "${activeAutomationMode?.displayName ?: "another automation"} is running"
                        )
                        return@let
                    }
                    startSequentialTasksForLabel(label, mode)
                }
                // Backward-compatible entry for older installed UI builds.
                ACTION_OPEN_LAST_APP -> {
                    val label = it.getStringExtra(EXTRA_TARGET_LABEL) ?: return@let
                    if (!runActive) {
                        startSequentialTasksForLabel(label, AutomationMode.COLLECT_AWARDS)
                    }
                }
                ACTION_STOP_AUTOMATION -> {
                    // Stop button, either in the app or on the notification.
                    if (!runActive) {
                        logProgress("Stop requested, but nothing is running")
                        return@let
                    }
                    manualInterruptionDetected = true
                    shouldClickElement = false
                    capturingTaskApps = false
                    unlikeUnfollowToken++
                    if (activeAutomationMode == AutomationMode.COLLECT_AWARDS) {
                        markCurrentTaskDone("stopped by the user")
                    }
                    finishTaskWithResult("Stopped by the user")
                    return@let
                }
            }
        }
        return super.onStartCommand(intent, flags, startId)
    }

    fun startSequentialTasksForLabel(
        label: String,
        mode: AutomationMode = AutomationMode.COLLECT_AWARDS,
    ) {
        if (runActive) {
            logProgress("Ignored ${mode.displayName} start because an automation is already running")
            return
        }
        // reset state
        targetPackageName = null
        targetLabel = label
        activeAutomationMode = mode
        unlikeUnfollowToken++
        resetUnlikeUnfollowManualState()
        // reset interruption tracking
        manualInterruptionDetected = false
        lastObservedPackage = null
        shouldClickElement = false
        clickAttempts = 0
        currentDelayMs = 500L
        mineFlowStarted = false
        startupRecoveryActive = false
        startupBackPresses = 0
        startupUnknownSignature = emptySet()
        startupUnknownHits = 0
        startupUnreadablePolls = 0
        lastChooserClickAt = 0L
        initialTaskListDumped = false
        actionLog.clear()
        overallResults.clear()
        currentTargetIndex = 0
        taskAppCleanupToken++
        taskAppCleanupInProgress = false
        capturingTaskApps = false
        taskApps.clear()
        externalTaskCandidate = null
        externalTaskCandidateHits = 0
        confirmedExternalTaskApp = null
        clearExternalHandoffState()

        // Announce the run in the append-only log (no toast/notification popup that would cover the
        // screen while the user watches the automation run).
        AutomationLog.setActiveMode(mode)
        AutomationLog.startRun("${mode.displayName} · $label")
        currentTaskTitle = null
        resetMiniProgramSession()
        planetFollowState = PlanetFollowState.IDLE
        planetFollowDeadlineMs = 0L
        hotelRankingState = HotelRankingState.IDLE
        hotelRankingDeadlineMs = 0L
        hotelRankingSourceSignature = emptySet()
        hotelRankingMarkerText = null
        hotelRankingNavigationHits = 0
        hotelRankingTapAttempt = 0
        hotelRankingVerificationPolls = 0
        hotelRankingDiagnosticsDumped = false
        dailyCashNoteState = DailyCashNoteState.IDLE
        dailyCashNoteDeadlineMs = 0L
        dailyCashDestinationHits = 0
        dailyCashScrollAnchorTop = null
        dailyCashNavigationSignature = emptySet()
        dailyCashNavigationHits = 0
        dailyCashDwellSeconds = 0
        dailyCashDiagnosticsDumped = false
        dailyCashTaskToken++
        taskResults.clear()
        skippedTasks.clear()
        ignoredTasks.clear()
        taskLoopPhase = TaskLoopPhase.SCANNING
        postClaimRescanBaseline = 0
        finalClaimPasses = 0
        lastNoClaimRewardAt = 0L
        closedApps.clear()
        startWatchdog()

        // Without an accessibility connection nothing can be read or clicked, so fail loudly here
        // instead of running the whole flow against empty windows.
        val enabledInSettings = isAccessibilityServiceEnabled()
        logProgress(
            "Service connected: $serviceConnected, enabled in settings: $enabledInSettings, " +
                    "readable windows: ${currentRoots().size}"
        )
        if (!serviceConnected) {
            finishTaskWithResult(
                "Failed: the accessibility service is not connected. Open Accessibility Settings, " +
                        "enable \"MyApplication\", then start the task again."
            )
            return
        }

        try {
            showForegroundNotification("${mode.displayName} · $label")
        } catch (_: Exception) {}

        mainHandler.post {
            val pm = packageManager
            // find all packages matching the label and iterate through them
            val pkgs = findPackagesByLabel(pm, label)
            if (pkgs.isEmpty()) {
                Log.w(TAG, "No app found matching label: $label")
                finishTaskWithResult("Failed: no app found matching '$label'")
                return@post
            }
            targetPackages = pkgs
            logProgress("Matched ${pkgs.size} package(s): ${pkgs.joinToString(", ")}")
            currentTargetIndex = 0
            // start with first package; each launch will start its own mine flow
            launchPackageAtIndex(currentTargetIndex)
        }
    }

    // Find all package names whose application label contains the provided label
    private fun findPackagesByLabel(pm: PackageManager, label: String): List<String> {
        val out = mutableListOf<String>()
        val mainIntent = Intent(Intent.ACTION_MAIN).addCategory(Intent.CATEGORY_LAUNCHER)
        val resolveList = pm.queryIntentActivities(mainIntent, PackageManager.ResolveInfoFlags.of(0))
        val t = label.trim()
        for (ri in resolveList) {
            val activityInfo = ri.activityInfo ?: continue
            val appInfo = activityInfo.applicationInfo
            val appLabel = pm.getApplicationLabel(appInfo).toString()
            if (appLabel.contains(t, ignoreCase = true)) out.add(activityInfo.packageName)
        }
        // A cloned ("dual") app resolves to the same package name as the original, and an app can
        // expose several launcher activities, so collapse duplicates to avoid running twice.
        return out.distinct()
    }

    // Launch the package at the given index from targetPackages
    private fun launchPackageAtIndex(index: Int) {
        if (index < 0 || index >= targetPackages.size) return
        val pkg = targetPackages[index]
        val pm = packageManager
        logProgressSection("App ${index + 1}/${targetPackages.size}: $pkg")
        val launch = pm.getLaunchIntentForPackage(pkg)
        if (launch == null) {
            logProgress("No launch intent for $pkg, skipping")
            overallResults.add("$pkg: no launch intent")
            proceedToNextPackage()
            return
        }
        launch.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
        try {
            targetPackageName = pkg
            shouldClickElement = true
            mineFlowStarted = false
            unlikeUnfollowToken++
            resetUnlikeUnfollowManualState()
            startupRecoveryActive = false
            startupBackPresses = 0
            startupUnknownSignature = emptySet()
            startupUnknownHits = 0
            startupUnreadablePolls = 0
            stepClicksIndex = -1
            stepClicks = 0
            taskEntryStepState = TaskEntryStepState.IDLE
            taskEntryStepDeadlineMs = 0L
            lastChooserClickAt = 0L
            chooserDumped = false
            initialTaskListDumped = false
            processedTasks.clear()
            tasksStarted = 0
            taskScrolls = 0
            lastPageSignature = emptySet()
            taskLoopPhase = TaskLoopPhase.SCANNING
            postClaimRescanBaseline = 0
            finalClaimPasses = 0
            expectingExternalApp = false
            capturingTaskApps = false
            planetFollowState = PlanetFollowState.IDLE
            planetFollowDeadlineMs = 0L
            hotelRankingState = HotelRankingState.IDLE
            hotelRankingDeadlineMs = 0L
            hotelRankingSourceSignature = emptySet()
            hotelRankingMarkerText = null
            hotelRankingNavigationHits = 0
            hotelRankingTapAttempt = 0
            hotelRankingVerificationPolls = 0
            hotelRankingDiagnosticsDumped = false
            dailyCashNoteState = DailyCashNoteState.IDLE
            dailyCashNoteDeadlineMs = 0L
            dailyCashDestinationHits = 0
            dailyCashScrollAnchorTop = null
            dailyCashNavigationSignature = emptySet()
            dailyCashNavigationHits = 0
            dailyCashDwellSeconds = 0
            dailyCashDiagnosticsDumped = false
            dailyCashTaskToken++
            taskAppCleanupToken++
            taskAppCleanupInProgress = false
            taskApps.clear()
            externalTaskCandidate = null
            externalTaskCandidateHits = 0
            confirmedExternalTaskApp = null
            clearExternalHandoffState()
            actionLog.clear()
            recordAction("Launching $pkg")
            startActivity(launch)
            // Wait for the app to actually reach the foreground (an app chooser may appear first on
            // devices with dual apps) before running the mine flow.
            mainHandler.postDelayed({ awaitTargetAppForeground() }, randomDelay(800, 1400))
        } catch (e: Exception) {
            Log.e(TAG, "Failed to launch app: $pkg", e)
            logProgress("Failed to launch $pkg: ${e.message}")
            overallResults.add("$pkg: failed to launch: ${e.message}")
            proceedToNextPackage()
        }
    }

    // Move to next package or finish overall
    private fun proceedToNextPackage() {
        currentTargetIndex++
        if (currentTargetIndex < targetPackages.size) {
            logProgress("Moving on to next app")
            mainHandler.postDelayed({ launchPackageAtIndex(currentTargetIndex) }, randomDelay(800, 1400))
        } else {
            // all done - send aggregated result
            val joined = overallResults.joinToString("\n")
            finishTaskWithResult("Overall results:\n$joined")
        }
    }

    /**
     * True when the current window looks like an app-selection dialog rather than the target app.
     *
     * On devices with "dual apps" / app cloning the system shows a picker containing two entries
     * with the *same* label and the *same* package name (the clone runs in a second user profile),
     * so the entries cannot be told apart by package. We only need to recognise the dialog here.
     */
    private fun isAppChooser(root: AccessibilityNodeInfo): Boolean {
        try {
            // Matched in-process for the same reason as findStepTarget: the app-side substring search
            // cannot be relied on to answer partial queries.
            val texts = collectTextNodes(root)
            // A task's "即将离开携程旅行打开…" dialog names the target app next to a 取消 button, which
            // would otherwise satisfy the fallback heuristic below. It is handled by confirmLeaveApp.
            if (texts.any { node -> LEAVE_APP_MARKERS.any { node.text.contains(it) } }) return false
            // An explicit chooser title is a strong signal, so it is checked before anything else:
            // some OEMs attribute the picker window to the target package.
            if (texts.any { node -> CHOOSER_TITLE_KEYS.any { node.text.contains(it, ignoreCase = true) } }) {
                return true
            }
            val rootPkg = root.packageName?.toString()
            val label = targetLabel
            val hasLabel = label != null && texts.any { it.text.contains(label, ignoreCase = true) }
            // A window owned by a known resolver host is a chooser even if the title is localised
            // differently than any string we know about.
            if (rootPkg != null && rootPkg != targetPackageName && CHOOSER_PACKAGES.contains(rootPkg)) {
                if (label == null || hasLabel) return true
            }
            // Beyond that, the target app's own windows are never treated as a chooser.
            if (rootPkg != null && targetPackageName != null && rootPkg == targetPackageName) return false
            // Fallback heuristic: an entry carrying the app label next to a cancel button.
            if (!hasLabel) return false
            val hasCancel = texts.any { node -> CANCEL_KEYS.any { node.text.trim().equals(it, ignoreCase = true) } }
            return hasCancel
        } catch (e: Exception) {
            Log.e(TAG, "isAppChooser failed", e)
            return false
        }
    }

    /**
     * Handles an app-selection dialog if one is on screen by picking the **first** entry.
     *
     * Returns true when a chooser is showing (whether or not this call clicked something), so the
     * caller knows to keep waiting instead of treating the window as the target app.
     */
    private fun handleAppChooserIfPresent(): Boolean {
        if (manualInterruptionDetected) return false
        // Scan every readable window: the picker is often not the "active" window, so checking only
        // rootInActiveWindow misses it entirely.
        val chooserRoot = currentRoots().firstOrNull { isAppChooser(it) } ?: return false
        // The dialog can emit a burst of content-changed events; only act once per cooldown so we
        // don't click a second time after the first choice has already been made.
        val now = SystemClock.uptimeMillis()
        if (now - lastChooserClickAt < CHOOSER_CLICK_COOLDOWN_MS) return true
        lastChooserClickAt = now
        // Record the real structure of the picker once, so a missed selection is diagnosable.
        dumpWindowForDiagnostics(chooserRoot, "app chooser")
        clickFirstChooserEntry(chooserRoot)
        return true
    }

    /**
     * Clicks the first entry of an app chooser, i.e. the top-most row and left-most column, which is
     * the primary (non-cloned) app on every launcher layout we have seen. The cancel button is
     * explicitly excluded so a failed match can never dismiss the dialog.
     */
    private fun clickFirstChooserEntry(root: AccessibilityNodeInfo): Boolean {
        try {
            var candidates = mutableListOf<Pair<AccessibilityNodeInfo, Rect>>()

            // Preferred: nodes carrying the app label (one per clone), mapped to their clickable row.
            targetLabel?.let { label ->
                // Keep the label nodes as well: when both clones live inside one clickable container
                // the container's centre sits between the two icons, so the per-label bounds are the
                // only way to aim at a specific entry.
                val labelNodes = mutableListOf<Pair<AccessibilityNodeInfo, Rect>>()
                val matched = collectTextNodes(root).filter { it.text.contains(label, ignoreCase = true) }
                for ((n, ownBounds) in matched.map { it.node to it.bounds }) {
                    if (!ownBounds.isEmpty()) labelNodes.add(n to ownBounds)
                    val entry = clickableSelfOrAncestor(n) ?: n
                    val r = Rect().also { runCatching { entry.getBoundsInScreen(it) } }
                    if (!r.isEmpty() && !isCancelEntry(entry)) candidates.add(entry to r)
                }
                val distinctEntries = candidates.distinctBy { it.second.toShortString() }.size
                val distinctLabels = labelNodes.distinctBy { it.second.toShortString() }.size
                if (distinctEntries < distinctLabels) {
                    logProgress("Chooser entries share one clickable container, aiming at labels instead")
                    candidates = labelNodes
                }
            }

            // Fallback: any clickable item in the dialog that is not the cancel button.
            if (candidates.isEmpty()) {
                for ((n, r) in collectClickableInWindow(root)) {
                    if (r.isEmpty() || isCancelEntry(n)) continue
                    candidates.add(n to r)
                }
            }

            if (candidates.isEmpty()) {
                logProgress("App chooser detected but no selectable entry found")
                return false
            }

            // Order in reading order: group into rows (tolerating a few px of vertical jitter
            // between side-by-side icons), then left to right within a row.
            var ordered = candidates
                .distinctBy { it.second.toShortString() }
                .sortedWith(compareBy({ it.second.top / CHOOSER_ROW_TOLERANCE_PX }, { it.second.left }))

            // MIUI badges the cloned entry ("双开"/XSpace). When some entries are badged and others
            // are not, the unbadged ones are the original app, which is what we want to open.
            val unbadged = ordered.filterNot { isCloneEntry(it.first) }
            if (unbadged.isNotEmpty() && unbadged.size < ordered.size) {
                logProgress("Ignoring ${ordered.size - unbadged.size} cloned (dual app) entry(ies)")
                ordered = unbadged
            }

            logProgress("App chooser: ${ordered.size} entry(ies), selecting the first one")
            val (first, bounds) = ordered.first()
            if (tryPerformClick(first)) {
                recordAction("Chooser selected first entry ${bounds.toShortString()}")
                return true
            }
            // If the preferred entry refuses the click, try the remaining ones in order.
            for ((node, r) in ordered.drop(1)) {
                if (tryPerformClick(node)) {
                    recordAction("Chooser selected entry ${r.toShortString()} (first entry not clickable)")
                    return true
                }
            }
            logProgress("App chooser: none of the entries could be clicked")
        } catch (e: Exception) {
            Log.e(TAG, "Error handling chooser", e)
        }
        return false
    }

    /** Nearest clickable ancestor (or the node itself), so we click the whole row/cell. */
    private fun clickableSelfOrAncestor(node: AccessibilityNodeInfo, maxDepth: Int = 5): AccessibilityNodeInfo? {
        var current: AccessibilityNodeInfo? = node
        var depth = 0
        while (current != null && depth < maxDepth) {
            if (current.isClickable) return current
            current = try { current.parent } catch (_: Exception) { null }
            depth++
        }
        return null
    }

    /**
     * True when a chooser entry looks like the cloned ("dual app") copy rather than the original.
     * MIUI labels or describes the clone with an XSpace marker; the original has none.
     */
    private fun isCloneEntry(node: AccessibilityNodeInfo): Boolean {
        val texts = collectTexts(node, maxDepth = 3)
        return texts.any { t -> CLONE_MARKER_KEYS.any { t.contains(it, ignoreCase = true) } }
    }

    /** Text and content descriptions of [node] and its descendants down to [maxDepth]. */
    private fun collectTexts(node: AccessibilityNodeInfo, maxDepth: Int): List<String> {
        val out = mutableListOf<String>()
        fun walk(n: AccessibilityNodeInfo, depth: Int) {
            if (depth > maxDepth) return
            try {
                n.text?.toString()?.takeIf { it.isNotBlank() }?.let { out.add(it) }
                n.contentDescription?.toString()?.takeIf { it.isNotBlank() }?.let { out.add(it) }
                n.viewIdResourceName?.takeIf { it.isNotBlank() }?.let { out.add(it) }
                for (i in 0 until n.childCount) n.getChild(i)?.let { walk(it, depth + 1) }
            } catch (_: Exception) {}
        }
        walk(node, 0)
        return out
    }

    /**
     * Captures a bounded immutable window hierarchy as one structured log attachment.
     *
     * The main log keeps only a compact summary/button; individual nodes are rendered on the
     * dedicated dump page. Emitted at most once per package unless [force] is requested.
     */
    private fun dumpWindowForDiagnostics(
        root: AccessibilityNodeInfo,
        reason: String,
        force: Boolean = false,
        maxNodes: Int = MAX_DUMP_NODES,
    ) {
        if (chooserDumped && !force) return
        if (!force) chooserDumped = true

        val rootBounds = Rect().also { runCatching { root.getBoundsInScreen(it) } }
        val nodes = mutableListOf<AutomationLog.DumpNode>()
        val queue = ArrayDeque<Pair<AccessibilityNodeInfo, Int>>()
        queue.add(root to 0)
        while (queue.isNotEmpty() && nodes.size < maxNodes) {
            val (node, depth) = queue.removeFirst()
            try {
                val text = node.text?.toString()?.take(DUMP_FIELD_MAX_CHARS).orEmpty()
                val description = node.contentDescription?.toString()
                    ?.take(DUMP_FIELD_MAX_CHARS)
                    .orEmpty()
                val viewId = node.viewIdResourceName?.take(DUMP_FIELD_MAX_CHARS).orEmpty()
                val bounds = Rect().also { runCatching { node.getBoundsInScreen(it) } }
                if (text.isNotEmpty() || description.isNotEmpty() ||
                    viewId.isNotEmpty() || node.isClickable
                ) {
                    nodes.add(
                        AutomationLog.DumpNode(
                            depth = depth,
                            className = node.className?.toString()?.substringAfterLast('.')
                                ?: "UnknownNode",
                            text = text,
                            contentDescription = description,
                            viewId = viewId,
                            clickable = node.isClickable,
                            bounds = AutomationLog.BoundsSnapshot(
                                bounds.left,
                                bounds.top,
                                bounds.right,
                                bounds.bottom,
                            ),
                        )
                    )
                }
                for (i in 0 until node.childCount) {
                    node.getChild(i)?.let { queue.add(it to depth + 1) }
                }
            } catch (_: Exception) {}
        }

        noteProgress()
        AutomationLog.appendWindowDump(
            AutomationLog.WindowDump(
                reason = reason,
                windowPackage = root.packageName?.toString() ?: "(unknown)",
                rootBounds = AutomationLog.BoundsSnapshot(
                    rootBounds.left,
                    rootBounds.top,
                    rootBounds.right,
                    rootBounds.bottom,
                ),
                nodes = nodes.toList(),
                truncated = queue.isNotEmpty(),
            )
        )
    }

    /** Guards against ever selecting 取消 / Cancel instead of an app entry. */
    private fun isCancelEntry(node: AccessibilityNodeInfo): Boolean {
        val own = listOfNotNull(node.text?.toString(), node.contentDescription?.toString())
        val texts = own.toMutableList()
        // Include direct children so a wrapping button around the cancel label is caught too.
        try {
            for (i in 0 until node.childCount) {
                val c = node.getChild(i) ?: continue
                c.text?.toString()?.let { texts.add(it) }
                c.contentDescription?.toString()?.let { texts.add(it) }
            }
        } catch (_: Exception) {}
        if (texts.isEmpty()) return false
        // Only treat it as cancel when none of its texts mention the app we are launching.
        val label = targetLabel
        if (label != null && texts.any { it.contains(label, ignoreCase = true) }) return false
        return texts.any { t -> CANCEL_KEYS.any { t.trim().equals(it, ignoreCase = true) } }
    }

    /**
     * Waits until [targetPackageName] is actually in the foreground before starting the 我的 flow,
     * resolving any app chooser (dual apps) that appears in between. Without this the flow would run
     * against the chooser window and fail immediately.
     */
    private fun awaitTargetAppForeground(attempt: Int = 1) {
        if (manualInterruptionDetected || mineFlowStarted) return
        val roots = currentRoots()
        // Resolve an app chooser first: it is checked before the foreground test because some OEMs
        // report the picker window under the target package name.
        val chooserShowing = handleAppChooserIfPresent()
        // Accept the target from any readable window, and also honour the package reported by
        // accessibility events, which arrives even when window content is briefly unreadable.
        val visiblePackages = roots.mapNotNull { it.packageName?.toString() }
        val targetVisible = targetPackageName != null &&
                (visiblePackages.contains(targetPackageName) || lastObservedPackage == targetPackageName)
        if (!chooserShowing && targetVisible) {
            logProgress("$targetPackageName is in the foreground")
            startMineFlowOnce()
            return
        }
        if (attempt >= MAX_FOREGROUND_WAIT_ATTEMPTS) {
            val detail = if (roots.isEmpty()) {
                "no readable windows (service connected: $serviceConnected, " +
                        "enabled in settings: ${isAccessibilityServiceEnabled()})"
            } else {
                "visible: ${visiblePackages.distinct().joinToString(", ")}"
            }
            // Whatever is stuck in front is what we need to see to fix this.
            roots.firstOrNull()?.let { dumpWindowForDiagnostics(it, "foreground wait timed out") }
            finishCurrentApp("Failed: $targetPackageName never came to the foreground — $detail")
            return
        }
        if (roots.isEmpty() && attempt == 1) {
            logProgress("No window content readable yet, waiting…")
        }
        val retryDelay = if (chooserShowing) randomDelay(700, 1200) else randomDelay(500, 900)
        mainHandler.postDelayed({ awaitTargetAppForeground(attempt + 1) }, retryDelay)
    }

    /** Single entry point for the selected mode so event- and poll-driven paths cannot both run it. */
    private fun startMineFlowOnce() {
        if (manualInterruptionDetected || mineFlowStarted || !runActive) return
        mineFlowStarted = true
        // The app is up, so launch-time chooser handling is complete. Each mode owns its navigation
        // from here and every delayed callback remains guarded by run/mode state.
        shouldClickElement = false
        when (activeAutomationMode) {
            AutomationMode.COLLECT_AWARDS -> {
                startupRecoveryActive = true
                startupBackPresses = 0
                startupUnknownSignature = emptySet()
                startupUnknownHits = 0
                startupUnreadablePolls = 0
                // Ctrip restores its previous top activity. Classify that activity after it settles
                // rather than assuming every page except 签到任务 is the home page.
                mainHandler.postDelayed({ resumeOrRecoverStartup() }, randomDelay(400, 700))
            }
            AutomationMode.UNLIKE_UNFOLLOW -> {
                startupRecoveryActive = true
                startupBackPresses = 0
                startupUnknownSignature = emptySet()
                startupUnknownHits = 0
                startupUnreadablePolls = 0
                val token = ++unlikeUnfollowToken
                logProgressSection("Unlike & Unfollow: detecting current Ctrip waypoint")
                mainHandler.postDelayed(
                    { resumeOrRecoverUnlikeUnfollow(token) },
                    randomDelay(500, 800)
                )
            }
            null -> finishTaskWithResult("Failed: no automation mode was selected")
        }
    }

    /**
     * Detects the deepest safe Unlike & Unfollow waypoint first. The liked-list destination must win
     * over profile tabs retained in the WebView while the masonry is attaching.
     */
    private fun detectUnlikeUnfollowWaypoint(
        root: AccessibilityNodeInfo,
    ): UnlikeUnfollowWaypoint {
        val texts = collectTextNodes(root)
        if (isLikedCardsMasonryVisible(root, texts) ||
            texts.any { it.text.trim() == "我赞过的" }
        ) {
            return UnlikeUnfollowWaypoint.LIKED_LIST
        }
        val exactLabels = texts.map { it.text.trim() }.toSet()
        if ("主页" in exactLabels && "赞过" in exactLabels) {
            return UnlikeUnfollowWaypoint.PROFILE_HOME
        }
        if (isOnMinePage(texts)) {
            return UnlikeUnfollowWaypoint.MINE_PAGE
        }
        if (findUnlikeUnfollowTarget(root, "我的", bottomBarOnly = true) != null) {
            return UnlikeUnfollowWaypoint.BOTTOM_HOME
        }
        return UnlikeUnfollowWaypoint.UNKNOWN
    }

    /**
     * Resumes Unlike & Unfollow from a recognized page, or backs out of an unknown/deep page only
     * after a non-empty page signature remains stable. Recovery is bounded and reclassifies after
     * every BACK instead of assuming that one particular route is active.
     */
    private fun resumeOrRecoverUnlikeUnfollow(token: Long) {
        if (token != unlikeUnfollowToken || !runActive || manualInterruptionDetected ||
            !startupRecoveryActive || activeAutomationMode != AutomationMode.UNLIKE_UNFOLLOW
        ) return

        val root = targetAppRoot()
        if (foregroundPackage() != targetPackageName || root == null) {
            startupUnreadablePolls++
            if (startupUnreadablePolls >= MAX_STARTUP_UNREADABLE_POLLS) {
                currentRoots().firstOrNull()?.let {
                    dumpWindowForDiagnostics(
                        it,
                        "Unlike & Unfollow startup page remained unreadable",
                        force = true,
                    )
                }
                startupRecoveryActive = false
                finishCurrentApp(
                    "Unlike & Unfollow failed: could not read Ctrip while detecting its current page"
                )
                return
            }
            mainHandler.postDelayed(
                { resumeOrRecoverUnlikeUnfollow(token) },
                randomDelay(STARTUP_RECOVERY_POLL_MIN_MS, STARTUP_RECOVERY_POLL_MAX_MS),
            )
            return
        }

        when (val waypoint = detectUnlikeUnfollowWaypoint(root)) {
            UnlikeUnfollowWaypoint.LIKED_LIST -> {
                startupRecoveryActive = false
                startupUnknownSignature = emptySet()
                startupUnknownHits = 0
                startupUnreadablePolls = 0
                logProgress(
                    "Unlike & Unfollow waypoint: ${waypoint.displayName} after " +
                            "$startupBackPresses BACK press(es); processing cards directly"
                )
                settleAndDumpUnlikeUnfollow(token)
                return
            }
            UnlikeUnfollowWaypoint.PROFILE_HOME -> {
                startupRecoveryActive = false
                startupUnknownSignature = emptySet()
                startupUnknownHits = 0
                startupUnreadablePolls = 0
                logProgress(
                    "Unlike & Unfollow waypoint: ${waypoint.displayName} after " +
                            "$startupBackPresses BACK press(es); resuming at 赞过"
                )
                runUnlikeUnfollowStep(token, stepIndex = 2)
                return
            }
            UnlikeUnfollowWaypoint.MINE_PAGE -> {
                startupRecoveryActive = false
                startupUnknownSignature = emptySet()
                startupUnknownHits = 0
                startupUnreadablePolls = 0
                logProgress(
                    "Unlike & Unfollow waypoint: ${waypoint.displayName} after " +
                            "$startupBackPresses BACK press(es); resuming at 主页"
                )
                runUnlikeUnfollowStep(token, stepIndex = 1)
                return
            }
            UnlikeUnfollowWaypoint.BOTTOM_HOME -> {
                startupRecoveryActive = false
                startupUnknownSignature = emptySet()
                startupUnknownHits = 0
                startupUnreadablePolls = 0
                logProgress(
                    "Unlike & Unfollow waypoint: ${waypoint.displayName} after " +
                            "$startupBackPresses BACK press(es); starting at 我的"
                )
                runUnlikeUnfollowStep(token, stepIndex = 0)
                return
            }
            UnlikeUnfollowWaypoint.UNKNOWN -> Unit
        }

        val signature = pageSignature(root)
        if (signature.isEmpty()) {
            startupUnreadablePolls++
            if (startupUnreadablePolls >= MAX_STARTUP_UNREADABLE_POLLS) {
                dumpWindowForDiagnostics(
                    root,
                    "Unlike & Unfollow startup page had no stable readable signature",
                    force = true,
                )
                startupRecoveryActive = false
                finishCurrentApp(
                    "Unlike & Unfollow failed: current Ctrip page had no readable signature"
                )
                return
            }
            mainHandler.postDelayed(
                { resumeOrRecoverUnlikeUnfollow(token) },
                randomDelay(STARTUP_RECOVERY_POLL_MIN_MS, STARTUP_RECOVERY_POLL_MAX_MS),
            )
            return
        }
        startupUnreadablePolls = 0
        if (signature == startupUnknownSignature) {
            startupUnknownHits++
        } else {
            startupUnknownSignature = signature
            startupUnknownHits = 1
        }
        if (startupUnknownHits < STARTUP_UNKNOWN_CONFIRMATIONS) {
            mainHandler.postDelayed(
                { resumeOrRecoverUnlikeUnfollow(token) },
                randomDelay(STARTUP_RECOVERY_POLL_MIN_MS, STARTUP_RECOVERY_POLL_MAX_MS),
            )
            return
        }

        if (startupBackPresses >= MAX_STARTUP_BACK_PRESSES) {
            dumpWindowForDiagnostics(
                root,
                "Unlike & Unfollow could not find a known startup waypoint",
                force = true,
            )
            startupRecoveryActive = false
            finishCurrentApp(
                "Unlike & Unfollow failed: no known page after " +
                        "$MAX_STARTUP_BACK_PRESSES BACK presses"
            )
            return
        }

        startupBackPresses++
        val pageHint = collectTextNodes(root)
            .sortedBy { it.bounds.top }
            .take(3)
            .joinToString(" / ") { it.text.take(24) }
        logProgress(
            "Unlike & Unfollow recovery: unknown/deep page '$pageHint'; BACK " +
                    "($startupBackPresses/$MAX_STARTUP_BACK_PRESSES)"
        )
        val dispatched = try {
            performGlobalAction(GLOBAL_ACTION_BACK)
        } catch (_: Exception) {
            false
        }
        if (!dispatched) {
            logProgress("Unlike & Unfollow recovery BACK was rejected; page will be rechecked")
        }
        startupUnknownSignature = emptySet()
        startupUnknownHits = 0
        mainHandler.postDelayed(
            { resumeOrRecoverUnlikeUnfollow(token) },
            randomDelay(STARTUP_BACK_SETTLE_MIN_MS, STARTUP_BACK_SETTLE_MAX_MS),
        )
    }

    /**
     * Reach 赞过, then process each safely identified card. Exact labels and the target package are
     * required at every navigation step before card-specific selectors take over.
     */
    private fun runUnlikeUnfollowStep(
        token: Long,
        stepIndex: Int,
        attempt: Int = 1,
    ) {
        if (token != unlikeUnfollowToken || !runActive || manualInterruptionDetected ||
            activeAutomationMode != AutomationMode.UNLIKE_UNFOLLOW
        ) return

        val root = targetAppRoot()?.takeIf { foregroundPackage() == targetPackageName }
        if (root == null) {
            retryUnlikeUnfollowStep(token, stepIndex, attempt, "Ctrip window unreadable")
            return
        }

        // A delayed retry may run after the preceding click has already reached the destination.
        // Never click 赞过 again or navigate away when the liked list is already visible.
        if (detectUnlikeUnfollowWaypoint(root) == UnlikeUnfollowWaypoint.LIKED_LIST) {
            logProgress("Unlike & Unfollow: 我赞过的 is already visible; processing cards directly")
            settleAndDumpUnlikeUnfollow(token)
            return
        }

        val (label, bottomBar) = when (stepIndex) {
            0 -> "我的" to true
            1 -> "主页" to false
            2 -> "赞过" to false
            else -> {
                settleAndDumpUnlikeUnfollow(token)
                return
            }
        }
        val target = findUnlikeUnfollowTarget(root, label, bottomBar)
        if (target != null && performClick(target)) {
            recordAction(
                "Unlike & Unfollow step ${stepIndex + 1}: clicked $label via " +
                        "${target.how} ${target.bounds.toShortString()}"
            )
            mainHandler.postDelayed(
                {
                    if (stepIndex == 2) settleAndDumpUnlikeUnfollow(token)
                    else runUnlikeUnfollowStep(token, stepIndex + 1)
                },
                if (stepIndex == 2) UNLIKE_DUMP_INITIAL_SETTLE_MS
                else randomDelay(UNLIKE_STEP_SETTLE_MIN_MS, UNLIKE_STEP_SETTLE_MAX_MS)
            )
            return
        }

        retryUnlikeUnfollowStep(
            token,
            stepIndex,
            attempt,
            if (target == null) "$label not found" else "$label was not clickable",
        )
    }

    private fun retryUnlikeUnfollowStep(
        token: Long,
        stepIndex: Int,
        attempt: Int,
        reason: String,
    ) {
        if (attempt >= UNLIKE_STEP_MAX_ATTEMPTS) {
            val label = listOf("我的", "主页", "赞过").getOrElse(stepIndex) { "dump" }
            targetAppRoot()?.let {
                dumpWindowForDiagnostics(
                    it,
                    "Unlike & Unfollow failed while finding $label: $reason",
                    force = true,
                )
            }
            finishCurrentApp(
                "Unlike & Unfollow failed at $label: $reason after $attempt tries"
            )
            return
        }
        if (attempt == 1 || attempt % UNLIKE_STATUS_EVERY_ATTEMPTS == 0) {
            logProgress(
                "Unlike & Unfollow step ${stepIndex + 1}: $reason " +
                        "($attempt/$UNLIKE_STEP_MAX_ATTEMPTS)"
            )
        }
        mainHandler.postDelayed(
            { runUnlikeUnfollowStep(token, stepIndex, attempt + 1) },
            randomDelay(UNLIKE_STEP_POLL_MIN_MS, UNLIKE_STEP_POLL_MAX_MS)
        )
    }

    private fun findUnlikeUnfollowTarget(
        root: AccessibilityNodeInfo,
        exactLabel: String,
        bottomBarOnly: Boolean,
    ): ClickTarget? {
        val bottomBarTop = resources.displayMetrics.heightPixels * BOTTOM_BAR_FRACTION
        val matches = collectTextNodes(root)
            .filter { it.text.trim() == exactLabel }
            .filter { !bottomBarOnly || it.bounds.centerY() >= bottomBarTop }
            .distinctBy { it.bounds.toShortString() }
        val chosen = if (bottomBarOnly) {
            matches.maxByOrNull { it.bounds.centerX() }
        } else {
            matches.minByOrNull { it.bounds.top }
        } ?: return null

        val target = clickTargetFor(chosen, "exact text '$exactLabel'")
        val screenWidth = resources.displayMetrics.widthPixels
        val screenHeight = resources.displayMetrics.heightPixels
        // Never click a page-sized ancestor around a short tab label; tap the exact label instead.
        return if (target.bounds.width() > screenWidth * UNLIKE_MAX_TARGET_WIDTH_FRACTION ||
            target.bounds.height() > screenHeight * UNLIKE_MAX_TARGET_HEIGHT_FRACTION
        ) {
            ClickTarget(null, chosen.bounds, "exact '$exactLabel' label (oversized ancestor rejected)")
        } else {
            target
        }
    }

    private data class LikedCardTarget(
        val key: String,
        val title: String,
        val coverBounds: Rect,
    )

    private enum class UnlikeDetailVariant(val label: String) {
        VIDEO("video favorite"),
        ARTICLE("article favorite"),
    }

    private data class UnlikeControl(
        val variant: UnlikeDetailVariant,
        val target: ClickTarget,
        val likeCount: Double?,
        val checkedOrSelected: Boolean,
        val labels: Set<String>,
    )

    private val unlikeTitleMetadataRegex = Regex("^\\d[\\d,.，万wW+]*人?点赞.*$")
    private val unlikeCountRegex = Regex("^([\\d,.，]+(?:\\.\\d+)?)(万|[wW])?$")

    /** Waits for the 赞过 masonry to settle, then opens the next unattempted card. */
    private fun settleAndDumpUnlikeUnfollow(
        token: Long,
        attempt: Int = 1,
        previousSignature: Set<String> = emptySet(),
        stableHits: Int = 0,
    ) {
        if (token != unlikeUnfollowToken || !runActive || manualInterruptionDetected ||
            activeAutomationMode != AutomationMode.UNLIKE_UNFOLLOW
        ) return
        unlikeUnfollowState = UnlikeUnfollowState.SETTLING_LIST
        val root = targetAppRoot()?.takeIf { foregroundPackage() == targetPackageName }
        if (root == null) {
            if (attempt < UNLIKE_DUMP_SETTLE_ATTEMPTS) {
                mainHandler.postDelayed(
                    { settleAndDumpUnlikeUnfollow(token, attempt + 1, previousSignature, stableHits) },
                    UNLIKE_DUMP_POLL_MS
                )
            } else {
                finishCurrentApp("Unlike & Unfollow failed: 赞过 page was unreadable")
            }
            return
        }

        val texts = collectTextNodes(root)
        val sourcePageSignature = pageSignature(root)
        val likesTabVisible = texts.any {
            val value = it.text.trim()
            value == "赞过" || value == "我赞过的"
        }
        // The WebView can update unrelated labels or image asset descriptions while the masonry is
        // already usable. Stabilize on resolved same-card groups, not every text node on the page.
        val targets = if (likesTabVisible) findLikedCardTargets(root) else emptyList()
        val resolverSignature = targets.map {
            "${it.key}@${it.coverBounds.left},${it.coverBounds.top}," +
                    "${it.coverBounds.right},${it.coverBounds.bottom}"
        }.toSet()
        val stabilitySignature = resolverSignature.takeIf { it.isNotEmpty() }
            ?: sourcePageSignature
        val nextStableHits = if (
            stabilitySignature.isNotEmpty() && stabilitySignature == previousSignature
        ) {
            stableHits + 1
        } else {
            0
        }
        if (targets.isNotEmpty() && attempt == 1) {
            logProgress(
                "Resolved ${targets.size} visible liked card group(s); waiting for stable card bounds"
            )
        }
        if (likesTabVisible && nextStableHits >= UNLIKE_DUMP_STABLE_SAMPLES) {
            val target = targets.firstOrNull { it.key !in attemptedLikedCards }
            if (target != null) {
                if (attemptedLikedCards.size >= UNLIKE_MAX_CARDS_PER_RUN) {
                    finishUnlikeUnfollowApp("reached the $UNLIKE_MAX_CARDS_PER_RUN-card safety limit")
                    return
                }
                // A selected card starts a new list generation. Scroll exhaustion from a previous
                // viewport must never make this card's post-Back list look finished immediately.
                unlikeLastVisibleSignature = emptySet()
                unlikeNoMoveScrolls = 0
                attemptedLikedCards.add(target.key)
                selectedLikedCardTitle = target.title
                logProgress(
                    "Selected liked card ${attemptedLikedCards.size}/$UNLIKE_MAX_CARDS_PER_RUN: " +
                            target.title
                )
                unlikeUnfollowState = UnlikeUnfollowState.VERIFYING_DETAIL
                if (!tryClickRect(target.coverBounds)) {
                    unlikeUnsupportedCount++
                    dumpWindowForDiagnostics(
                        root,
                        "Unlike & Unfollow failed to click cover: ${target.title}",
                        force = true,
                    )
                    logProgress("Cover click was rejected for '${target.title}'; skipping it")
                    mainHandler.postDelayed(
                        { settleAndDumpUnlikeUnfollow(token) },
                        UNLIKE_DUMP_POLL_MS,
                    )
                    return
                }
                recordAction("Clicked cover image for '${target.title}'")
                mainHandler.postDelayed(
                    {
                        settleUnlikeUnfollowDetail(
                            token = token,
                            card = target,
                            sourcePageSignature = sourcePageSignature,
                            sourceListSignature = targets.map { it.key }.toSet(),
                        )
                    },
                    UNLIKE_DUMP_INITIAL_SETTLE_MS,
                )
                return
            }

            if (targets.isNotEmpty()) {
                val visibleSignature = targets.map { it.key }.toSet()
                val viewportUnchanged = visibleSignature == unlikeLastVisibleSignature
                if (viewportUnchanged) {
                    unlikeNoMoveScrolls++
                } else {
                    unlikeLastVisibleSignature = visibleSignature
                    unlikeNoMoveScrolls = 0
                }
                if (unlikeNoMoveScrolls >= UNLIKE_NO_MOVE_SCROLL_CONFIRMATIONS) {
                    finishUnlikeUnfollowApp(
                        "all reachable cards were attempted after " +
                                "$unlikeNoMoveScrolls unchanged scroll(s)"
                    )
                    return
                }
                if (unlikeListScrolls >= UNLIKE_MAX_LIST_SCROLLS) {
                    finishCurrentApp(
                        "Unlike & Unfollow stopped after ${attemptedLikedCards.size} card(s): " +
                                "reached the $UNLIKE_MAX_LIST_SCROLLS-scroll safety limit before " +
                                "the current viewport proved exhaustion"
                    )
                    return
                }
                unlikeListScrolls++
                if (swipeVertical(
                        UNLIKE_LIST_SCROLL_FROM_FRACTION,
                        UNLIKE_LIST_SCROLL_TO_FRACTION,
                        UNLIKE_LIST_SCROLL_DURATION_MS,
                    )
                ) {
                    logProgress(
                        "All ${targets.size} visible card(s) were attempted; scrolling for more " +
                                "($unlikeListScrolls/$UNLIKE_MAX_LIST_SCROLLS, " +
                                "unchanged=$unlikeNoMoveScrolls/" +
                                "$UNLIKE_NO_MOVE_SCROLL_CONFIRMATIONS)"
                    )
                    mainHandler.postDelayed(
                        { settleAndDumpUnlikeUnfollow(token) },
                        UNLIKE_LIST_SCROLL_SETTLE_MS,
                    )
                    return
                }
                finishCurrentApp(
                    "Unlike & Unfollow failed: could not scroll after processing " +
                            "${attemptedLikedCards.size} card(s)"
                )
                return
            }
            // A heading can render before the masonry cards. Confirm several samples before treating
            // an empty target set as the true end of the liked list.
            if (attempt >= UNLIKE_EMPTY_LIST_CONFIRM_ATTEMPTS) {
                finishUnlikeUnfollowApp("no liked cards remain")
                return
            }
        }

        if (attempt >= UNLIKE_DUMP_SETTLE_ATTEMPTS) {
            dumpWindowForDiagnostics(
                root,
                "Unlike & Unfollow failed to resolve a card/title/like-count group on 赞过",
                force = true,
            )
            finishUnlikeUnfollowApp("no safe visible card group was found")
            return
        }

        mainHandler.postDelayed(
            {
                settleAndDumpUnlikeUnfollow(
                    token,
                    attempt + 1,
                    stabilitySignature,
                    nextStableHits,
                )
            },
            UNLIKE_DUMP_POLL_MS
        )
    }

    private fun finishUnlikeUnfollowApp(reason: String) {
        finishCurrentApp(
            "Unlike & Unfollow completed: $unlikeSucceededCount confirmed, " +
                    "$unlikeAmbiguousCount unverified, $unlikeUnsupportedCount skipped; $reason"
        )
    }

    /**
     * Resolves cards from the structure Ctrip actually exposes: a clickable masonry card containing
     * an Image, a title and a trailing “xxxx人点赞” label. Starting from the count/title pair also
     * keeps the detector stable when WebView image roles or card heights vary between devices.
     */
    private fun findLikedCardTargets(root: AccessibilityNodeInfo): List<LikedCardTarget> {
        val rootBounds = Rect().also { root.getBoundsInScreen(it) }
        if (rootBounds.isEmpty) return emptyList()
        val width = rootBounds.width().toFloat()
        val height = rootBounds.height().toFloat()
        val masonryTop = listOf("masonry_root", "masonry_product", "choice_column_0")
            .firstNotNullOfOrNull { findBoundsByViewId(root, it)?.top }
            ?: collectTextNodes(root)
                .filter {
                    val value = it.text.trim()
                    value == "赞过" || value == "我赞过的"
                }
                .maxOfOrNull { it.bounds.bottom }
            ?: return emptyList()
        val texts = collectTextNodes(root)
        val imageBounds = mutableListOf<Rect>()
        val cardBounds = mutableListOf<Rect>()
        val queue = ArrayDeque<AccessibilityNodeInfo>()
        queue.add(root)
        while (queue.isNotEmpty()) {
            val node = queue.removeFirst()
            try {
                val bounds = Rect().also { node.getBoundsInScreen(it) }
                val className = node.className?.toString()?.substringAfterLast('.').orEmpty()
                val widthFraction = bounds.width() / width
                val heightFraction = bounds.height() / height
                val intersectsRoot = !bounds.isEmpty && Rect(bounds).intersect(rootBounds)
                if (intersectsRoot && bounds.top >= masonryTop - UNLIKE_COVER_TOP_TOLERANCE_PX) {
                    if ((className == "Image" || className == "ImageView") &&
                        widthFraction in UNLIKE_COVER_MIN_WIDTH_FRACTION..UNLIKE_COVER_MAX_WIDTH_FRACTION &&
                        heightFraction in UNLIKE_COVER_MIN_HEIGHT_FRACTION..UNLIKE_COVER_MAX_HEIGHT_FRACTION
                    ) {
                        imageBounds.add(bounds)
                    }
                    if (node.isClickable &&
                        widthFraction in UNLIKE_COVER_MIN_WIDTH_FRACTION..UNLIKE_CARD_MAX_WIDTH_FRACTION &&
                        heightFraction in UNLIKE_CARD_MIN_HEIGHT_FRACTION..UNLIKE_CARD_MAX_HEIGHT_FRACTION
                    ) {
                        cardBounds.add(bounds)
                    }
                }
                for (i in 0 until node.childCount) node.getChild(i)?.let { queue.add(it) }
            } catch (_: Exception) {}
        }

        val metadataNodes = texts.filter { unlikeTitleMetadataRegex.matches(it.text.trim()) }
        return metadataNodes.mapNotNull { metadata ->
            val titleNode = texts.asSequence()
                .filter { it !== metadata }
                .filter {
                    it.bounds.bottom <= metadata.bounds.top + UNLIKE_TITLE_COUNT_OVERLAP_TOLERANCE_PX &&
                            metadata.bounds.top - it.bounds.bottom <= UNLIKE_TITLE_COUNT_MAX_GAP_PX
                }
                .filter { horizontalOverlapRatio(it.bounds, metadata.bounds) >= UNLIKE_TITLE_MIN_HORIZONTAL_OVERLAP }
                .map { it to normalizeLikedCardTitle(it.text) }
                .filter { (_, value) -> value.length >= UNLIKE_TITLE_MIN_LENGTH }
                .filter { (_, value) -> value !in UNLIKE_LIST_CHROME_TEXTS }
                .filterNot { (_, value) -> unlikeTitleMetadataRegex.matches(value) }
                .maxByOrNull { (node, _) -> node.bounds.bottom }
                ?: return@mapNotNull null
            val title = titleNode.second
            val titleBounds = titleNode.first.bounds
            val cover = imageBounds.asSequence()
                .filter { it.top < titleBounds.top }
                .filter { titleBounds.top - it.bottom <= height * UNLIKE_TITLE_MAX_GAP_FRACTION }
                .filter { horizontalOverlapRatio(it, titleBounds) >= UNLIKE_TITLE_MIN_HORIZONTAL_OVERLAP }
                .maxByOrNull { it.bottom }
                ?.let(::Rect)
                ?: cardBounds.asSequence()
                    .filter { it.contains(titleBounds.centerX(), titleBounds.centerY()) }
                    .filter { it.contains(metadata.bounds.centerX(), metadata.bounds.centerY()) }
                    .minByOrNull { it.width().toLong() * it.height() }
                    ?.let { card ->
                        Rect(
                            card.left,
                            card.top,
                            card.right,
                            (titleBounds.top - UNLIKE_COVER_TITLE_PADDING_PX)
                                .coerceAtLeast(card.top + 1),
                        )
                    }
                ?: return@mapNotNull null
            LikedCardTarget(
                key = title.lowercase(),
                title = title,
                coverBounds = cover,
            )
        }
            .distinctBy { it.key }
            .sortedWith(compareBy<LikedCardTarget> { it.coverBounds.top }.thenBy { it.coverBounds.left })
    }

    private fun horizontalOverlapRatio(first: Rect, second: Rect): Float {
        val overlap = minOf(first.right, second.right) - maxOf(first.left, second.left)
        val smallerWidth = minOf(first.width(), second.width()).coerceAtLeast(1)
        return overlap.coerceAtLeast(0).toFloat() / smallerWidth
    }

    private fun normalizeLikedCardTitle(raw: String): String =
        raw.trim()
            .replace(Regex("\\s+"), " ")
            .trimEnd { it.isWhitespace() || it == '|' || it == '｜' }
            .trim()
            .take(UNLIKE_TITLE_MAX_LENGTH)

    /** Waits for a stable detail variant, resolves its unlike control, and dispatches one tap only. */
    private fun settleUnlikeUnfollowDetail(
        token: Long,
        card: LikedCardTarget,
        sourcePageSignature: Set<String>,
        sourceListSignature: Set<String>,
        attempt: Int = 1,
        previousSignature: Set<String> = emptySet(),
        stableHits: Int = 0,
    ) {
        if (token != unlikeUnfollowToken || !runActive || manualInterruptionDetected ||
            activeAutomationMode != AutomationMode.UNLIKE_UNFOLLOW ||
            unlikeUnfollowState != UnlikeUnfollowState.VERIFYING_DETAIL
        ) return
        val root = targetAppRoot()?.takeIf { foregroundPackage() == targetPackageName }
        if (root == null) {
            if (attempt < UNLIKE_DETAIL_SETTLE_ATTEMPTS) {
                mainHandler.postDelayed(
                    {
                        settleUnlikeUnfollowDetail(
                            token, card, sourcePageSignature, sourceListSignature,
                            attempt + 1, previousSignature, stableHits,
                        )
                    },
                    UNLIKE_DUMP_POLL_MS,
                )
            } else {
                unlikeUnsupportedCount++
                returnFromUnlikeDetail(token, card, sourceListSignature, "detail was unreadable")
            }
            return
        }

        val signature = pageSignature(root)
        val texts = collectTextNodes(root)
        val sourceListVisible = isLikedCardsMasonryVisible(root, texts)
        val candidateDetail = signature.isNotEmpty() && signature != sourcePageSignature &&
                (!sourceListVisible || hasUnlikeDetailBackControl(root))
        val nextStableHits = if (candidateDetail) {
            if (signature == previousSignature) stableHits + 1 else 1
        } else {
            0
        }
        val control = if (candidateDetail) findUnlikeControl(root) else null
        val detailReady = control != null &&
                (nextStableHits >= UNLIKE_DUMP_STABLE_SAMPLES || attempt >= UNLIKE_DETAIL_MIN_POLLS)
        if (detailReady) {
            dispatchUnlikeAction(token, card, sourceListSignature, control)
            return
        }

        if (attempt >= UNLIKE_DETAIL_SETTLE_ATTEMPTS) {
            unlikeUnsupportedCount++
            dumpWindowForDiagnostics(
                root,
                "Unlike control not found for '${card.title}'",
                force = true,
                maxNodes = MANUAL_DUMP_MAX_NODES,
            )
            returnFromUnlikeDetail(
                token,
                card,
                sourceListSignature,
                "no safe video/article unlike control was found",
            )
            return
        }

        mainHandler.postDelayed(
            {
                settleUnlikeUnfollowDetail(
                    token,
                    card,
                    sourcePageSignature,
                    sourceListSignature,
                    attempt + 1,
                    if (candidateDetail) signature else emptySet(),
                    nextStableHits,
                )
            },
            UNLIKE_DUMP_POLL_MS,
        )
    }

    private fun dispatchUnlikeAction(
        token: Long,
        card: LikedCardTarget,
        sourceListSignature: Set<String>,
        control: UnlikeControl,
    ) {
        if (token != unlikeUnfollowToken || unlikeUnfollowState != UnlikeUnfollowState.VERIFYING_DETAIL) return
        // Move state before dispatch: content-change events cannot cause a second toggle.
        unlikeUnfollowState = UnlikeUnfollowState.UNLIKING
        val accepted = performClick(control.target)
        if (!accepted) {
            unlikeUnsupportedCount++
            returnFromUnlikeDetail(
                token, card, sourceListSignature,
                "${control.variant.label} unlike tap was rejected",
            )
            return
        }
        unlikeUnfollowState = UnlikeUnfollowState.VERIFYING_UNLIKE
        recordAction(
            "Clicked ${control.variant.label} unlike for '${card.title}' at " +
                    control.target.bounds.toShortString()
        )
        mainHandler.postDelayed(
            { verifyUnlikeAction(token, card, sourceListSignature, control) },
            UNLIKE_ACTION_SETTLE_MS,
        )
    }

    private fun verifyUnlikeAction(
        token: Long,
        card: LikedCardTarget,
        sourceListSignature: Set<String>,
        before: UnlikeControl,
        attempt: Int = 1,
        missingHits: Int = 0,
    ) {
        if (token != unlikeUnfollowToken || !runActive || manualInterruptionDetected ||
            unlikeUnfollowState != UnlikeUnfollowState.VERIFYING_UNLIKE
        ) return
        val root = targetAppRoot()?.takeIf { foregroundPackage() == targetPackageName }
        val current = root?.let(::findUnlikeControl)?.takeIf { it.variant == before.variant }
        val nextMissingHits = if (current == null) missingHits + 1 else 0
        val countDecreased = before.likeCount != null && current?.likeCount != null &&
                current.likeCount < before.likeCount
        val selectionCleared = before.checkedOrSelected && current != null &&
                !current.checkedOrSelected
        val semanticCleared = current != null &&
                hasLikedSemantic(before.labels) && hasUnlikedSemantic(current.labels)
        val verified = countDecreased || selectionCleared || semanticCleared ||
                nextMissingHits >= UNLIKE_CONTROL_MISSING_STABLE_SAMPLES
        if (verified) {
            unlikeSucceededCount++
            val evidence = when {
                countDecreased -> "like count decreased"
                selectionCleared -> "selected state cleared"
                semanticCleared -> "label changed to unliked"
                else -> "liked control disappeared"
            }
            logProgress("Unlike confirmed for '${card.title}': $evidence")
            returnFromUnlikeDetail(token, card, sourceListSignature, "unlike confirmed")
            return
        }

        if (attempt >= UNLIKE_VERIFY_ATTEMPTS) {
            // The gesture may already have landed. Never retry this control because another tap could
            // re-like the card; list disappearance after Back remains secondary evidence.
            unlikeAmbiguousCount++
            logProgress(
                "Unlike was dispatched once for '${card.title}' but could not be verified; " +
                        "it will not be tapped again"
            )
            returnFromUnlikeDetail(token, card, sourceListSignature, "unlike result unverified")
            return
        }
        mainHandler.postDelayed(
            {
                verifyUnlikeAction(
                    token, card, sourceListSignature, before,
                    attempt + 1, nextMissingHits,
                )
            },
            UNLIKE_DUMP_POLL_MS,
        )
    }

    private fun returnFromUnlikeDetail(
        token: Long,
        card: LikedCardTarget,
        sourceListSignature: Set<String>,
        outcome: String,
    ) {
        if (token != unlikeUnfollowToken || !runActive || manualInterruptionDetected) return
        unlikeUnfollowState = UnlikeUnfollowState.RETURNING
        logProgress("Returning from '${card.title}' ($outcome)")
        // Always use Android's navigation stack here. A geometry-only top-left node can be a
        // forward/overlay control, and an acknowledged local click would otherwise suppress BACK.
        val backAccepted = runCatching {
            performGlobalAction(GLOBAL_ACTION_BACK)
        }.getOrDefault(false)
        if (!backAccepted) {
            logProgress("Android global BACK dispatch was not acknowledged; waiting for the list before failing")
        } else {
            logProgress("Android global BACK dispatched for '${card.title}'")
        }
        unlikeUnfollowState = UnlikeUnfollowState.WAITING_FOR_LIST_REFRESH
        noteProgress(UNLIKE_LIST_RETURN_TIMEOUT_MS)
        mainHandler.postDelayed(
            { waitForLikedListAfterReturn(token, card, sourceListSignature) },
            UNLIKE_RETURN_INITIAL_SETTLE_MS,
        )
    }

    private fun waitForLikedListAfterReturn(
        token: Long,
        card: LikedCardTarget,
        sourceListSignature: Set<String>,
        attempt: Int = 1,
        previousSignature: Set<String>? = null,
        stableHits: Int = 0,
        refreshAttempted: Boolean = false,
    ) {
        if (token != unlikeUnfollowToken || !runActive || manualInterruptionDetected ||
            unlikeUnfollowState != UnlikeUnfollowState.WAITING_FOR_LIST_REFRESH
        ) return
        val root = targetAppRoot()?.takeIf { foregroundPackage() == targetPackageName }
        val listVisible = root != null && isLikedCardsMasonryVisible(root, collectTextNodes(root))
        val signature = root?.takeIf { listVisible }
            ?.let { findLikedCardTargets(it).map { cardTarget -> cardTarget.key }.toSet() }
        val nextStableHits = if (signature != null) {
            if (signature == previousSignature) stableHits + 1 else 1
        } else {
            0
        }
        val signatureStable = signature != null &&
                nextStableHits >= UNLIKE_LIST_REFRESH_STABLE_SAMPLES
        if (signatureStable) {
            val stableSignature = requireNotNull(signature)
            val removed = card.key !in stableSignature
            val unattemptedCount = stableSignature.count { it !in attemptedLikedCards }
            val sourceHadOtherCards = sourceListSignature.any { it != card.key }
            // Never hand a partial/empty WebView back to the normal list loop when the source view
            // proved that other cards existed. That was the main premature-finish path after card 1.
            val credibleNonEmptyList = stableSignature.isNotEmpty() &&
                    (removed || unattemptedCount > 0)
            // Ctrip can keep the processed cards in its masonry after BACK instead of refreshing.
            // This is still a safe list: the normal loop cannot reopen attempted keys and will use
            // its bounded upward swipe to expose later cards.
            val stableAttemptedOnlyList = stableSignature.isNotEmpty() &&
                    unattemptedCount == 0
            val confirmedFinalEmpty = stableSignature.isEmpty() && !sourceHadOtherCards &&
                    nextStableHits >= UNLIKE_LIST_EMPTY_REFRESH_STABLE_SAMPLES
            if (credibleNonEmptyList || stableAttemptedOnlyList || confirmedFinalEmpty) {
                val refreshEvidence = when {
                    confirmedFinalEmpty -> "processed card disappeared; no visible cards remain"
                    unattemptedCount > 0 ->
                        "$unattemptedCount unattempted visible card(s) ready"
                    stableAttemptedOnlyList ->
                        "no new cards appeared; scrolling up for more cards"
                    else -> "processed card disappeared"
                }
                logProgress("赞过 list ready after Back: $refreshEvidence")
                selectedLikedCardTitle = null
                // Scope no-movement detection to this post-Back list generation. A viewport retained
                // from an earlier card must not terminate processing of the next card.
                unlikeLastVisibleSignature = emptySet()
                unlikeNoMoveScrolls = 0
                unlikeUnfollowState = UnlikeUnfollowState.SETTLING_LIST
                mainHandler.postDelayed(
                    { settleAndDumpUnlikeUnfollow(token) },
                    UNLIKE_DUMP_POLL_MS,
                )
                return
            }
        }

        if (attempt >= UNLIKE_LIST_RETURN_ATTEMPTS) {
            // One intentional tab reselect gives a stale/partially attached masonry a chance to
            // repopulate. This is a list refresh only; it never touches a card's thumb-up control.
            val refreshTarget = root?.let {
                findUnlikeUnfollowTarget(it, "赞过", bottomBarOnly = false)
            }
            if (!refreshAttempted && refreshTarget != null && performClick(refreshTarget)) {
                logProgress(
                    "赞过 list did not expose the remaining cards; reselecting 赞过 once to refresh"
                )
                noteProgress(UNLIKE_LIST_RETURN_TIMEOUT_MS)
                mainHandler.postDelayed(
                    {
                        waitForLikedListAfterReturn(
                            token, card, sourceListSignature,
                            attempt = 1,
                            previousSignature = null,
                            stableHits = 0,
                            refreshAttempted = true,
                        )
                    },
                    UNLIKE_RETURN_INITIAL_SETTLE_MS,
                )
                return
            }
            root?.let {
                dumpWindowForDiagnostics(
                    it,
                    "Unlike & Unfollow did not expose a complete stable 赞过 list after card " +
                            "'${card.title}'",
                    force = true,
                )
            }
            finishCurrentApp(
                "Unlike & Unfollow failed after ${attemptedLikedCards.size} card(s): " +
                        "the 赞过 list did not expose its remaining cards"
            )
            return
        }
        mainHandler.postDelayed(
            {
                waitForLikedListAfterReturn(
                    token, card, sourceListSignature, attempt + 1,
                    signature, nextStableHits, refreshAttempted,
                )
            },
            UNLIKE_DUMP_POLL_MS,
        )
    }

    private fun findUnlikeControl(root: AccessibilityNodeInfo): UnlikeControl? {
        val bounds = Rect().also { root.getBoundsInScreen(it) }
        if (bounds.isEmpty) return null
        val width = bounds.width().toFloat()
        val height = bounds.height().toFloat()
        val clickables = collectClickableInWindow(root)
            .filter { (_, candidate) -> !candidate.isEmpty && Rect(candidate).intersect(bounds) }
        fun build(
            variant: UnlikeDetailVariant,
            node: AccessibilityNodeInfo,
            candidate: Rect,
        ): UnlikeControl {
            val labels = collectTexts(node, maxDepth = 3)
                .map { it.trim() }
                .filter { it.isNotEmpty() }
                .toSet()
            return UnlikeControl(
                variant = variant,
                target = ClickTarget(node, candidate, "${variant.label} geometry"),
                likeCount = parseUnlikeCount(labels),
                checkedOrSelected = nodeOrDescendantChecked(node),
                labels = labels,
            )
        }

        val bottomRow = clickables.filter { (_, candidate) ->
            candidate.centerY() >= bounds.top + height * UNLIKE_ARTICLE_MIN_Y_FRACTION &&
                    candidate.width() <= width * UNLIKE_DETAIL_CONTROL_MAX_WIDTH_FRACTION &&
                    candidate.height() <= height * UNLIKE_DETAIL_CONTROL_MAX_HEIGHT_FRACTION
        }
        if (bottomRow.size >= UNLIKE_ARTICLE_MIN_BOTTOM_CONTROLS) {
            bottomRow.asSequence()
                .filter { (_, candidate) ->
                    candidate.centerX() in
                            (bounds.left + width * UNLIKE_ARTICLE_MIN_X_FRACTION).toInt()..
                            (bounds.left + width * UNLIKE_ARTICLE_MAX_X_FRACTION).toInt()
                }
                .map { (node, candidate) ->
                    build(UnlikeDetailVariant.ARTICLE, node, candidate)
                }
                .filter { it.likeCount != null || hasLikedSemantic(it.labels) }
                .minByOrNull {
                    kotlin.math.abs(it.target.bounds.centerX() - (bounds.left + width * 0.52f))
                }
                ?.let { return it }
        }

        return clickables.asSequence()
            .filter { (_, candidate) ->
                candidate.centerX() >= bounds.left + width * UNLIKE_VIDEO_MIN_X_FRACTION &&
                        candidate.centerY() >= bounds.top + height * UNLIKE_VIDEO_MIN_Y_FRACTION &&
                        candidate.centerY() <= bounds.top + height * UNLIKE_VIDEO_MAX_Y_FRACTION &&
                        candidate.width() <= width * UNLIKE_DETAIL_CONTROL_MAX_WIDTH_FRACTION &&
                        candidate.height() <= height * UNLIKE_DETAIL_CONTROL_MAX_HEIGHT_FRACTION
            }
            .map { (node, candidate) -> build(UnlikeDetailVariant.VIDEO, node, candidate) }
            .filter { it.likeCount != null || hasLikedSemantic(it.labels) }
            .minByOrNull { it.target.bounds.top }
    }

    private fun parseUnlikeCount(labels: Set<String>): Double? {
        for (label in labels) {
            val normalized = label.trim().replace(",", "").replace("，", "")
            val match = unlikeCountRegex.matchEntire(normalized) ?: continue
            val value = match.groupValues[1].toDoubleOrNull() ?: continue
            val multiplier = if (match.groupValues[2].isNotEmpty()) 10_000.0 else 1.0
            return value * multiplier
        }
        return null
    }

    private fun nodeOrDescendantChecked(root: AccessibilityNodeInfo): Boolean {
        val queue = ArrayDeque<Pair<AccessibilityNodeInfo, Int>>()
        queue.add(root to 0)
        while (queue.isNotEmpty()) {
            val (node, depth) = queue.removeFirst()
            try {
                if (node.isChecked || node.isSelected) return true
                if (depth < 3) {
                    for (i in 0 until node.childCount) {
                        node.getChild(i)?.let { queue.add(it to depth + 1) }
                    }
                }
            } catch (_: Exception) {}
        }
        return false
    }

    private fun hasLikedSemantic(labels: Set<String>): Boolean = labels.any { label ->
        label.contains("已点赞") || label.contains("取消点赞") || label.contains("赞过")
    }

    private fun hasUnlikedSemantic(labels: Set<String>): Boolean = labels.any { label ->
        val value = label.trim()
        value == "点赞" || value == "赞"
    }

    private fun findUnlikeBackTarget(root: AccessibilityNodeInfo): ClickTarget? {
        val bounds = Rect().also { root.getBoundsInScreen(it) }
        if (bounds.isEmpty) return null
        val width = bounds.width().toFloat()
        val height = bounds.height().toFloat()
        return collectClickableInWindow(root).asSequence()
            .filter { (_, candidate) ->
                !candidate.isEmpty &&
                        candidate.centerX() <= bounds.left + width * UNLIKE_BACK_MAX_X_FRACTION &&
                        candidate.centerY() <= bounds.top + height * UNLIKE_BACK_MAX_Y_FRACTION &&
                        candidate.width() <= width * UNLIKE_BACK_MAX_WIDTH_FRACTION &&
                        candidate.height() <= height * UNLIKE_BACK_MAX_HEIGHT_FRACTION
            }
            .sortedWith(compareBy<Pair<AccessibilityNodeInfo, Rect>> { it.second.top }
                .thenBy { it.second.left })
            .map { (node, candidate) -> ClickTarget(node, candidate, "detail top-left Back") }
            .firstOrNull()
    }

    private fun isLikedCardsMasonryVisible(
        root: AccessibilityNodeInfo,
        texts: List<TextNode>,
    ): Boolean {
        val hasMasonry = listOf("masonry_root", "masonry_product", "choice_column_0")
            .any { findNodeByViewId(root, it) != null }
        val hasLikesHeading = texts.any {
            val value = it.text.trim()
            value == "赞过" || value == "我赞过的"
        }
        return hasMasonry && hasLikesHeading
    }

    private fun hasUnlikeDetailBackControl(root: AccessibilityNodeInfo): Boolean =
        findUnlikeBackTarget(root) != null

    private val UNLIKE_COVER_MIN_WIDTH_FRACTION = 0.35f
    private val UNLIKE_COVER_MAX_WIDTH_FRACTION = 0.55f
    private val UNLIKE_COVER_MIN_HEIGHT_FRACTION = 0.16f
    private val UNLIKE_COVER_MAX_HEIGHT_FRACTION = 0.55f
    private val UNLIKE_CARD_MAX_WIDTH_FRACTION = 0.56f
    private val UNLIKE_CARD_MIN_HEIGHT_FRACTION = 0.20f
    private val UNLIKE_CARD_MAX_HEIGHT_FRACTION = 0.60f
    private val UNLIKE_COVER_TOP_TOLERANCE_PX = 32
    private val UNLIKE_COVER_TITLE_PADDING_PX = 8
    private val UNLIKE_TITLE_COUNT_MAX_GAP_PX = 220
    private val UNLIKE_TITLE_COUNT_OVERLAP_TOLERANCE_PX = 16
    private val UNLIKE_TITLE_MAX_GAP_FRACTION = 0.12f
    private val UNLIKE_TITLE_MIN_HORIZONTAL_OVERLAP = 0.60f
    private val UNLIKE_TITLE_MIN_LENGTH = 2
    private val UNLIKE_TITLE_MAX_LENGTH = 80
    private val UNLIKE_LIST_CHROME_TEXTS = setOf("我的", "主页", "赞过", "我赞过的")
    private val UNLIKE_DETAIL_SETTLE_ATTEMPTS = 16
    private val UNLIKE_DETAIL_MIN_POLLS = 4
    private val UNLIKE_VERIFY_ATTEMPTS = 10
    private val UNLIKE_CONTROL_MISSING_STABLE_SAMPLES = 2
    private val UNLIKE_EMPTY_LIST_CONFIRM_ATTEMPTS = 6
    private val UNLIKE_LIST_RETURN_ATTEMPTS = 24
    private val UNLIKE_LIST_REFRESH_STABLE_SAMPLES = 2
    private val UNLIKE_LIST_EMPTY_REFRESH_STABLE_SAMPLES = 6
    private val UNLIKE_NO_MOVE_SCROLL_CONFIRMATIONS = 2
    private val UNLIKE_MAX_CARDS_PER_RUN = 100
    private val UNLIKE_MAX_LIST_SCROLLS = 30
    private val UNLIKE_LIST_SCROLL_FROM_FRACTION = 0.82f
    private val UNLIKE_LIST_SCROLL_TO_FRACTION = 0.28f
    private val UNLIKE_LIST_SCROLL_DURATION_MS = 650L
    private val UNLIKE_LIST_SCROLL_SETTLE_MS = 900L
    private val UNLIKE_ACTION_SETTLE_MS = 700L
    private val UNLIKE_RETURN_INITIAL_SETTLE_MS = 900L
    private val UNLIKE_LIST_RETURN_TIMEOUT_MS = 12_000L
    private val UNLIKE_VIDEO_MIN_X_FRACTION = 0.84f
    private val UNLIKE_VIDEO_MIN_Y_FRACTION = 0.52f
    private val UNLIKE_VIDEO_MAX_Y_FRACTION = 0.68f
    private val UNLIKE_ARTICLE_MIN_X_FRACTION = 0.43f
    private val UNLIKE_ARTICLE_MAX_X_FRACTION = 0.62f
    private val UNLIKE_ARTICLE_MIN_Y_FRACTION = 0.90f
    private val UNLIKE_ARTICLE_MIN_BOTTOM_CONTROLS = 3
    private val UNLIKE_DETAIL_CONTROL_MAX_WIDTH_FRACTION = 0.28f
    private val UNLIKE_DETAIL_CONTROL_MAX_HEIGHT_FRACTION = 0.14f
    private val UNLIKE_BACK_MAX_X_FRACTION = 0.22f
    private val UNLIKE_BACK_MAX_Y_FRACTION = 0.16f
    private val UNLIKE_BACK_MAX_WIDTH_FRACTION = 0.20f
    private val UNLIKE_BACK_MAX_HEIGHT_FRACTION = 0.14f

    private data class StartupWaypoint(val name: String, val stepIndex: Int)

    /**
     * Detects the deepest safe waypoint first. Returning the corresponding existing flow index lets
     * a restarted schedule continue without repeating earlier navigation steps.
     */
    private fun detectStartupWaypoint(root: AccessibilityNodeInfo): StartupWaypoint? {
        val texts = collectTextNodes(root)
        // Strong task-list evidence wins over stale source-page markers retained by the WebView.
        if (isVerifiedTaskPage(root, texts)) {
            return StartupWaypoint(TASK_PAGE_TITLE, flowSteps.size)
        }
        if (isOnPreTaskEntryPage(root, texts)) {
            return StartupWaypoint("携程会员签到 page", flowSteps.lastIndex)
        }
        if (isOnPointsShell(texts)) {
            return StartupWaypoint("我的积分", 2)
        }
        if (isOnMinePage(texts)) {
            return StartupWaypoint("我的", 1)
        }
        if (findStepTarget(root, flowSteps.first()) != null) {
            return StartupWaypoint("Ctrip home", 0)
        }
        return null
    }

    private fun isOnPreTaskEntryPage(
        root: AccessibilityNodeInfo,
        texts: List<TextNode>,
    ): Boolean =
        findNodeByViewId(root, TASK_ENTRY_SOURCE_PAGE_ID) != null ||
                isOnPreTaskEntryPage(texts)

    private fun isOnPreTaskEntryPage(texts: List<TextNode>): Boolean =
        texts.any { it.text.trim() == TASK_ENTRY_SOURCE_PAGE_TITLE } ||
                texts.any { node -> TASK_ENTRY_PAGE_MARKERS.any { node.text.contains(it) } }

    /** Strong proof of the final 签到任务 list, deliberately excluding 携程会员签到. */
    private fun isVerifiedTaskPage(root: AccessibilityNodeInfo, texts: List<TextNode>): Boolean {
        val taskListRootVisible = findNodeByViewId(root, TASK_LIST_PAGE_ID) != null
        val exactTitleVisible = texts.any { it.text.trim() == TASK_PAGE_TITLE }
        val normalizedTexts = texts.map { cjkOnly(it.text) }
        val visibleTaskTabs = TASK_GROUP_NAMES_CJK.count { name ->
            normalizedTexts.any { it.contains(name) }
        }
        // A transitioned WebView can retain the source page ID/button in its accessibility subtree.
        // Strong destination evidence must win over those stale markers; the source page itself does
        // not expose the task-list ID plus title or at least three distinct task-group names.
        if ((taskListRootVisible && exactTitleVisible) || visibleTaskTabs >= 3) return true
        if (isOnPreTaskEntryPage(root, texts)) return false
        return false
    }

    private fun isOnPointsShell(texts: List<TextNode>): Boolean {
        if (texts.any { it.text.contains(SIGN_IN_CARD_SUBTITLE) }) return true
        val labels = texts.map { cjkOnly(it.text) }.toSet()
        return POINTS_SHELL_LABELS_CJK.count { it in labels } >= 3
    }

    private fun isOnMinePage(texts: List<TextNode>): Boolean {
        val labels = texts.map { cjkOnly(it.text) }.toSet()
        return CJK_POINTS in labels && MINE_COUNTER_LABELS_CJK.count { it in labels } >= 2
    }

    /**
     * Resumes from a known waypoint, or backs out of an unknown/deep page one verified step at a time.
     * This is deliberately separate from returnToTaskPage: startup recovery must not mark a task done.
     */
    private fun resumeOrRecoverStartup() {
        if (manualInterruptionDetected || !runActive || !startupRecoveryActive) return

        val root = targetAppRoot()
        if (foregroundPackage() != targetPackageName || root == null) {
            startupUnreadablePolls++
            if (startupUnreadablePolls >= MAX_STARTUP_UNREADABLE_POLLS) {
                currentRoots().firstOrNull()?.let {
                    dumpWindowForDiagnostics(it, "startup page remained unreadable", force = true)
                }
                startupRecoveryActive = false
                finishCurrentApp("Failed: could not read Ctrip while recovering its previous page")
                return
            }
            mainHandler.postDelayed(
                { resumeOrRecoverStartup() },
                randomDelay(STARTUP_RECOVERY_POLL_MIN_MS, STARTUP_RECOVERY_POLL_MAX_MS)
            )
            return
        }
        startupUnreadablePolls = 0

        val waypoint = detectStartupWaypoint(root)
        if (waypoint != null) {
            startupRecoveryActive = false
            startupUnknownSignature = emptySet()
            startupUnknownHits = 0
            // A new schedule owns a fresh task-entry deadline even if the previous schedule failed
            // while this coordinate step was active.
            taskEntryStepState = TaskEntryStepState.IDLE
            taskEntryStepDeadlineMs = 0L
            stepClicksIndex = -1
            stepClicks = 0
            logProgress(
                "Restart recovery found ${waypoint.name} after $startupBackPresses BACK press(es); " +
                        "resuming at step ${waypoint.stepIndex + 1}/${flowSteps.size + 1}"
            )
            runFlowStep(waypoint.stepIndex)
            return
        }

        val signature = pageSignature(root)
        if (signature.isEmpty()) {
            startupUnreadablePolls++
            mainHandler.postDelayed(
                { resumeOrRecoverStartup() },
                randomDelay(STARTUP_RECOVERY_POLL_MIN_MS, STARTUP_RECOVERY_POLL_MAX_MS)
            )
            return
        }
        if (signature == startupUnknownSignature) {
            startupUnknownHits++
        } else {
            startupUnknownSignature = signature
            startupUnknownHits = 1
        }
        if (startupUnknownHits < STARTUP_UNKNOWN_CONFIRMATIONS) {
            mainHandler.postDelayed(
                { resumeOrRecoverStartup() },
                randomDelay(STARTUP_RECOVERY_POLL_MIN_MS, STARTUP_RECOVERY_POLL_MAX_MS)
            )
            return
        }

        if (startupBackPresses >= MAX_STARTUP_BACK_PRESSES) {
            dumpWindowForDiagnostics(root, "startup could not find a known waypoint", force = true)
            startupRecoveryActive = false
            finishCurrentApp(
                "Failed: could not recover a known navigation page after " +
                        "$MAX_STARTUP_BACK_PRESSES BACK presses"
            )
            return
        }

        startupBackPresses++
        val texts = collectTextNodes(root)
        val pageHint = findHotelRankingMarker(texts)
            ?: texts.sortedBy { it.bounds.top }.take(3).joinToString(" / ") { it.text.take(24) }
        logProgress(
            "Restart recovery: unknown/deep page '$pageHint'; BACK " +
                    "($startupBackPresses/$MAX_STARTUP_BACK_PRESSES)"
        )
        val dispatched = try {
            performGlobalAction(GLOBAL_ACTION_BACK)
        } catch (_: Exception) {
            false
        }
        if (!dispatched) logProgress("Restart recovery BACK was rejected; page will be rechecked")
        startupUnknownSignature = emptySet()
        startupUnknownHits = 0
        mainHandler.postDelayed(
            { resumeOrRecoverStartup() },
            randomDelay(STARTUP_BACK_SETTLE_MIN_MS, STARTUP_BACK_SETTLE_MAX_MS)
        )
    }

    /**
     * Whether the 签到任务 page is on screen: its title, or several group names at once, which only the
     * tab row shows together.
     */
    private fun isOnTaskPage(texts: List<TextNode>): Boolean {
        if (texts.any { it.text.contains(TASK_PAGE_TITLE) }) return true
        return TASK_GROUP_NAMES_CJK.count { name -> texts.any { cjkOnly(it.text) == name } } >= 3
    }

    /** Finds an accessibility node by the final segment of its exposed WebView/Android view ID. */
    private fun findNodeByViewId(root: AccessibilityNodeInfo, id: String): AccessibilityNodeInfo? {
        val queue = ArrayDeque<AccessibilityNodeInfo>()
        queue.add(root)
        while (queue.isNotEmpty()) {
            val node = queue.removeFirst()
            try {
                if (node.viewIdResourceName?.substringAfterLast('/') == id) return node
                for (i in 0 until node.childCount) {
                    node.getChild(i)?.let { queue.add(it) }
                }
            } catch (_: Exception) {}
        }
        return null
    }

    /** Finds a WebView/Android accessibility node's bounds by its exposed view ID. */
    private fun findBoundsByViewId(root: AccessibilityNodeInfo, id: String): Rect? {
        val node = findNodeByViewId(root, id) ?: return null
        return Rect().also { node.getBoundsInScreen(it) }.takeUnless { it.isEmpty() }
    }

    private fun collectClickableInWindow(root: AccessibilityNodeInfo): List<Pair<AccessibilityNodeInfo, Rect>> {
        val out = mutableListOf<Pair<AccessibilityNodeInfo, Rect>>()
        val queue = ArrayDeque<AccessibilityNodeInfo>()
        queue.add(root)
        while (queue.isNotEmpty()) {
            val n = queue.removeFirst()
            try {
                if (n.isClickable) {
                    val r = Rect().also { runCatching { n.getBoundsInScreen(it) } }
                    out.add(Pair(n, r))
                }
                for (i in 0 until n.childCount) {
                    n.getChild(i)?.let { queue.add(it) }
                }
            } catch (_: Exception) {}
        }
        return out
    }

    private fun findFirstPackageByLabel(pm: PackageManager, label: String): String? {
        val mainIntent = Intent(Intent.ACTION_MAIN).addCategory(Intent.CATEGORY_LAUNCHER)
        val resolveList = pm.queryIntentActivities(mainIntent, PackageManager.ResolveInfoFlags.of(0))
        val t = label.trim()
        for (ri in resolveList) {
            val activityInfo = ri.activityInfo ?: continue
            val appInfo = activityInfo.applicationInfo
            val appLabel = pm.getApplicationLabel(appInfo).toString()
            if (appLabel.contains(t, ignoreCase = true)) return activityInfo.packageName
        }
        return null
    }

    private fun searchAndClickElement() {
        if (!shouldClickElement || clickAttempts >= maxClickAttempts) return
        clickAttempts++
        currentDelayMs = (currentDelayMs * 1.1).toLong().coerceAtMost(3000L)

        if (appRoot() == null) { Log.w(TAG, "root null"); return }
        // A chooser may still be in front (dual apps); resolve it and let the polling loop continue.
        if (handleAppChooserIfPresent()) return
        // stop attempting to click the 特价/直播 element
        shouldClickElement = false
        // directly run the 我的 flow
        mainHandler.post { startMineFlowOnce() }
    }

    // ---------------------------------------------------------------------------------------------
    // In-app flow: 我的 → 积分 → 签到·任务 card (bottom-tab fallback) → 做任务赚积分
    // ---------------------------------------------------------------------------------------------

    /** Where on screen a step's target is expected to be. */
    private enum class Region { ANY, BOTTOM_BAR }

    /** Which match to take when a step matches several nodes. */
    private enum class Pick { TOP_MOST, RIGHT_MOST }

    private data class FlowStep(
        val name: String,
        /** Texts to match against text and contentDescription, in priority order. */
        val texts: List<String>,
        val region: Region = Region.ANY,
        /** Require the node's own label to equal the candidate exactly. */
        val exact: Boolean = false,
        val pick: Pick = Pick.TOP_MOST,
        /**
         * Optional replacement for the generic text search, for targets that need to be identified
         * by their surroundings rather than by their own label.
         */
        val finder: ((AccessibilityNodeInfo) -> ClickTarget?)? = null,
        /**
         * Optional check that the click actually got somewhere. When set, the step is clicked again
         * until this holds, instead of being assumed done as soon as a click is dispatched.
         */
        val verify: ((List<TextNode>) -> Boolean)? = null,
    )

    /**
     * What a step will click. [node] is preferred when present, because ACTION_CLICK is more reliable
     * than a synthetic tap; when it is null the tap is dispatched inside [bounds] instead, which is
     * how we hit a cell that has no clickable node of its own.
     */
    private data class ClickTarget(
        val node: AccessibilityNodeInfo?,
        val bounds: Rect,
        val how: String,
    )

    /**
     * The navigation steps, run in order once the app is in the foreground:
     *
     * 1. `我的` — the right-most tab of the home bottom bar. Matched exactly and restricted to the
     *    bottom bar so it cannot land on 我的订单 / 我的钱包 elsewhere on the page.
     * 2. `积分` — the counters row of the profile page (收藏 / 浏览历史 / 积分 / 优惠券). Matched
     *    exactly, because the same page also shows 积分加速, 积分抵￥30 and 携程积多分, all of which a
     *    substring match would reach first.
     * 3. `签到赚积分 / 签到·任务` — first taps the marked upper-left card using a bounded
     *    label/card rectangle. If that dispatch does not open the sign-in page, the verified retry
     *    taps the marked second bottom-bar item instead. Full-page WebView ancestors are never used.
     * 4. `做任务赚积分` — resolved from exposed text when available, otherwise from the confirmed
     *    source page's unique centered wide clickable node. The supplied hierarchy's button bounds
     *    provide the final scaled fallback. Success still requires the real task-tab page.
     */
    private val flowSteps = listOf(
        FlowStep("我的 (bottom tab)", listOf("我的"), Region.BOTTOM_BAR, exact = true, pick = Pick.RIGHT_MOST),
        FlowStep("积分 (counters row)", listOf("积分"), exact = true, finder = { findPointsCounterCell(it) }),
        FlowStep(
            "签到赚积分 card / 签到·任务 bottom tab",
            listOf(SIGN_IN_CARD_SUBTITLE),
            finder = { findSignInTaskEntry(it) },
            // A dispatched tap is not success: try the lower marked tab if the card did not navigate.
            verify = { texts -> isOnPreTaskEntryPage(texts) || isOnTaskPage(texts) },
        ),
        FlowStep(
            TASK_ENTRY_BUTTON_TEXT,
            listOf(TASK_ENTRY_BUTTON_TEXT),
            finder = { findTaskListEntryTarget(it) },
            // A dispatched tap is not success until the real task-tab page is verified.
            verify = { texts -> isOnTaskPage(texts) },
        ),
    )

    private fun isTaskEntryStep(index: Int): Boolean = index == flowSteps.lastIndex

    private fun taskEntryDelay(proposedMs: Long): Long {
        if (taskEntryStepState != TaskEntryStepState.ACTIVE) return proposedMs
        val remaining = (taskEntryStepDeadlineMs - SystemClock.uptimeMillis()).coerceAtLeast(0L)
        return minOf(proposedMs, remaining)
    }

    private fun failTaskEntryStep(reason: String) {
        if (taskEntryStepState == TaskEntryStepState.FAILED ||
            taskEntryStepState == TaskEntryStepState.COMPLETE
        ) return
        taskEntryStepState = TaskEntryStepState.FAILED
        taskEntryStepDeadlineMs = 0L
        val timeoutSeconds = TASK_ENTRY_STEP_TIMEOUT_MS / 1000
        val message = "未能在${timeoutSeconds}秒内打开“签到任务”，请手动点击“$TASK_ENTRY_BUTTON_TEXT”后重试"
        Toast.makeText(applicationContext, message, Toast.LENGTH_LONG).show()
        targetAppRoot()?.let {
            dumpWindowForDiagnostics(it, "$TASK_ENTRY_BUTTON_TEXT entry failed: $reason", force = true)
        }
        finishCurrentApp(
            "Failed at step ${flowSteps.size} ($TASK_ENTRY_BUTTON_TEXT): $reason. " +
                    "Actions: ${actionLog.joinToString(" -> ")}"
        )
    }

    /**
     * Runs [flowSteps] one at a time. The last step owns one wall-clock deadline covering target
     * resolution, every coordinate click, all settle waits and all destination-verification polls.
     */
    private fun runFlowStep(index: Int, attempt: Int = 1) {
        if (manualInterruptionDetected || !runActive) return
        if (index >= flowSteps.size) {
            if (!initialTaskListDumped) {
                val taskRoot = targetAppRoot()
                    ?.takeIf { foregroundPackage() == targetPackageName }
                if (taskRoot == null) {
                    if (attempt < STEP_RETRY_ATTEMPTS) {
                        mainHandler.postDelayed(
                            { runFlowStep(index, attempt + 1) },
                            randomDelay(STEP_RETRY_MIN_MS, STEP_RETRY_MAX_MS),
                        )
                        return
                    }
                    logProgress(
                        "Could not capture the initial $TASK_PAGE_TITLE node dump after " +
                                "$attempt readability checks; continuing"
                    )
                } else {
                    initialTaskListDumped = true
                    dumpWindowForDiagnostics(
                        taskRoot,
                        "initial verified $TASK_PAGE_TITLE task list",
                        force = true,
                        maxNodes = TASK_LIST_DUMP_MAX_NODES,
                    )
                }
            }
            logProgress("On $TASK_PAGE_TITLE; returning to the top before collecting pending awards")
            taskScrolls = 0
            lastPageSignature = emptySet()
            scrollToPageTop {
                if (!manualInterruptionDetected && runActive &&
                    taskLoopPhase == TaskLoopPhase.SCANNING
                ) {
                    // Start the bounded claim budget only after top normalization. A restored task
                    // page can be many screens down, and scrolling must not consume the claim window.
                    val claimStartedAt = SystemClock.uptimeMillis()
                    logProgress("At the top of $TASK_PAGE_TITLE; collecting anything already waiting")
                    mainHandler.postDelayed(
                        { collectPendingAwards(startedAtMs = claimStartedAt) },
                        randomDelay(CLAIM_FIRST_LOOK_MIN_MS, CLAIM_FIRST_LOOK_MAX_MS)
                    )
                }
            }
            return
        }

        val taskEntryStep = isTaskEntryStep(index)
        if (taskEntryStep) {
            when (taskEntryStepState) {
                TaskEntryStepState.COMPLETE, TaskEntryStepState.FAILED -> return
                TaskEntryStepState.IDLE -> {
                    taskEntryStepState = TaskEntryStepState.ACTIVE
                    taskEntryStepDeadlineMs = SystemClock.uptimeMillis() + TASK_ENTRY_STEP_TIMEOUT_MS
                    stepClicksIndex = index
                    stepClicks = 0
                    logProgress(
                        "Step ${index + 1}/${flowSteps.size}: find and click $TASK_ENTRY_BUTTON_TEXT " +
                                "(${TASK_ENTRY_STEP_TIMEOUT_MS / 1000}s limit)"
                    )
                }
                TaskEntryStepState.ACTIVE -> Unit
            }
            if (SystemClock.uptimeMillis() >= taskEntryStepDeadlineMs) {
                failTaskEntryStep(
                "${TASK_ENTRY_STEP_TIMEOUT_MS / 1000}-second deadline reached before the page appeared"
            )
                return
            }
        }

        val step = flowSteps[index]
        if (attempt == 1 && !taskEntryStep) {
            logProgress("Step ${index + 1}/${flowSteps.size}: looking for ${step.name}")
        }

        val root = if (taskEntryStep) {
            targetAppRoot()?.takeIf { foregroundPackage() == targetPackageName }
        } else {
            appRoot()
        }
        if (root == null) {
            retryStepOrFail(index, attempt, "no readable window")
            return
        }

        // The destination can become accessible between the final verification sample and this retry.
        // Recognise it before resolving/clicking the retained source button again.
        if (taskEntryStep) {
            val currentTexts = collectTextNodes(root)
            if (isVerifiedTaskPage(root, currentTexts)) {
                taskEntryStepState = TaskEntryStepState.COMPLETE
                taskEntryStepDeadlineMs = 0L
                logProgress("Step ${index + 1} took effect before retrying the click")
                runFlowStep(index + 1)
                return
            }
        }

        if (index != stepClicksIndex) {
            stepClicksIndex = index
            stepClicks = 0
        }
        val target = step.finder?.invoke(root) ?: findStepTarget(root, step)
        if (target != null) {
            stepClicks++
            if (performClick(target)) {
                recordAction(
                    "Step ${index + 1}: clicked ${step.name} via ${target.how} ${target.bounds.toShortString()}"
                )
                val settle = randomDelay(STEP_SETTLE_MIN_MS, STEP_SETTLE_MAX_MS)
                if (step.verify == null) {
                    mainHandler.postDelayed({ runFlowStep(index + 1) }, settle)
                } else {
                    val delay = if (taskEntryStep) taskEntryDelay(settle) else settle
                    mainHandler.postDelayed({ verifyStepTookEffect(index) }, delay)
                }
                return
            }
        }

        // A banner or modal may be covering the target (the 积分 page opens with a rules notice), so
        // try once to dismiss it before burning the remaining attempts.
        if (target == null && attempt == DISMISS_POPUP_ON_ATTEMPT_FAST && findAndClickCloseButton()) {
            logProgress("Dismissed a popup, retrying ${step.name}")
        }
        retryStepOrFail(index, attempt, if (target == null) "not found" else "not clickable")
    }

    /**
     * Confirms a step got somewhere, and clicks it again if it did not.
     *
     * `performClick` only reports that a tap was *dispatched*. A tap can land on exactly the right node
     * and still do nothing — the page may still be binding, or the label may not yet be wired to its
     * handler. Treating a dispatched tap as success is how a run sailed past 立即赚更多 and then worked
     * the wrong page, so a step with a verifier is not finished until its result is on screen.
     */
    private fun verifyStepTookEffect(index: Int, poll: Int = 1) {
        if (manualInterruptionDetected) return
        val taskEntryStep = isTaskEntryStep(index)
        if (taskEntryStep && taskEntryStepState != TaskEntryStepState.ACTIVE) return

        val step = flowSteps[index]
        val verify = step.verify ?: run { runFlowStep(index + 1); return }
        val root = if (taskEntryStep) {
            targetAppRoot()?.takeIf { foregroundPackage() == targetPackageName }
        } else {
            appRoot()
        }
        val texts = root?.let { collectTextNodes(it) }
        val verified = if (taskEntryStep) {
            root != null && texts != null && isVerifiedTaskPage(root, texts)
        } else {
            texts != null && verify(texts)
        }
        if (verified) {
            if (taskEntryStep) {
                taskEntryStepState = TaskEntryStepState.COMPLETE
                taskEntryStepDeadlineMs = 0L
            }
            logProgress("Step ${index + 1} took effect")
            runFlowStep(index + 1)
            return
        }

        if (taskEntryStep && SystemClock.uptimeMillis() >= taskEntryStepDeadlineMs) {
            failTaskEntryStep(
                "${TASK_ENTRY_STEP_TIMEOUT_MS / 1000}-second deadline reached while verifying $TASK_PAGE_TITLE"
            )
            return
        }

        val maxPolls = if (taskEntryStep) TASK_ENTRY_VERIFY_POLLS else STEP_VERIFY_POLLS
        if (poll < maxPolls) {
            val proposedDelay = randomDelay(STEP_RETRY_MIN_MS, STEP_RETRY_MAX_MS)
            val delay = if (taskEntryStep) taskEntryDelay(proposedDelay) else proposedDelay
            mainHandler.postDelayed({ verifyStepTookEffect(index, poll + 1) }, delay)
            return
        }

        val maxClicks = if (taskEntryStep) TASK_ENTRY_MAX_CLICKS else STEP_MAX_CLICKS
        if (stepClicks < maxClicks) {
            logProgress(
                "Step ${index + 1} (${step.name}) did not open the next page after " +
                        "$stepClicks click(s), trying again"
            )
            runFlowStep(index)
            return
        }

        if (taskEntryStep) {
            failTaskEntryStep("$stepClicks $TASK_ENTRY_BUTTON_TEXT click(s) did not open $TASK_PAGE_TITLE")
            return
        }
        appRoot()?.let { dumpWindowForDiagnostics(it, "step ${index + 1} ${step.name} had no effect") }
        finishCurrentApp(
            "Failed at step ${index + 1} (${step.name}): clicked $stepClicks time(s) but the next page " +
                    "never appeared. Actions: ${actionLog.joinToString(" -> ")}"
        )
    }

    private fun retryStepOrFail(index: Int, attempt: Int, reason: String) {
        val step = flowSteps[index]
        val taskEntryStep = isTaskEntryStep(index)
        if (taskEntryStep && SystemClock.uptimeMillis() >= taskEntryStepDeadlineMs) {
            failTaskEntryStep(
                "${TASK_ENTRY_STEP_TIMEOUT_MS / 1000}-second deadline reached: $reason"
            )
            return
        }
        if (attempt >= STEP_RETRY_ATTEMPTS) {
            if (taskEntryStep) {
                failTaskEntryStep("$reason after $attempt $TASK_ENTRY_BUTTON_TEXT attempts")
                return
            }
            // Dump what is actually on screen: that is what explains a missed step.
            appRoot()?.let { dumpWindowForDiagnostics(it, "step ${index + 1} ${step.name}: $reason") }
            finishCurrentApp(
                "Failed at step ${index + 1} (${step.name}): $reason after $attempt tries. " +
                        "Actions: ${actionLog.joinToString(" -> ")}"
            )
            return
        }
        logProgress("${step.name}: $reason, retry $attempt/$STEP_RETRY_ATTEMPTS")
        val proposedDelay = randomDelay(STEP_RETRY_MIN_MS, STEP_RETRY_MAX_MS)
        val delay = if (taskEntryStep) taskEntryDelay(proposedDelay) else proposedDelay
        mainHandler.postDelayed({ runFlowStep(index, attempt + 1) }, delay)
    }

    /**
     * Resolves 做任务赚积分 on the confirmed 携程会员签到 source page.
     *
     * Some WebView builds expose the label, while the supplied hierarchy exposes only a centered,
     * wide clickable TextView at [264,1196][816,1344] on a 1080×2400 root. Prefer ACTION_CLICK on
     * either form; use that measured rectangle only when the button node itself is hidden.
     */
    private fun findTaskListEntryTarget(root: AccessibilityNodeInfo): ClickTarget? {
        val texts = collectTextNodes(root)
        texts.firstOrNull { it.text.contains(TASK_ENTRY_BUTTON_TEXT) }?.let { textNode ->
            return clickTargetFor(textNode, "visible $TASK_ENTRY_BUTTON_TEXT")
        }
        if (!isOnPreTaskEntryPage(root, texts)) return null

        val rootBounds = Rect().also { root.getBoundsInScreen(it) }
        if (rootBounds.isEmpty()) return null
        val rootWidth = rootBounds.width().toFloat()
        val rootHeight = rootBounds.height().toFloat()
        val expectedX = rootBounds.left + rootWidth * TASK_ENTRY_EXPECTED_CENTER_X_FRACTION
        val expectedY = rootBounds.top + rootHeight * TASK_ENTRY_EXPECTED_CENTER_Y_FRACTION
        val buttonNode = collectClickableInWindow(root)
            .filter { (_, bounds) -> !bounds.isEmpty() }
            .filter { (_, bounds) ->
                val widthFraction = bounds.width() / rootWidth
                val heightFraction = bounds.height() / rootHeight
                val centerXFraction = (bounds.centerX() - rootBounds.left) / rootWidth
                val centerYFraction = (bounds.centerY() - rootBounds.top) / rootHeight
                widthFraction in TASK_ENTRY_MIN_WIDTH_FRACTION..TASK_ENTRY_MAX_WIDTH_FRACTION &&
                        heightFraction in TASK_ENTRY_MIN_HEIGHT_FRACTION..TASK_ENTRY_MAX_HEIGHT_FRACTION &&
                        centerXFraction in TASK_ENTRY_MIN_CENTER_X_FRACTION..TASK_ENTRY_MAX_CENTER_X_FRACTION &&
                        centerYFraction in TASK_ENTRY_MIN_CENTER_Y_FRACTION..TASK_ENTRY_MAX_CENTER_Y_FRACTION
            }
            .minByOrNull { (_, bounds) ->
                abs(bounds.centerX() - expectedX) + abs(bounds.centerY() - expectedY)
            }
        if (buttonNode != null) {
            return ClickTarget(
                node = buttonNode.first,
                bounds = buttonNode.second,
                how = "confirmed source-page wide button"
            )
        }

        val bounds = Rect(
            rootBounds.left + (rootWidth * TASK_ENTRY_LEFT_FRACTION).toInt(),
            rootBounds.top + (rootHeight * TASK_ENTRY_TOP_FRACTION).toInt(),
            rootBounds.left + (rootWidth * TASK_ENTRY_RIGHT_FRACTION).toInt(),
            rootBounds.top + (rootHeight * TASK_ENTRY_BOTTOM_FRACTION).toInt()
        )
        return ClickTarget(null, bounds, "dump-calibrated $TASK_ENTRY_BUTTON_TEXT rectangle")
    }

    /** Clicks a resolved [ClickTarget], falling back to a tap inside its bounds. */
    private fun performClick(target: ClickTarget): Boolean =
        if (target.node != null) tryPerformClick(target.node) else tryClickRect(target.bounds)

    /**
     * Opens 签到任务 from 我的积分 using the two marked areas in order.
     *
     * The card subtitle is sometimes exposed only through one full-page WebView label. Promoting that
     * label to its clickable ancestor produced a false `[0,0][screen]` click, so the first attempt
     * accepts only a genuinely bounded label and otherwise taps the screenshot-calibrated card. If
     * verification says that click did not navigate, [stepClicks] makes the next attempt use the
     * second bottom-bar tab instead.
     */
    private fun findSignInTaskEntry(root: AccessibilityNodeInfo): ClickTarget? =
        if (stepClicks == 0) findUpperSignInTaskCard(root) else findBottomSignInTaskTab(root)

    private fun findUpperSignInTaskCard(root: AccessibilityNodeInfo): ClickTarget? {
        val rootBounds = Rect().also { root.getBoundsInScreen(it) }
        if (rootBounds.isEmpty()) return null
        val rootWidth = rootBounds.width().toFloat()
        val rootHeight = rootBounds.height().toFloat()
        val texts = collectTextNodes(root)
        if (!isOnPointsShell(texts)) return null

        val boundedLabel = texts
            .filter { it.text.contains(SIGN_IN_CARD_SUBTITLE) }
            .filter { label ->
                label.bounds.width() <= rootWidth * SIGN_IN_CARD_MAX_LABEL_WIDTH_FRACTION &&
                        label.bounds.height() <= rootHeight * SIGN_IN_CARD_MAX_LABEL_HEIGHT_FRACTION &&
                        label.bounds.centerX() <= rootBounds.left +
                        rootWidth * SIGN_IN_CARD_MAX_CENTER_X_FRACTION &&
                        label.bounds.centerY() in
                        (rootBounds.top + rootHeight * SIGN_IN_CARD_MIN_CENTER_Y_FRACTION).toInt()..
                        (rootBounds.top + rootHeight * SIGN_IN_CARD_MAX_CENTER_Y_FRACTION).toInt()
            }
            .minByOrNull { it.bounds.top }
        if (boundedLabel != null) {
            return ClickTarget(null, boundedLabel.bounds, "$SIGN_IN_CARD_SUBTITLE bounded label")
        }

        val bounds = Rect(
            rootBounds.left + (rootWidth * SIGN_IN_CARD_LEFT_FRACTION).toInt(),
            rootBounds.top + (rootHeight * SIGN_IN_CARD_TOP_FRACTION).toInt(),
            rootBounds.left + (rootWidth * SIGN_IN_CARD_RIGHT_FRACTION).toInt(),
            rootBounds.top + (rootHeight * SIGN_IN_CARD_BOTTOM_FRACTION).toInt(),
        )
        return ClickTarget(null, bounds, "$SIGN_IN_CARD_SUBTITLE calibrated card")
    }

    private fun findBottomSignInTaskTab(root: AccessibilityNodeInfo): ClickTarget? {
        val texts = collectTextNodes(root)
        if (!isOnPointsShell(texts)) return null
        secondBottomBarItem(root)?.let { return it }

        val rootBounds = Rect().also { root.getBoundsInScreen(it) }
        if (rootBounds.isEmpty()) return null
        val rootWidth = rootBounds.width().toFloat()
        val rootHeight = rootBounds.height().toFloat()
        val bounds = Rect(
            rootBounds.left + (rootWidth * SIGN_IN_TAB_LEFT_FRACTION).toInt(),
            rootBounds.top + (rootHeight * SIGN_IN_TAB_TOP_FRACTION).toInt(),
            rootBounds.left + (rootWidth * SIGN_IN_TAB_RIGHT_FRACTION).toInt(),
            rootBounds.top + (rootHeight * SIGN_IN_TAB_BOTTOM_FRACTION).toInt(),
        )
        return ClickTarget(null, bounds, "calibrated bottom bar tab 2")
    }

    /** Everything except CJK characters removed, so separators and spacing stop mattering. */
    private fun cjkOnly(text: String): String = text.filter { it.code in 0x4E00..0x9FFF }

    /** Prefers a clickable ancestor of a label, falling back to tapping the label itself. */
    private fun clickTargetFor(node: TextNode, how: String): ClickTarget {
        clickableSelfOrAncestor(node.node, maxDepth = 5)?.let { clickable ->
            val b = Rect().also { runCatching { clickable.getBoundsInScreen(it) } }
            if (!b.isEmpty()) return ClickTarget(clickable, b, how)
        }
        return ClickTarget(null, node.bounds, "$how (tap)")
    }

    /**
     * The second tab of the bottom bar, located purely by position: 会员中心 / 签到·任务 / 我的积分 /
     * 会员商城 / 积多分, left to right.
     */
    private fun secondBottomBarItem(root: AccessibilityNodeInfo): ClickTarget? {
        val screenWidth = resources.displayMetrics.widthPixels
        val bottomBarTop = resources.displayMetrics.heightPixels * BOTTOM_BAR_FRACTION
        val maxTabWidth = screenWidth * MAX_BOTTOM_TAB_WIDTH_FRACTION

        // Individual tabs, not the bar that contains them.
        var candidates = collectClickableInWindow(root)
            .filter { it.second.centerY() >= bottomBarTop && !it.second.isEmpty() }
            .filter { it.second.width() <= maxTabWidth }
            .map { it.first to it.second }

        if (candidates.size < 2) {
            // No clickable tabs exposed: fall back to whatever labels sit in the bar.
            candidates = collectTextNodes(root)
                .filter { it.bounds.centerY() >= bottomBarTop && it.bounds.width() <= maxTabWidth }
                .map { it.node to it.bounds }
        }

        val distinct = candidates.distinctBy { it.second.toShortString() }
        // The bottom region can hold more than one row (a floating button, a banner). Keep only the
        // lowest row, which is the bar itself, before ordering left to right.
        val lowestRow = distinct.maxByOrNull { it.second.centerY() } ?: run {
            logProgress("Bottom bar is empty, cannot pick the second item")
            return null
        }
        val ordered = distinct
            .filter { abs(it.second.centerY() - lowestRow.second.centerY()) <= TAB_ROW_TOLERANCE_PX }
            .sortedBy { it.second.centerX() }
        if (ordered.size < 2) {
            logProgress("Bottom bar has ${ordered.size} item(s), cannot pick the second one")
            return null
        }
        val (node, bounds) = ordered[1]
        logProgress("Using the second bottom-bar item at ${bounds.toShortString()}")
        return ClickTarget(node, bounds, "bottom bar tab 2")
    }

    /**
     * Collects whatever is already waiting via 一键领, then starts on the tasks.
     *
     * The summary card holding that button renders *after* the task list, so a quick look finds nothing
     * and the step gets skipped. Startup first normalizes the restored list to its top, then deliberately
     * waits before the first look and polls patiently. This keeps an off-screen 一键领 from being missed
     * when Ctrip restores 签到任务 at a previous middle-of-list scroll position.
     */
    private fun claimStopReason(startedAtMs: Long): String? {
        if (lastNoClaimRewardAt >= startedAtMs) return "page reported 暂无可领取奖励"
        if (SystemClock.uptimeMillis() - startedAtMs >= CLAIM_ATTEMPT_TIMEOUT_MS) {
            return "reached the five-second claim limit"
        }
        return null
    }

    /** Caps every scheduled retry so the callback runs no later than the claim deadline. */
    private fun claimDelay(startedAtMs: Long, minMs: Int, maxMs: Int): Long {
        val remaining = (startedAtMs + CLAIM_ATTEMPT_TIMEOUT_MS - SystemClock.uptimeMillis())
            .coerceAtLeast(0L)
        return minOf(randomDelay(minMs, maxMs), remaining)
    }

    private fun continueAfterOpeningClaims(
        claimCount: Int,
        lastClaimBaseline: Set<String>?,
    ) {
        val startTaskScan: () -> Unit = {
            if (!manualInterruptionDetected && runActive &&
                taskLoopPhase == TaskLoopPhase.SCANNING
            ) {
                val beginScan: () -> Unit = {
                    if (!manualInterruptionDetected && runActive &&
                        taskLoopPhase == TaskLoopPhase.SCANNING
                    ) {
                        taskScrolls = 0
                        lastPageSignature = emptySet()
                        processNextTask()
                    }
                }
                taskScrolls = 0
                lastPageSignature = emptySet()
                if (claimCount > 0) {
                    logProgress("Re-anchoring at the top after opening reward collection")
                    scrollToPageTop { beginScan() }
                } else {
                    beginScan()
                }
            }
        }
        if (claimCount <= 0 || lastClaimBaseline == null) {
            startTaskScan()
            return
        }

        logProgress(
            "Waiting up to ${TASK_LIST_REFRESH_TIMEOUT_MS / 1000}s for task rows to refresh " +
                    "after opening claim"
        )
        noteProgress(TASK_LIST_REFRESH_TIMEOUT_MS)
        waitForTaskListRefresh(
            baseline = lastClaimBaseline,
            purpose = "opening claim",
            onReady = startTaskScan,
        )
    }

    /**
     * Waits for readable task rows to remain stable for two samples. A claim may update only the
     * reward card or points balance, so task-row mutation is useful diagnostic evidence but is not a
     * prerequisite for continuing once the post-claim list itself is readable and settled.
     */
    private fun waitForTaskListRefresh(
        baseline: Set<String>,
        purpose: String,
        startedAtMs: Long = SystemClock.uptimeMillis(),
        observedChange: Boolean = false,
        stableSignature: Set<String> = emptySet(),
        stableHits: Int = 0,
        onReady: () -> Unit,
    ) {
        if (manualInterruptionDetected || !runActive) return

        val root = targetAppRoot()
        val current = if (foregroundPackage() == targetPackageName && root != null) {
            taskListSignature(root)
        } else {
            emptySet()
        }
        val changedNow = observedChange || (current.isNotEmpty() && current != baseline)
        val nextStableSignature: Set<String>
        val nextStableHits: Int
        if (current.isNotEmpty()) {
            nextStableSignature = current
            nextStableHits = if (current == stableSignature) stableHits + 1 else 1
        } else {
            // An empty/transitional hierarchy cannot count as a stable task list.
            nextStableSignature = emptySet()
            nextStableHits = 0
        }

        if (nextStableHits >= TASK_LIST_REFRESH_STABLE_SAMPLES) {
            val refreshDetail = if (changedNow) "refreshed" else "remained unchanged"
            logProgress(
                "Task rows are readable and stable after $purpose; they $refreshDetail " +
                        "(${baseline.size} → ${current.size} row signatures)"
            )
            onReady()
            return
        }

        val elapsed = SystemClock.uptimeMillis() - startedAtMs
        if (elapsed >= TASK_LIST_REFRESH_TIMEOUT_MS) {
            logProgress(
                "Task rows did not become readable and stable within " +
                        "${TASK_LIST_REFRESH_TIMEOUT_MS / 1000}s after $purpose; " +
                        "continuing with the latest hierarchy"
            )
            onReady()
            return
        }

        mainHandler.postDelayed(
            {
                waitForTaskListRefresh(
                    baseline = baseline,
                    purpose = purpose,
                    startedAtMs = startedAtMs,
                    observedChange = changedNow,
                    stableSignature = nextStableSignature,
                    stableHits = nextStableHits,
                    onReady = onReady,
                )
            },
            randomDelay(TASK_LIST_REFRESH_POLL_MIN_MS, TASK_LIST_REFRESH_POLL_MAX_MS)
        )
    }

    private fun collectPendingAwards(
        attempt: Int = 1,
        claimCount: Int = 0,
        startedAtMs: Long = SystemClock.uptimeMillis(),
        lastClaimBaseline: Set<String>? = null,
        lastClickedClaimSignature: String? = null,
        observedClaimStateChange: Boolean = false,
    ) {
        if (manualInterruptionDetected) return
        val stopReason = claimStopReason(startedAtMs)
        if (stopReason != null) {
            logProgress("Opening claim check stopped: $stopReason")
            continueAfterOpeningClaims(claimCount, lastClaimBaseline)
            return
        }

        val root = appRoot()
        val preClaimSignature = root?.let { taskListSignature(it) }.orEmpty()
        val claimState = root?.let { findClaimState(it) }
        val stateChanged = observedClaimStateChange ||
                (lastClickedClaimSignature != null &&
                        claimState?.signature != null &&
                        claimState.signature != lastClickedClaimSignature)
        val target = claimState?.target
        val canClick = target != null &&
                (lastClickedClaimSignature == null ||
                        target.stateSignature != lastClickedClaimSignature || stateChanged)
        if (target != null && canClick && clickClaimButton(target)) {
            val nextClaimCount = claimCount + 1
            val pending = target.pendingCount?.let { ", pending count $it" }.orEmpty()
            recordAction(
                "Pressed pending-awards button ('${target.label}') click $nextClaimCount$pending"
            )
            // Re-inspect the reward card after the popup settles. The same target may be clicked again
            // only after its card signature changes, preventing a stale WebView node from looping.
            mainHandler.postDelayed({
                if (findAndClickCloseButton()) logProgress("Closed the reward popup")
                val refreshedStopReason = claimStopReason(startedAtMs)
                when {
                    refreshedStopReason != null -> {
                        logProgress("Opening claim check stopped: $refreshedStopReason")
                        continueAfterOpeningClaims(nextClaimCount, preClaimSignature)
                    }
                    nextClaimCount >= MAX_CLAIM_CLICKS_SAFETY -> {
                        logProgress(
                            "Stopped the opening claim loop at the $MAX_CLAIM_CLICKS_SAFETY-click " +
                                    "safety limit; the button may be stale"
                        )
                        continueAfterOpeningClaims(nextClaimCount, preClaimSignature)
                    }
                    else -> collectPendingAwards(
                        attempt = 1,
                        claimCount = nextClaimCount,
                        startedAtMs = startedAtMs,
                        lastClaimBaseline = preClaimSignature,
                        lastClickedClaimSignature = target.stateSignature,
                    )
                }
            }, claimDelay(startedAtMs, CLAIM_REFRESH_MIN_MS, CLAIM_REFRESH_MAX_MS))
            return
        }

        if (attempt < CLAIM_POLLS) {
            mainHandler.postDelayed(
                {
                    collectPendingAwards(
                        attempt = attempt + 1,
                        claimCount = claimCount,
                        startedAtMs = startedAtMs,
                        lastClaimBaseline = lastClaimBaseline,
                        lastClickedClaimSignature = lastClickedClaimSignature,
                        observedClaimStateChange = stateChanged,
                    )
                },
                claimDelay(startedAtMs, CLAIM_POLL_MIN_MS, CLAIM_POLL_MAX_MS)
            )
            return
        }
        if (claimCount == 0) {
            logProgress("Nothing waiting to be collected after $CLAIM_POLLS looks")
        } else {
            logProgress(
                "Opening claim loop complete after $claimCount click(s); " +
                        "no changed claim target appeared for $CLAIM_POLLS looks"
            )
        }
        continueAfterOpeningClaims(claimCount, lastClaimBaseline)
    }

    private data class ClaimState(
        val signature: String?,
        val target: ClaimTarget?,
    )

    private data class ClaimTarget(
        val label: String,
        val labelBounds: Rect,
        val clickNode: AccessibilityNodeInfo?,
        val stateSignature: String,
        val pendingCount: Int?,
        val source: String,
    )

    /**
     * Reads the reward summary card and returns its exact right-side claim control when available.
     * The module ID and geometry come from the captured hierarchy/screenshot. The old global lookup is
     * retained only as a constrained fallback for builds that do not expose the module ID.
     */
    private fun findClaimState(root: AccessibilityNodeInfo): ClaimState {
        val module = findNodeByViewId(root, CLAIM_REWARD_MODULE_ID)
        if (module != null) {
            val moduleBounds = Rect().also { runCatching { module.getBoundsInScreen(it) } }
            if (isBoundsVisible(moduleBounds)) {
                val texts = collectTextNodes(module, includeOffscreen = true)
                val stateParts = texts
                    .map { "${it.text}@${it.bounds.left},${it.bounds.top},${it.bounds.right},${it.bounds.bottom}" }
                    .sorted()
                val signature = "module:${moduleBounds.flattenToString()}|${stateParts.joinToString("|")}" 
                var pendingCount: Int? = null
                for (text in texts) {
                    val match = CLAIM_PENDING_COUNT_RE.find(text.text) ?: continue
                    pendingCount = match.groupValues[1].toIntOrNull()
                    if (pendingCount != null) break
                }
                val rightEdgeStart = moduleBounds.left +
                        (moduleBounds.width() * CLAIM_MODULE_ACTION_MIN_X_FRACTION).toInt()
                val label = texts
                    .filter {
                        it.text in CLAIM_ALL_LABELS &&
                                isBoundsVisible(it.bounds) &&
                                it.bounds.centerX() >= rightEdgeStart &&
                                it.bounds.left >= moduleBounds.left &&
                                it.bounds.right <= moduleBounds.right &&
                                it.bounds.top >= moduleBounds.top &&
                                it.bounds.bottom <= moduleBounds.bottom
                    }
                    .minByOrNull { it.bounds.top }
                if (label == null) return ClaimState(signature, null)

                val clickable = clickableSelfOrAncestor(label.node, maxDepth = 4)?.takeIf { node ->
                    val bounds = Rect().also { runCatching { node.getBoundsInScreen(it) } }
                    isBoundsVisible(bounds) &&
                            bounds.centerX() >= rightEdgeStart &&
                            bounds.width() <= moduleBounds.width() * CLAIM_MAX_TARGET_WIDTH_FRACTION &&
                            bounds.left >= moduleBounds.left && bounds.right <= moduleBounds.right &&
                            bounds.top >= moduleBounds.top && bounds.bottom <= moduleBounds.bottom
                }
                return ClaimState(
                    signature,
                    ClaimTarget(
                        label = label.text,
                        labelBounds = label.bounds,
                        clickNode = clickable,
                        stateSignature = signature,
                        pendingCount = pendingCount,
                        source = "reward module $CLAIM_REWARD_MODULE_ID",
                    )
                )
            }
        }

        val screenWidth = resources.displayMetrics.widthPixels
        val fallback = collectTextNodes(root)
            .filter {
                it.text in CLAIM_ALL_LABELS &&
                        it.bounds.centerX() >= screenWidth * CLAIM_FALLBACK_MIN_X_FRACTION
            }
            .minByOrNull { it.bounds.top }
            ?: return ClaimState(null, null)
        val signature = "fallback:${fallback.text}@${fallback.bounds.flattenToString()}"
        val clickable = clickableSelfOrAncestor(fallback.node, maxDepth = 4)?.takeIf { node ->
            val bounds = Rect().also { runCatching { node.getBoundsInScreen(it) } }
            isBoundsVisible(bounds) &&
                    bounds.centerX() >= screenWidth * CLAIM_FALLBACK_MIN_X_FRACTION &&
                    bounds.width() <= screenWidth * CLAIM_MAX_TARGET_WIDTH_FRACTION
        }
        return ClaimState(
            signature,
            ClaimTarget(
                label = fallback.text,
                labelBounds = fallback.bounds,
                clickNode = clickable,
                stateSignature = signature,
                pendingCount = null,
                source = "right-side global fallback",
            )
        )
    }

    /** Clicks a previously validated claim target, preferring its bounded clickable ancestor. */
    private fun clickClaimButton(target: ClaimTarget): Boolean {
        val clicked = target.clickNode?.let { tryPerformClick(it) } ?: tryClickRect(target.labelBounds)
        if (!clicked) {
            logProgress("Found '${target.label}' in ${target.source} but could not click it")
        }
        return clicked
    }

    // ---------------------------------------------------------------------------------------------
    // Task list processing
    // ---------------------------------------------------------------------------------------------

    /** Lowest piece of text on screen, so the log shows how far down the page we actually got. */
    private fun bottomMostText(root: AccessibilityNodeInfo): String =
        collectTextNodes(root).maxByOrNull { it.bounds.bottom }?.text?.take(24)?.let { "'$it'" }
            ?: "(nothing readable)"

    /** Text plus vertical position of everything on screen, used to tell whether the list moved. */
    private fun pageSignature(root: AccessibilityNodeInfo): Set<String> =
        collectTextNodes(root).map { "${it.text}@${it.bounds.top}" }.toSet()

    /** Semantic task-row content; reward popups and layout-only movement do not count as refreshes. */
    private fun taskListSignature(root: AccessibilityNodeInfo): Set<String> =
        buildTaskRows(collectTextNodes(root))
            .map { "${it.title}|${it.description}|${it.buttonText}" }
            .toSet()

    /** One row of the task list: icon, title, description on the left, action button on the right. */
    private data class TaskRow(
        val title: String,
        val description: String,
        val buttonText: String,
        val buttonNode: AccessibilityNodeInfo,
        val buttonBounds: Rect,
        /** Top of the title, used to test the row against the section header. */
        val titleTop: Int,
    )

    /**
     * Works the task list from the full exposed hierarchy while preserving visible-only clicks.
     * Direct show-on-screen requests avoid blind page-by-page discovery; controlled drags remain the
     * bounded fallback for WebView builds that do not support hierarchy-guided navigation.
     */
    private fun processNextTask(
        attempt: Int = 1,
        noMoveStreak: Int = 0,
        showOnScreenAttemptedTitle: String? = null,
    ) {
        if (manualInterruptionDetected || !runActive) return
        if (taskLoopPhase == TaskLoopPhase.CLAIMING || taskLoopPhase == TaskLoopPhase.FINISHED) return

        val root = appRoot()
        if (root == null || foregroundPackage() != targetPackageName) {
            if (attempt >= MAX_SEARCH_ATTEMPTS) {
                finishTaskLoop(
                    "lost the app (foreground: ${foregroundPackage()})",
                    allowClaimRescan = false
                )
                return
            }
            mainHandler.postDelayed(
                { processNextTask(attempt + 1, noMoveStreak, showOnScreenAttemptedTitle) },
                randomDelay(700, 1200)
            )
            return
        }

        // Ctrip exposes the whole WebView document at once. Use that complete hierarchy to plan the
        // next destination, but retain the visible-only row set as the sole source of clickable tasks.
        val allTexts = collectTextNodes(root, includeOffscreen = true)
        val rows = buildTaskRows(allTexts.filter { isBoundsVisible(it.bounds) })
        val allRows = buildTaskRows(allTexts)
        val actionable = rows.filter {
            ACTION_BUTTON_RE.matches(it.buttonText) &&
                    !isIgnoredRow(it) &&
                    it.title !in processedTasks
        }
        val allActionable = allRows.filter {
            ACTION_BUTTON_RE.matches(it.buttonText) &&
                    !isIgnoredRow(it) &&
                    it.title !in processedTasks
        }
        val finished = allRows.filter { it.buttonText in SKIP_BUTTON_TEXTS }
        val ignored = allRows.filter { isIgnoredRow(it) }
        if (attempt == 1 && allRows.isNotEmpty()) {
            logProgress(
                "Task hierarchy: ${allRows.size} row(s), ${allActionable.size} supported unfinished; " +
                        "visible: ${rows.size}, actionable: ${actionable.size}"
            )
            finished.forEach {
                if (skippedTasks.add(it.title)) logProgress("Skipping '${it.title}' (${it.buttonText})")
            }
            ignored.forEach {
                if (ignoredTasks.add(it.title)) {
                    logProgress("Leaving '${it.title}' alone (${it.buttonText})")
                }
            }
        }

        // After ACTION_SHOW_ON_SCREEN, only the row that was planned is eligible for a click. A
        // different action becoming visible during the jump must never inherit the planned identity.
        val next = if (showOnScreenAttemptedTitle != null) {
            actionable
                .filter { it.title == showOnScreenAttemptedTitle }
                .minByOrNull { it.buttonBounds.top }
        } else {
            actionable.minByOrNull { it.buttonBounds.top }
        }
        if (next != null) {
            if (AutomationSettings.matchesWhitelist(next.title, next.description)) {
                logProgress("'${next.title}' is whitelisted, running it despite its ${next.buttonText} button")
            }
            startTask(next)
            return
        }

        val planned = if (showOnScreenAttemptedTitle != null) {
            allActionable.firstOrNull { it.title == showOnScreenAttemptedTitle }
        } else {
            allActionable.minByOrNull { it.titleTop }
        }
        val fullListExposed = allTexts.any { it.text.contains(TASK_LIST_END_TEXT) }
        if (planned == null && fullListExposed) {
            if (showOnScreenAttemptedTitle != null && allActionable.isNotEmpty()) {
                logProgress(
                    "Planned task '$showOnScreenAttemptedTitle' is no longer an unfinished row; " +
                            "replanning from the complete hierarchy"
                )
                mainHandler.post { processNextTask(showOnScreenAttemptedTitle = null) }
            } else {
                finishTaskLoop("the complete task hierarchy has no remaining supported task actions")
            }
            return
        }

        var attemptedTitle = showOnScreenAttemptedTitle
        if (planned != null && planned.title != showOnScreenAttemptedTitle) {
            attemptedTitle = planned.title
            val requested = runCatching {
                planned.buttonNode.performAction(
                    AccessibilityNodeInfo.AccessibilityAction.ACTION_SHOW_ON_SCREEN.id
                )
            }.getOrDefault(false)
            if (requested) {
                logProgress("Bringing next task into view: '${planned.title}'")
                lastPageSignature = pageSignature(root)
                mainHandler.postDelayed(
                    {
                        processNextTask(
                            noMoveStreak = 0,
                            showOnScreenAttemptedTitle = planned.title,
                        )
                    },
                    TASK_SHOW_ON_SCREEN_SETTLE_MS,
                )
                return
            }
            logProgress("WebView could not reveal '${planned.title}' directly; using a controlled drag")
        }

        // Fallback for WebView builds that expose only visible nodes or reject ACTION_SHOW_ON_SCREEN.
        // When a known row is outside the viewport, drag toward its document position rather than
        // always moving down and potentially leaving a missed row behind.
        val screenHeight = resources.displayMetrics.heightPixels
        val scrollDown = when {
            planned == null -> true
            planned.titleTop < 0 || planned.buttonBounds.bottom <= 0 -> false
            planned.buttonBounds.top >= screenHeight -> true
            else -> planned.buttonBounds.centerY() >= screenHeight / 2
        }
        val signature = pageSignature(root)
        val noMoveNow = if (signature == lastPageSignature) noMoveStreak + 1 else 0
        if (noMoveNow >= END_OF_PAGE_CONFIRMATIONS) {
            val detail = planned?.let { " while trying to reach '${it.title}'" }.orEmpty()
            finishTaskLoop(
                "reached the end of page movement$detail " +
                        "(bottom of screen: ${bottomMostText(root)})"
            )
            return
        }
        if (taskScrolls >= MAX_TASK_SCROLLS) {
            finishTaskLoop("used all $MAX_TASK_SCROLLS controlled drags")
            return
        }
        lastPageSignature = signature
        taskScrolls++
        val direction = if (scrollDown) "down" else "up"
        logProgress(
            "No supported unfinished task is fully visible; scrolling $direction " +
                    "($taskScrolls/$MAX_TASK_SCROLLS)"
        )
        scrollTaskList(down = scrollDown)
        mainHandler.postDelayed(
            {
                processNextTask(
                    noMoveStreak = noMoveNow,
                    showOnScreenAttemptedTitle = attemptedTitle,
                )
            },
            randomDelay(700, 1100),
        )
    }

    /**
     * Handles a complete top-to-bottom scan. The first complete scan starts a final claim pass; every
     * claim pass is followed by another complete scan because claiming can refresh and unlock tasks.
     * Summary is allowed only when that refreshed scan starts no new task.
     */
    private fun finishTaskLoop(reason: String, allowClaimRescan: Boolean = true) {
        if (!runActive || taskLoopPhase == TaskLoopPhase.FINISHED) return
        if (manualInterruptionDetected) return

        if (!allowClaimRescan || foregroundPackage() != targetPackageName) {
            completeTaskLoop(reason)
            return
        }

        when (taskLoopPhase) {
            TaskLoopPhase.SCANNING -> beginFinalClaimPass(reason)
            TaskLoopPhase.RESCANNING -> {
                val newTaskCount = tasksStarted - postClaimRescanBaseline
                if (newTaskCount > 0) {
                    logProgress(
                        "Post-claim scan started $newTaskCount new task(s); " +
                                "collecting their refreshed rewards"
                    )
                    beginFinalClaimPass(reason)
                } else {
                    completeTaskLoop("no new executable tasks after the final claim — $reason")
                }
            }
            TaskLoopPhase.CLAIMING -> Unit // Its asynchronous callback owns the next transition.
            TaskLoopPhase.FINISHED -> Unit
        }
    }

    private fun beginFinalClaimPass(reason: String) {
        if (finalClaimPasses >= MAX_FINAL_CLAIM_PASSES) {
            completeTaskLoop(
                "reached the $MAX_FINAL_CLAIM_PASSES-pass claim/rescan safety limit — $reason"
            )
            return
        }
        taskLoopPhase = TaskLoopPhase.CLAIMING
        finalClaimPasses++
        logProgress(
            "Task scan complete — final claim pass $finalClaimPasses, then rescan refreshed tasks"
        )
        scrollToPageTop {
            if (!manualInterruptionDetected && runActive && taskLoopPhase == TaskLoopPhase.CLAIMING) {
                claimAgainThenFinish(reason)
            }
        }
    }

    /** Starts the mandatory top-to-bottom scan after a final claim pass. */
    private fun beginPostClaimRescan(
        reason: String,
        claimCount: Int,
        lastClaimBaseline: Set<String>? = null,
    ) {
        if (manualInterruptionDetected || !runActive || taskLoopPhase != TaskLoopPhase.CLAIMING) return
        taskLoopPhase = TaskLoopPhase.RESCANNING
        postClaimRescanBaseline = tasksStarted
        taskScrolls = 0
        lastPageSignature = emptySet()
        logProgress(
            "Final claim pass $finalClaimPasses ended after $claimCount click(s); " +
                    "checking the refreshed task list again"
        )

        val startRescan: () -> Unit = {
            if (!manualInterruptionDetected && runActive &&
                taskLoopPhase == TaskLoopPhase.RESCANNING
            ) {
                scrollToPageTop {
                    if (!manualInterruptionDetected && runActive &&
                        taskLoopPhase == TaskLoopPhase.RESCANNING
                    ) {
                        taskScrolls = 0
                        lastPageSignature = emptySet()
                        mainHandler.postDelayed(
                            { processNextTask() },
                            POST_CLAIM_RESCAN_SETTLE_MS
                        )
                    }
                }
            }
        }

        if (claimCount > 0 && lastClaimBaseline != null) {
            logProgress(
                "Waiting up to ${TASK_LIST_REFRESH_TIMEOUT_MS / 1000}s for task rows to refresh " +
                        "after final claim pass $finalClaimPasses"
            )
            noteProgress(TASK_LIST_REFRESH_TIMEOUT_MS)
            waitForTaskListRefresh(
                baseline = lastClaimBaseline,
                purpose = "final claim pass $finalClaimPasses",
                onReady = startRescan,
            )
        } else {
            startRescan()
        }
    }

    private fun completeTaskLoop(reason: String) {
        if (taskLoopPhase == TaskLoopPhase.FINISHED) return
        taskLoopPhase = TaskLoopPhase.FINISHED
        expectingExternalApp = false
        finishCurrentApp(
            "Done: started $tasksStarted task(s) — $reason. " +
                    "Actions: ${actionLog.joinToString(" -> ")}"
        )
    }

    /** Drags the page back to the top, then runs [then]. */
    private fun scrollToPageTop(attempt: Int = 1, noMoveStreak: Int = 0, then: () -> Unit) {
        if (manualInterruptionDetected) {
            then()
            return
        }
        val root = appRoot() ?: run { then(); return }
        val signature = pageSignature(root)
        val noMoveNow = if (attempt > 1 && signature == lastPageSignature) noMoveStreak + 1 else 0
        if (noMoveNow >= END_OF_PAGE_CONFIRMATIONS || attempt > MAX_TASK_SCROLLS) {
            lastPageSignature = emptySet()
            logProgress("At the top of the page")
            then()
            return
        }
        lastPageSignature = signature
        scrollTaskList(down = false)
        mainHandler.postDelayed(
            { scrollToPageTop(attempt + 1, noMoveNow, then) },
            randomDelay(600, 900)
        )
    }

    /** Second go at 一键领 now that tasks have been completed, then finish for real. */
    private fun claimAgainThenFinish(
        reason: String,
        attempt: Int = 1,
        claimCount: Int = 0,
        startedAtMs: Long = SystemClock.uptimeMillis(),
        lastClaimBaseline: Set<String>? = null,
        lastClickedClaimSignature: String? = null,
        observedClaimStateChange: Boolean = false,
    ) {
        if (manualInterruptionDetected || !runActive ||
            taskLoopPhase != TaskLoopPhase.CLAIMING
        ) return
        val stopReason = claimStopReason(startedAtMs)
        if (stopReason != null) {
            logProgress("Final claim check stopped: $stopReason")
            beginPostClaimRescan(reason, claimCount, lastClaimBaseline)
            return
        }

        val root = appRoot()
        val preClaimSignature = root?.let { taskListSignature(it) }.orEmpty()
        val claimState = root?.let { findClaimState(it) }
        val stateChanged = observedClaimStateChange ||
                (lastClickedClaimSignature != null &&
                        claimState?.signature != null &&
                        claimState.signature != lastClickedClaimSignature)
        val target = claimState?.target
        val canClick = target != null &&
                (lastClickedClaimSignature == null ||
                        target.stateSignature != lastClickedClaimSignature || stateChanged)
        if (target != null && canClick && clickClaimButton(target)) {
            val nextClaimCount = claimCount + 1
            val pending = target.pendingCount?.let { ", pending count $it" }.orEmpty()
            recordAction(
                "Pressed tasks-rewards button ('${target.label}') click $nextClaimCount$pending"
            )
            mainHandler.postDelayed({
                if (findAndClickCloseButton()) logProgress("Closed the reward popup")
                val refreshedStopReason = claimStopReason(startedAtMs)
                when {
                    refreshedStopReason != null -> {
                        logProgress("Final claim check stopped: $refreshedStopReason")
                        beginPostClaimRescan(reason, nextClaimCount, preClaimSignature)
                    }
                    nextClaimCount >= MAX_CLAIM_CLICKS_SAFETY -> {
                        logProgress(
                            "Stopped the final claim loop at the $MAX_CLAIM_CLICKS_SAFETY-click " +
                                    "safety limit; the button may be stale"
                        )
                        beginPostClaimRescan(reason, nextClaimCount, preClaimSignature)
                    }
                    else -> claimAgainThenFinish(
                        reason = reason,
                        attempt = 1,
                        claimCount = nextClaimCount,
                        startedAtMs = startedAtMs,
                        lastClaimBaseline = preClaimSignature,
                        lastClickedClaimSignature = target.stateSignature,
                    )
                }
            }, claimDelay(startedAtMs, CLAIM_REFRESH_MIN_MS, CLAIM_REFRESH_MAX_MS))
            return
        }
        if (attempt < CLAIM_POLLS) {
            mainHandler.postDelayed(
                {
                    claimAgainThenFinish(
                        reason = reason,
                        attempt = attempt + 1,
                        claimCount = claimCount,
                        startedAtMs = startedAtMs,
                        lastClaimBaseline = lastClaimBaseline,
                        lastClickedClaimSignature = lastClickedClaimSignature,
                        observedClaimStateChange = stateChanged,
                    )
                },
                claimDelay(startedAtMs, CLAIM_POLL_MIN_MS, CLAIM_POLL_MAX_MS)
            )
            return
        }
        if (claimCount == 0) {
            logProgress("Nothing more to collect")
        } else {
            logProgress(
                "Final claim loop complete after $claimCount click(s); " +
                        "no changed claim target appeared for $CLAIM_POLLS looks"
            )
        }
        beginPostClaimRescan(reason, claimCount, lastClaimBaseline)
    }

    /**
     * Groups the visible text nodes into task rows.
     *
     * The action button and the task title both start with 去 (去七猫 vs 去七猫免费看小说短剧), so they
     * cannot be told apart by text. Position does it: buttons sit in the right-hand column, titles and
     * descriptions in the left.
     */
    private fun buildTaskRows(texts: List<TextNode>): List<TaskRow> {
        val screenWidth = resources.displayMetrics.widthPixels
        val rightColumn = screenWidth * ACTION_COLUMN_MIN_X_FRACTION
        val taskContentMinX = screenWidth * TASK_CONTENT_MIN_X_FRACTION
        val leftTexts = texts.filter { it.bounds.centerX() < rightColumn }
        val titleCandidates = leftTexts.filter {
            val text = it.text.trim()
            it.bounds.left >= taskContentMinX &&
                    text.isNotEmpty() &&
                    text != TASK_PAGE_TITLE &&
                    text !in TASK_GROUP_NAMES &&
                    text !in CLAIM_ALL_LABELS &&
                    text !in NO_CLAIM_REWARD_TEXTS &&
                    CLAIM_CARD_TEXT_PREFIXES.none { prefix -> text.startsWith(prefix) }
        }

        val rows = mutableListOf<TaskRow>()
        val buttons = texts.filter {
            it.bounds.centerX() >= rightColumn &&
                    (ACTION_BUTTON_RE.matches(it.text) || it.text in SKIP_BUTTON_TEXTS)
        }
        for (button in buttons) {
            // A real title begins shortly before its right-column action. This top-coordinate rule
            // also works for Ctrip's clipped/inverted off-screen rectangles and prevents fixed page
            // or tab chrome from being paired with a newly revealed action.
            val title = titleCandidates
                .filter {
                    val lead = button.bounds.top - it.bounds.top
                    lead in 0..TASK_TITLE_MAX_LEAD_PX
                }
                .maxByOrNull { it.bounds.top }
                ?: continue
            // Description: the next left-aligned line beneath the title. Compare top coordinates
            // rather than title.bottom because Ctrip clips off-screen bottoms to the viewport,
            // producing inverted rectangles while preserving each node's document-relative top.
            val description = leftTexts
                .filter {
                    it.bounds.top > title.bounds.top &&
                            it.bounds.top - title.bounds.top <= TASK_DESC_MAX_GAP_PX &&
                            abs(it.bounds.left - title.bounds.left) <= TASK_DESC_MAX_INDENT_PX
                }
                .minByOrNull { it.bounds.top }
                ?.text
                .orEmpty()
            rows.add(
                TaskRow(title.text, description, button.text, button.node, button.bounds, title.bounds.top)
            )
        }
        return rows.distinctBy { it.title }
    }

    private fun isPlanetFollowTask(row: TaskRow): Boolean =
        row.buttonText == PLANET_FOLLOW_ACTION && PLANET_FOLLOW_TASK_RE.matches(row.title.trim())

    private fun isHotelRankingTask(row: TaskRow): Boolean =
        row.buttonText == HOTEL_RANKING_ACTION && row.title.trim() == HOTEL_RANKING_TASK_TITLE

    private fun isDailyCashNoteTask(row: TaskRow): Boolean =
        row.buttonText == DAILY_CASH_NOTE_ACTION &&
                row.title.trim() == DAILY_CASH_NOTE_TASK_TITLE &&
                row.description.contains(DAILY_CASH_NOTE_DESCRIPTION)

    /** Registry lookup is the only place task-list wording is coupled to mini-program behavior. */
    private fun miniProgramSpecFor(title: String): MiniProgramTaskSpec? {
        val normalized = title.trim()
        return MINI_PROGRAM_TASK_SPECS.firstOrNull { it.taskTitle.matches(normalized) }
    }

    private fun miniProgramSpecFor(row: TaskRow): MiniProgramTaskSpec? =
        miniProgramSpecFor(row.title)

    private fun startTask(row: TaskRow) {
        val miniProgramSpec = miniProgramSpecFor(row)
        val planetFollowTask = isPlanetFollowTask(row)
        val hotelRankingTask = isHotelRankingTask(row)
        val dailyCashNoteTask = isDailyCashNoteTask(row)
        processedTasks.add(row.title)
        currentTaskTitle = row.title
        planetFollowState = if (planetFollowTask) {
            PlanetFollowState.WAITING_FOR_CONTROL
        } else {
            PlanetFollowState.IDLE
        }
        planetFollowDeadlineMs = if (planetFollowTask) {
            SystemClock.uptimeMillis() + PLANET_FOLLOW_TIMEOUT_MS
        } else {
            0L
        }
        hotelRankingState = if (hotelRankingTask) {
            HotelRankingState.WAITING_FOR_DATA
        } else {
            HotelRankingState.IDLE
        }
        hotelRankingDeadlineMs = if (hotelRankingTask) {
            SystemClock.uptimeMillis() + HOTEL_RANKING_TIMEOUT_MS
        } else {
            0L
        }
        hotelRankingSourceSignature = emptySet()
        hotelRankingMarkerText = null
        hotelRankingNavigationHits = 0
        hotelRankingTapAttempt = 0
        hotelRankingVerificationPolls = 0
        hotelRankingDiagnosticsDumped = false
        dailyCashNoteState = if (dailyCashNoteTask) {
            DailyCashNoteState.WAITING_FOR_DESTINATION
        } else {
            DailyCashNoteState.IDLE
        }
        dailyCashNoteDeadlineMs = if (dailyCashNoteTask) {
            SystemClock.uptimeMillis() + DAILY_CASH_NOTE_TIMEOUT_MS
        } else {
            0L
        }
        dailyCashDestinationHits = 0
        dailyCashScrollAnchorTop = null
        dailyCashNavigationSignature = emptySet()
        dailyCashNavigationHits = 0
        dailyCashDwellSeconds = if (dailyCashNoteTask) {
            planDwell(row.description, row.title).seconds
        } else {
            0
        }
        dailyCashDiagnosticsDumped = false
        dailyCashTaskToken++
        tasksStarted++

        when {
            miniProgramSpec != null -> {
                val plan = planDwell(row.description, row.title)
                logProgressSection(
                    "Task $tasksStarted: ${row.title} → ${row.buttonText} " +
                            "(mini-program '${miniProgramSpec.id}', CTA ${miniProgramSpec.ctaDescription})"
                )
                if (row.description.isNotEmpty()) logProgress("Task note: ${row.description}")
                logProgress("After the CTA, staying ${plan.seconds}s before returning")
            }
            planetFollowTask -> {
                logProgressSection("Task $tasksStarted: ${row.title} → ${row.buttonText} (follow interaction)")
                if (row.description.isNotEmpty()) logProgress("Task note: ${row.description}")
            }
            hotelRankingTask -> {
                logProgressSection(
                    "Task $tasksStarted: ${row.title} → ${row.buttonText} (hotel ranking interaction)"
                )
                if (row.description.isNotEmpty()) logProgress("Task note: ${row.description}")
            }
            dailyCashNoteTask -> {
                val plan = planDwell(row.description, row.title)
                logProgressSection(
                    "Task $tasksStarted: ${row.title} → ${row.buttonText} " +
                            "(open a later note and stay ${plan.seconds}s)"
                )
                if (row.description.isNotEmpty()) logProgress("Task note: ${row.description}")
                logProgress(
                    "Task needs at least ${plan.statedSeconds ?: plan.seconds}s, staying " +
                            "${plan.seconds}s after the note page is verified"
                )
            }
            else -> {
                val plan = planDwell(row.description, row.title)
                val dwell = plan.seconds
                logProgressSection(
                    "Task $tasksStarted: ${row.title} → ${row.buttonText} (stay ${dwell}s)"
                )
                if (row.description.isNotEmpty()) logProgress("Task note: ${row.description}")
                when {
                    plan.statedSeconds == null ->
                        logProgress("No duration stated, using the ${dwell}s default")
                    plan.capped ->
                        logProgress(
                            "Task needs at least ${plan.statedSeconds}s but the stay is capped at ${dwell}s"
                        )
                    else ->
                        logProgress(
                            "Task needs at least ${plan.statedSeconds}s, staying ${dwell}s " +
                                    "(+${DWELL_SAFETY_MARGIN_SECONDS}s margin)"
                        )
                }
            }
        }

        // Suppress interruption handling while the task destination is in flight. Dedicated in-app
        // tasks deliberately do not capture or later kill another package.
        expectingExternalApp = true
        capturingTaskApps = !(planetFollowTask || hotelRankingTask || dailyCashNoteTask)
        taskAppCleanupToken++
        taskAppCleanupInProgress = false
        taskApps.clear()
        externalTaskCandidate = null
        externalTaskCandidateHits = 0
        confirmedExternalTaskApp = null
        clearExternalHandoffState()
        if (!performClick(ClickTarget(row.buttonNode, row.buttonBounds, "task button"))) {
            logProgress("Could not click ${row.buttonText}, skipping this task")
            expectingExternalApp = false
            capturingTaskApps = false
            failCurrentTaskWithScreenshot("button would not click") {
                mainHandler.postDelayed({ processNextTask() }, randomDelay(700, 1200))
            }
            return
        }
        recordAction("Clicked ${row.buttonText} for '${row.title}'")
        if (miniProgramSpec != null) {
            beginMiniProgramWatch(miniProgramSpec)
        }

        when {
            planetFollowTask -> {
                logProgress("Waiting for the destination's top-right $PLANET_FOLLOW_CONTROL")
                noteProgress(PLANET_FOLLOW_TIMEOUT_MS)
                mainHandler.postDelayed(
                    { awaitPlanetFollowControl() },
                    randomDelay(PLANET_FOLLOW_POLL_MIN_MS, PLANET_FOLLOW_POLL_MAX_MS)
                )
            }
            hotelRankingTask -> {
                logProgress(
                    "Waiting ${HOTEL_RANKING_DATA_SETTLE_MS / 1000}s for ranking data before " +
                            "tapping the hotel image"
                )
                noteProgress(HOTEL_RANKING_TIMEOUT_MS)
                mainHandler.postDelayed(
                    { awaitHotelRankingData() },
                    HOTEL_RANKING_DATA_SETTLE_MS
                )
            }
            dailyCashNoteTask -> {
                val taskToken = dailyCashTaskToken
                logProgress("Waiting for $DAILY_CASH_DESTINATION_MARKER before scrolling to note cards")
                noteProgress(DAILY_CASH_NOTE_TIMEOUT_MS + dailyCashDwellSeconds * 1000L)
                mainHandler.postDelayed(
                    { awaitDailyCashDestination(taskToken) },
                    DAILY_CASH_INITIAL_SETTLE_MS
                )
            }
            else -> {
                val dwell = planDwell(row.description, row.title).seconds
                mainHandler.postDelayed({ confirmLeaveApp(dwell) }, randomDelay(700, 1200))
            }
        }
    }

    /** Waits for and clicks the exact top-right 关注 control on a 星球号 destination page. */
    private fun awaitPlanetFollowControl() {
        if (manualInterruptionDetected || !runActive ||
            planetFollowState != PlanetFollowState.WAITING_FOR_CONTROL
        ) return

        val now = SystemClock.uptimeMillis()
        val root = targetAppRoot()
        if (now >= planetFollowDeadlineMs) {
            root?.let { dumpWindowForDiagnostics(it, "planet follow control not found") }
            failPlanetFollowTask(
                if (root == null) "planet destination was not readable"
                else "top-right $PLANET_FOLLOW_CONTROL was not found within " +
                        "${PLANET_FOLLOW_TIMEOUT_MS / 1000}s"
            )
            return
        }

        if (root != null) {
            val texts = collectTextNodes(root)
            if (!isOnTaskPage(texts)) {
                val target = findTopRightFollowControl(texts)
                if (target != null && performClick(target)) {
                    planetFollowState = PlanetFollowState.RETURNING
                    planetFollowDeadlineMs = 0L
                    capturingTaskApps = false
                    recordAction(
                        "Clicked top-right $PLANET_FOLLOW_CONTROL for '${currentTaskTitle.orEmpty()}' " +
                                "via ${target.how} ${target.bounds.toShortString()}"
                    )
                    mainHandler.postDelayed(
                        {
                            if (planetFollowState == PlanetFollowState.RETURNING) returnToTaskPage()
                        },
                        randomDelay(PLANET_FOLLOW_SETTLE_MIN_MS, PLANET_FOLLOW_SETTLE_MAX_MS)
                    )
                    return
                }
            }
        }

        val remaining = (planetFollowDeadlineMs - now).coerceAtLeast(0L)
        val delay = minOf(
            randomDelay(PLANET_FOLLOW_POLL_MIN_MS, PLANET_FOLLOW_POLL_MAX_MS),
            remaining
        )
        mainHandler.postDelayed({ awaitPlanetFollowControl() }, delay)
    }

    /**
     * Selects only an exact 关注 label in the destination header's upper-right area. A wide ancestor
     * (for example the whole header) is rejected so coordinate fallback remains inside the button.
     */
    private fun findTopRightFollowControl(texts: List<TextNode>): ClickTarget? {
        val width = resources.displayMetrics.widthPixels
        val height = resources.displayMetrics.heightPixels
        val chosen = texts
            .filter { it.text == PLANET_FOLLOW_CONTROL }
            .filter {
                it.bounds.centerX() >= width * PLANET_FOLLOW_MIN_X_FRACTION &&
                        it.bounds.centerY() <= height * PLANET_FOLLOW_MAX_Y_FRACTION
            }
            .minByOrNull { it.bounds.top }
            ?: return null

        val clickable = clickableSelfOrAncestor(chosen.node, maxDepth = 4)
        if (clickable != null) {
            val bounds = Rect().also { runCatching { clickable.getBoundsInScreen(it) } }
            val safeContainer = !bounds.isEmpty() &&
                    bounds.centerX() >= width * PLANET_FOLLOW_MIN_X_FRACTION &&
                    bounds.centerY() <= height * PLANET_FOLLOW_MAX_Y_FRACTION &&
                    bounds.width() <= width * PLANET_FOLLOW_MAX_WIDTH_FRACTION &&
                    bounds.height() <= height * PLANET_FOLLOW_MAX_HEIGHT_FRACTION
            if (safeContainer) {
                return ClickTarget(clickable, bounds, "top-right follow control")
            }
        }
        return ClickTarget(null, chosen.bounds, "top-right follow text")
    }

    /** Records an interaction failure, then safely backs out without later marking it successful. */
    private fun failPlanetFollowTask(reason: String) {
        if (planetFollowState != PlanetFollowState.WAITING_FOR_CONTROL) return
        logProgress("Planet follow task failed: $reason; returning to $TASK_PAGE_TITLE")
        capturingTaskApps = false
        taskApps.clear()
        externalTaskCandidate = null
        externalTaskCandidateHits = 0
        confirmedExternalTaskApp = null
        failCurrentTaskWithScreenshot(reason) { returnToTaskPage() }
    }

    /** Waits for the ranking list to render, then taps the device-scaled bottom hotel image area. */
    /** Waits for the ranking list to render, dumps it once, then starts calibrated image taps. */
    private fun awaitHotelRankingData() {
        if (manualInterruptionDetected || !runActive ||
            hotelRankingState != HotelRankingState.WAITING_FOR_DATA
        ) return

        val now = SystemClock.uptimeMillis()
        val root = targetAppRoot()
        if (foregroundPackage() == targetPackageName && root != null) {
            val texts = collectTextNodes(root)
            val signature = pageSignature(root)
            if (!isOnTaskPage(texts) && signature.isNotEmpty()) {
                val target = hotelRankingImageTarget()
                hotelRankingSourceSignature = signature
                hotelRankingMarkerText = findHotelRankingMarker(texts)
                hotelRankingNavigationHits = 0
                hotelRankingTapAttempt = 0
                hotelRankingVerificationPolls = 0
                if (!hotelRankingDiagnosticsDumped) {
                    hotelRankingDiagnosticsDumped = true
                    dumpWindowForDiagnostics(root, "hotel ranking before image tap", force = true)
                    logHotelRankingTapDiagnostics(root, target.bounds)
                    logProgress(
                        "Hotel ranking marker: " +
                                (hotelRankingMarkerText?.let { "'$it'" } ?: "not exposed; using signature fallback")
                    )
                }
                hotelRankingState = HotelRankingState.VERIFYING_NAVIGATION
                attemptHotelRankingImageTap()
                return
            }
        }

        if (now >= hotelRankingDeadlineMs) {
            root?.let {
                dumpWindowForDiagnostics(it, "hotel ranking data did not become ready", force = true)
            }
            val reason = when {
                root == null -> "hotel ranking page was not readable"
                isOnTaskPage(collectTextNodes(root)) -> "hotel ranking page did not open"
                else -> "hotel ranking data was still empty"
            }
            failHotelRankingTask(reason)
            return
        }

        val remaining = (hotelRankingDeadlineMs - now).coerceAtLeast(0L)
        mainHandler.postDelayed(
            { awaitHotelRankingData() },
            minOf(
                randomDelay(HOTEL_RANKING_VERIFY_POLL_MIN_MS, HOTEL_RANKING_VERIFY_POLL_MAX_MS),
                remaining
            )
        )
    }

    /** A stable title such as 阳朔高档酒店榜, shown on the ranking page but not hotel details. */
    private fun findHotelRankingMarker(texts: List<TextNode>): String? =
        texts.asSequence()
            .map { it.text.trim() }
            .firstOrNull { it.length in 4..24 && it.endsWith(HOTEL_RANKING_MARKER_SUFFIX) }

    /** Logs the live hierarchy and every clickable node intersecting the calibrated image rectangle. */
    private fun logHotelRankingTapDiagnostics(root: AccessibilityNodeInfo, target: Rect) {
        val width = resources.displayMetrics.widthPixels
        val height = resources.displayMetrics.heightPixels
        val plannedPoints = HOTEL_IMAGE_TAP_POINTS.joinToString { (xFraction, yFraction) ->
            "(${(width * xFraction).toInt()},${(height * yFraction).toInt()})"
        }
        logProgress(
            "Hotel image diagnostics: screen=${width}x$height, target=${target.toShortString()}, " +
                    "planned=$plannedPoints"
        )

        val overlapping = collectClickableInWindow(root)
            .filter { (_, bounds) -> !bounds.isEmpty() && Rect.intersects(bounds, target) }
            .take(HOTEL_RANKING_MAX_CLICKABLE_DUMP_NODES)
        if (overlapping.isEmpty()) {
            logProgress("Hotel image diagnostics: no accessibility-clickable node overlaps the target")
            return
        }
        logProgress("Hotel image diagnostics: ${overlapping.size} overlapping clickable node(s)")
        overlapping.forEachIndexed { index, (node, bounds) ->
            val text = runCatching { node.text?.toString()?.take(40).orEmpty() }.getOrDefault("")
            val desc = runCatching {
                node.contentDescription?.toString()?.take(40).orEmpty()
            }.getOrDefault("")
            val id = runCatching {
                node.viewIdResourceName?.substringAfterLast('/')?.take(40).orEmpty()
            }.getOrDefault("")
            val intersection = Rect(bounds).apply { intersect(target) }
            logProgress(
                "  hotel-clickable ${index + 1}: ${node.className?.toString()?.substringAfterLast('.')} " +
                        "txt='$text' desc='$desc' id='$id' bounds=${bounds.toShortString()} " +
                        "overlap=${intersection.toShortString()}"
            )
        }
    }

    /** Dispatches the next deterministic point from the supplied screenshot's first hotel image. */
    private fun attemptHotelRankingImageTap() {
        if (manualInterruptionDetected || !runActive ||
            hotelRankingState != HotelRankingState.VERIFYING_NAVIGATION
        ) return
        if (SystemClock.uptimeMillis() >= hotelRankingDeadlineMs) {
            failHotelRankingTask("hotel image attempts exceeded the interaction deadline")
            return
        }
        if (hotelRankingTapAttempt >= HOTEL_IMAGE_TAP_POINTS.size) {
            failHotelRankingTask("all ${HOTEL_IMAGE_TAP_POINTS.size} hotel image points were ignored")
            return
        }

        val attempt = hotelRankingTapAttempt + 1
        val (xFraction, yFraction) = HOTEL_IMAGE_TAP_POINTS[hotelRankingTapAttempt]
        hotelRankingTapAttempt = attempt
        hotelRankingVerificationPolls = 0
        hotelRankingNavigationHits = 0

        val width = resources.displayMetrics.widthPixels
        val height = resources.displayMetrics.heightPixels
        val x = (width * xFraction).coerceIn(1f, (width - 2).coerceAtLeast(1).toFloat())
        val y = (height * yFraction).coerceIn(1f, (height - 2).coerceAtLeast(1).toFloat())
        recordAction(
            "Hotel image tap $attempt/${HOTEL_IMAGE_TAP_POINTS.size}: " +
                    "screen=${width}x$height point=(${x.toInt()},${y.toInt()}) " +
                    "fraction=($xFraction,$yFraction)"
        )

        val accepted = try {
            jitterBeforeClick()
            if (manualInterruptionDetected) return
            val path = Path().apply { moveTo(x, y) }
            val stroke = GestureDescription.StrokeDescription(path, 20, 80)
            dispatchGesture(
                GestureDescription.Builder().addStroke(stroke).build(),
                object : GestureResultCallback() {
                    override fun onCompleted(gestureDescription: GestureDescription?) {
                        logProgress("Hotel image tap $attempt gesture completed at (${x.toInt()},${y.toInt()})")
                    }

                    override fun onCancelled(gestureDescription: GestureDescription?) {
                        logProgress("Hotel image tap $attempt gesture cancelled at (${x.toInt()},${y.toInt()})")
                    }
                },
                mainHandler
            )
        } catch (error: Throwable) {
            logProgress("Hotel image tap $attempt threw: ${error.message ?: error.javaClass.simpleName}")
            false
        }

        if (!accepted) {
            logProgress("Hotel image tap $attempt was rejected before dispatch")
            if (hotelRankingTapAttempt < HOTEL_IMAGE_TAP_POINTS.size) {
                mainHandler.postDelayed(
                    { attemptHotelRankingImageTap() },
                    HOTEL_RANKING_RETRY_SETTLE_MS
                )
            } else {
                failHotelRankingTask("all hotel image gestures were rejected")
            }
            return
        }
        mainHandler.postDelayed(
            { verifyHotelRankingNavigation() },
            randomDelay(HOTEL_RANKING_VERIFY_POLL_MIN_MS, HOTEL_RANKING_VERIFY_POLL_MAX_MS)
        )
    }

    /** Verifies that the ranking title disappeared; retries another calibrated point if it did not. */
    private fun verifyHotelRankingNavigation() {
        if (manualInterruptionDetected || !runActive ||
            hotelRankingState != HotelRankingState.VERIFYING_NAVIGATION
        ) return

        val now = SystemClock.uptimeMillis()
        val root = targetAppRoot()
        val texts = root?.let { collectTextNodes(it) }
        val signature = root?.let { pageSignature(it) }.orEmpty()
        val rankingMarkerVisible = texts?.let { visibleTexts ->
            val expected = hotelRankingMarkerText
            if (expected != null) {
                visibleTexts.any { it.text.trim() == expected }
            } else {
                findHotelRankingMarker(visibleTexts) != null
            }
        } == true
        val signatureChanged = signature.isNotEmpty() && signature != hotelRankingSourceSignature
        val navigated = foregroundPackage() == targetPackageName &&
                texts != null &&
                !isOnTaskPage(texts) &&
                !rankingMarkerVisible &&
                signatureChanged

        hotelRankingNavigationHits = if (navigated) hotelRankingNavigationHits + 1 else 0
        if (hotelRankingNavigationHits >= HOTEL_RANKING_NAVIGATION_CONFIRMATIONS) {
            hotelRankingState = HotelRankingState.RETURNING
            hotelRankingDeadlineMs = 0L
            logProgress(
                "Hotel ranking marker disappeared after tap $hotelRankingTapAttempt; " +
                        "returning to $TASK_PAGE_TITLE"
            )
            mainHandler.postDelayed(
                {
                    if (hotelRankingState == HotelRankingState.RETURNING) returnToTaskPage()
                },
                randomDelay(HOTEL_RANKING_DETAIL_SETTLE_MIN_MS, HOTEL_RANKING_DETAIL_SETTLE_MAX_MS)
            )
            return
        }

        if (now >= hotelRankingDeadlineMs) {
            root?.let {
                dumpWindowForDiagnostics(it, "hotel image did not open another page", force = true)
            }
            failHotelRankingTask(
                "hotel image did not open a detail page after $hotelRankingTapAttempt tap(s)"
            )
            return
        }

        hotelRankingVerificationPolls++
        if (rankingMarkerVisible &&
            hotelRankingVerificationPolls >= HOTEL_RANKING_POLLS_PER_TAP &&
            hotelRankingTapAttempt < HOTEL_IMAGE_TAP_POINTS.size
        ) {
            logProgress(
                "Ranking marker '${hotelRankingMarkerText ?: HOTEL_RANKING_MARKER_SUFFIX}' is still " +
                        "visible after tap $hotelRankingTapAttempt; trying the next image point"
            )
            mainHandler.postDelayed(
                { attemptHotelRankingImageTap() },
                HOTEL_RANKING_RETRY_SETTLE_MS
            )
            return
        }

        val remaining = (hotelRankingDeadlineMs - now).coerceAtLeast(0L)
        mainHandler.postDelayed(
            { verifyHotelRankingNavigation() },
            minOf(
                randomDelay(HOTEL_RANKING_VERIFY_POLL_MIN_MS, HOTEL_RANKING_VERIFY_POLL_MAX_MS),
                remaining
            )
        )
    }

    /** Bottom image rectangle measured from the supplied 478x1080 ranking screenshot. */
    private fun hotelRankingImageTarget(): ClickTarget {
        val width = resources.displayMetrics.widthPixels
        val height = resources.displayMetrics.heightPixels
        return ClickTarget(
            node = null,
            bounds = Rect(
                (width * HOTEL_IMAGE_LEFT_FRACTION).toInt(),
                (height * HOTEL_IMAGE_TOP_FRACTION).toInt(),
                (width * HOTEL_IMAGE_RIGHT_FRACTION).toInt(),
                (height * HOTEL_IMAGE_BOTTOM_FRACTION).toInt()
            ),
            how = "scaled first hotel-image region"
        )
    }

    private fun failHotelRankingTask(reason: String) {
        if (hotelRankingState == HotelRankingState.IDLE ||
            hotelRankingState == HotelRankingState.RETURNING
        ) return
        logProgress("Hotel ranking task failed: $reason; returning to $TASK_PAGE_TITLE")
        capturingTaskApps = false
        taskApps.clear()
        externalTaskCandidate = null
        externalTaskCandidateHits = 0
        confirmedExternalTaskApp = null
        failCurrentTaskWithScreenshot(reason) { returnToTaskPage() }
    }

    /** Waits for the cash activity to render and settle before performing its one controlled scroll. */
    private fun awaitDailyCashDestination(taskToken: Long) {
        if (taskToken != dailyCashTaskToken || manualInterruptionDetected || !runActive ||
            dailyCashNoteState != DailyCashNoteState.WAITING_FOR_DESTINATION
        ) return

        val now = SystemClock.uptimeMillis()
        val root = targetAppRoot()
        if (foregroundPackage() == targetPackageName && root != null) {
            val texts = collectTextNodes(root)
            val destinationTitle = texts.firstOrNull {
                it.text.trim() == DAILY_CASH_DESTINATION_MARKER
            }
            val browsePanelBounds = findBoundsByViewId(root, DAILY_CASH_BROWSE_PANEL_ID)
            val destinationVisible = !isOnTaskPage(texts) && destinationTitle != null &&
                    browsePanelBounds != null
            if (destinationVisible) {
                val previousTop = dailyCashScrollAnchorTop
                if (previousTop != null &&
                    abs(browsePanelBounds.top - previousTop) <= DAILY_CASH_ANCHOR_STABLE_TOLERANCE_PX
                ) {
                    dailyCashDestinationHits++
                } else {
                    dailyCashDestinationHits = 1
                }
                dailyCashScrollAnchorTop = browsePanelBounds.top
                if (dailyCashDestinationHits >= DAILY_CASH_DESTINATION_CONFIRMATIONS) {
                    dailyCashNoteState = DailyCashNoteState.WAITING_FOR_SCROLL
                    logProgress(
                        "$DAILY_CASH_DESTINATION_MARKER and #$DAILY_CASH_BROWSE_PANEL_ID are stable; " +
                                "scrolling to expose the note waterfall"
                    )
                    if (!scrollTaskList(down = true)) {
                        failDailyCashNoteTask("the note-list scroll gesture was rejected")
                        return
                    }
                    mainHandler.postDelayed(
                        { awaitDailyCashScroll(taskToken) },
                        DAILY_CASH_SCROLL_SETTLE_MS
                    )
                    return
                }
            } else {
                dailyCashDestinationHits = 0
                dailyCashScrollAnchorTop = null
            }
        }

        if (now >= dailyCashNoteDeadlineMs) {
            root?.let {
                dumpWindowForDiagnostics(it, "daily cash destination did not become ready", force = true)
            }
            failDailyCashNoteTask(
                if (root == null) "the daily-cash destination was not readable"
                else "$DAILY_CASH_DESTINATION_MARKER did not become stable"
            )
            return
        }
        postDailyCashPoll(taskToken) { awaitDailyCashDestination(taskToken) }
    }

    /** Verifies that the page actually moved before any card geometry is considered. */
    private fun awaitDailyCashScroll(taskToken: Long) {
        if (taskToken != dailyCashTaskToken || manualInterruptionDetected || !runActive ||
            dailyCashNoteState != DailyCashNoteState.WAITING_FOR_SCROLL
        ) return

        val now = SystemClock.uptimeMillis()
        val root = targetAppRoot()
        if (foregroundPackage() == targetPackageName && root != null) {
            val texts = collectTextNodes(root)
            val currentAnchorTop = findBoundsByViewId(root, DAILY_CASH_BROWSE_PANEL_ID)?.top
            val oldAnchorTop = dailyCashScrollAnchorTop
            val anchorMoved = oldAnchorTop != null &&
                    (currentAnchorTop == null ||
                            currentAnchorTop <= oldAnchorTop -
                            resources.displayMetrics.heightPixels * DAILY_CASH_MIN_SCROLL_FRACTION)
            if (!isOnTaskPage(texts) &&
                texts.any { it.text.trim() == DAILY_CASH_DESTINATION_MARKER } && anchorMoved
            ) {
                dailyCashNoteState = DailyCashNoteState.FINDING_CARD
                logProgress("Daily-cash welfare panel moved upward; validating the note-card grid")
                mainHandler.postDelayed(
                    { findAndOpenDailyCashCard(taskToken) },
                    DAILY_CASH_CARD_SETTLE_MS
                )
                return
            }
        }

        if (now >= dailyCashNoteDeadlineMs) {
            root?.let {
                dumpWindowForDiagnostics(it, "daily cash page did not scroll", force = true)
            }
            failDailyCashNoteTask("the daily-cash page did not visibly move after scrolling")
            return
        }
        postDailyCashPoll(taskToken) { awaitDailyCashScroll(taskToken) }
    }

    private data class DailyCashCardCandidate(
        val node: AccessibilityNodeInfo,
        val bounds: Rect,
        val summary: String,
    )

    /**
     * Opens only a proven card from the second visible two-column row. The first complete row is the
     * two cards the task explicitly says to skip. No coordinate fallback is used: an inconclusive
     * hierarchy is dumped so it can be calibrated from real node data instead of guessing.
     */
    private fun findAndOpenDailyCashCard(taskToken: Long) {
        if (taskToken != dailyCashTaskToken || manualInterruptionDetected || !runActive ||
            dailyCashNoteState != DailyCashNoteState.FINDING_CARD
        ) return
        val root = targetAppRoot()
        if (root == null || foregroundPackage() != targetPackageName) {
            if (SystemClock.uptimeMillis() >= dailyCashNoteDeadlineMs) {
                failDailyCashNoteTask("the daily-cash card grid was not readable")
            } else {
                postDailyCashPoll(taskToken) { findAndOpenDailyCashCard(taskToken) }
            }
            return
        }

        val rows = findDailyCashCardRows(root)
        if (rows.size < DAILY_CASH_REQUIRED_CARD_ROWS) {
            if (!dailyCashDiagnosticsDumped) {
                dailyCashDiagnosticsDumped = true
                dumpWindowForDiagnostics(
                    root,
                    "daily cash card grid inconclusive after scrolling: found ${rows.size} complete row(s)",
                    force = true
                )
            }
            failDailyCashNoteTask(
                "could not prove two complete clickable card rows; node dump captured for calibration"
            )
            return
        }

        val selected = rows[1].first()
        dailyCashNavigationSignature = emptySet()
        dailyCashNavigationHits = 0
        dailyCashNoteState = DailyCashNoteState.VERIFYING_NOTE
        if (!performClick(ClickTarget(selected.node, selected.bounds, "second-row daily-cash note card"))) {
            failDailyCashNoteTask("the verified later note card would not click")
            return
        }
        recordAction(
            "Clicked a later daily-cash note card ${selected.bounds.toShortString()} " +
                    "(${selected.summary.ifEmpty { "no exposed label" }})"
        )
        mainHandler.postDelayed(
            { verifyDailyCashNoteOpened(taskToken) },
            DAILY_CASH_NAVIGATION_SETTLE_MS
        )
    }

    /** Returns complete left/right card rows, sorted top-to-bottom, after strict geometry filtering. */
    private fun findDailyCashCardRows(root: AccessibilityNodeInfo): List<List<DailyCashCardCandidate>> {
        val width = resources.displayMetrics.widthPixels
        val height = resources.displayMetrics.heightPixels
        val screen = Rect(0, 0, width, height)
        val waterfallBounds = DAILY_CASH_WATERFALL_IDS
            .firstNotNullOfOrNull { id -> findBoundsByViewId(root, id) }
        val noteGridTop = waterfallBounds?.top ?: collectTextNodes(root)
            .filter { it.text.contains(DAILY_CASH_NOTE_GRID_ANCHOR) }
            .maxOfOrNull { it.bounds.bottom }
            ?: return emptyList()
        val raw = collectClickableInWindow(root).mapNotNull { (node, originalBounds) ->
            val bounds = Rect(originalBounds)
            if (bounds.isEmpty() || !bounds.intersect(screen) ||
                bounds.top < noteGridTop - DAILY_CASH_GRID_TOP_TOLERANCE_PX
            ) return@mapNotNull null
            val widthFraction = bounds.width().toFloat() / width
            val heightFraction = bounds.height().toFloat() / height
            if (widthFraction !in DAILY_CASH_CARD_MIN_WIDTH_FRACTION..DAILY_CASH_CARD_MAX_WIDTH_FRACTION ||
                heightFraction !in DAILY_CASH_CARD_MIN_HEIGHT_FRACTION..DAILY_CASH_CARD_MAX_HEIGHT_FRACTION ||
                bounds.centerY() < height * DAILY_CASH_CARD_MIN_CENTER_Y_FRACTION ||
                abs(bounds.centerX() - width / 2) < width * DAILY_CASH_CARD_CENTER_GUTTER_FRACTION
            ) return@mapNotNull null
            val summary = collectTexts(node, maxDepth = 4)
                .map { it.trim() }
                .filter { it.isNotEmpty() }
                .distinct()
                .take(3)
                .joinToString(" / ")
            if (DAILY_CASH_REJECTED_CARD_TEXTS.any { summary.contains(it) }) return@mapNotNull null
            DailyCashCardCandidate(node, bounds, summary.take(120))
        }.sortedByDescending { it.bounds.width() * it.bounds.height() }

        val deduplicated = mutableListOf<DailyCashCardCandidate>()
        for (candidate in raw) {
            val duplicate = deduplicated.any { kept ->
                val overlap = Rect(candidate.bounds)
                if (!overlap.intersect(kept.bounds)) false else {
                    val overlapArea = overlap.width().toLong() * overlap.height().toLong()
                    val smallerArea = minOf(
                        candidate.bounds.width().toLong() * candidate.bounds.height().toLong(),
                        kept.bounds.width().toLong() * kept.bounds.height().toLong()
                    )
                    smallerArea > 0 && overlapArea.toDouble() / smallerArea >=
                            DAILY_CASH_CARD_DUPLICATE_OVERLAP
                }
            }
            if (!duplicate) deduplicated.add(candidate)
        }

        val left = deduplicated.filter { it.bounds.centerX() < width / 2 }.sortedBy { it.bounds.top }
        val right = deduplicated.filter { it.bounds.centerX() > width / 2 }.sortedBy { it.bounds.top }
        val rows = mutableListOf<List<DailyCashCardCandidate>>()
        val usedRight = mutableSetOf<Int>()
        for (leftCard in left) {
            val match = right.withIndex()
                .filter { it.index !in usedRight }
                .filter {
                    abs(it.value.bounds.top - leftCard.bounds.top) <=
                            height * DAILY_CASH_CARD_ROW_TOP_TOLERANCE_FRACTION
                }
                .filter {
                    val smaller = minOf(it.value.bounds.width(), leftCard.bounds.width()).coerceAtLeast(1)
                    val larger = maxOf(it.value.bounds.width(), leftCard.bounds.width())
                    larger.toDouble() / smaller <= DAILY_CASH_CARD_MAX_WIDTH_RATIO
                }
                .minByOrNull { abs(it.value.bounds.top - leftCard.bounds.top) }
                ?: continue
            usedRight.add(match.index)
            rows.add(listOf(leftCard, match.value))
        }
        return rows.sortedBy { row -> row.minOf { it.bounds.top } }
    }

    /** Requires stable, positive note-detail evidence before starting the dwell timer. */
    private fun verifyDailyCashNoteOpened(taskToken: Long) {
        if (taskToken != dailyCashTaskToken || manualInterruptionDetected || !runActive ||
            dailyCashNoteState != DailyCashNoteState.VERIFYING_NOTE
        ) return
        val now = SystemClock.uptimeMillis()
        val root = targetAppRoot()
        val texts = root?.let { collectTextNodes(it) }
        val contentSignature = texts?.let { dailyCashNoteContentSignature(it) }.orEmpty()
        val sourceMarkerVisible = texts?.any {
            it.text.trim() == DAILY_CASH_DESTINATION_MARKER ||
                    it.text.contains(DAILY_CASH_NOTE_GRID_ANCHOR)
        } == true
        val errorOrLoadingVisible = texts?.any { node ->
            DAILY_CASH_NON_CONTENT_MARKERS.any { node.text.contains(it, ignoreCase = true) }
        } == true
        val hasBackControl = root?.let { hasDailyCashNoteBackControl(it) } == true
        val candidateDetail = foregroundPackage() == targetPackageName && texts != null &&
                !isOnTaskPage(texts) && !sourceMarkerVisible && !errorOrLoadingVisible &&
                hasBackControl && contentSignature.size >= DAILY_CASH_MIN_NOTE_CONTENT_NODES
        if (candidateDetail) {
            if (contentSignature == dailyCashNavigationSignature) {
                dailyCashNavigationHits++
            } else {
                dailyCashNavigationSignature = contentSignature
                dailyCashNavigationHits = 1
            }
        } else {
            dailyCashNavigationSignature = emptySet()
            dailyCashNavigationHits = 0
        }
        if (dailyCashNavigationHits >= DAILY_CASH_NAVIGATION_CONFIRMATIONS) {
            val dwellSeconds = dailyCashDwellSeconds
            val title = currentTaskTitle
            dailyCashNoteState = DailyCashNoteState.DWELLING
            dailyCashNoteDeadlineMs = 0L
            logProgress("Stable note detail verified; staying ${dwellSeconds}s for '$title'")
            noteProgress(dwellSeconds * 1000L)
            mainHandler.postDelayed(
                {
                    if (taskToken == dailyCashTaskToken && runActive &&
                        !manualInterruptionDetected && currentTaskTitle == title &&
                        dailyCashNoteState == DailyCashNoteState.DWELLING
                    ) {
                        dailyCashNoteState = DailyCashNoteState.RETURNING
                        leaveTaskApp()
                    }
                },
                dwellSeconds * 1000L
            )
            return
        }

        if (now >= dailyCashNoteDeadlineMs) {
            root?.let {
                dumpWindowForDiagnostics(it, "daily cash card did not open stable note content", force = true)
            }
            failDailyCashNoteTask("the selected card did not open a stable, readable note page")
            return
        }
        postDailyCashPoll(taskToken) { verifyDailyCashNoteOpened(taskToken) }
    }

    /** Text identity only: coordinates and volatile short counters do not destabilize this proof. */
    private fun dailyCashNoteContentSignature(texts: List<TextNode>): Set<String> =
        texts.asSequence()
            .map { it.text.trim() }
            .filter { it.length >= DAILY_CASH_MIN_NOTE_TEXT_LENGTH }
            .filter { value -> DAILY_CASH_NOTE_CHROME_TEXTS.none { value.contains(it) } }
            .take(DAILY_CASH_MAX_NOTE_SIGNATURE_NODES)
            .toSet()

    private fun hasDailyCashNoteBackControl(root: AccessibilityNodeInfo): Boolean {
        val width = resources.displayMetrics.widthPixels
        val height = resources.displayMetrics.heightPixels
        return collectClickableInWindow(root).any { (node, bounds) ->
            if (bounds.isEmpty() || bounds.centerX() > width * DAILY_CASH_BACK_MAX_X_FRACTION ||
                bounds.centerY() > height * DAILY_CASH_BACK_MAX_Y_FRACTION ||
                bounds.width() > width * DAILY_CASH_BACK_MAX_WIDTH_FRACTION ||
                bounds.height() > height * DAILY_CASH_BACK_MAX_HEIGHT_FRACTION
            ) return@any false
            val labels = collectTexts(node, maxDepth = 2)
            labels.isEmpty() || labels.any { label ->
                DAILY_CASH_BACK_LABELS.any { label.contains(it, ignoreCase = true) }
            }
        }
    }

    private fun postDailyCashPoll(taskToken: Long, action: () -> Unit) {
        if (taskToken != dailyCashTaskToken) return
        val remaining = (dailyCashNoteDeadlineMs - SystemClock.uptimeMillis()).coerceAtLeast(0L)
        mainHandler.postDelayed(
            action,
            minOf(randomDelay(DAILY_CASH_POLL_MIN_MS, DAILY_CASH_POLL_MAX_MS), remaining)
        )
    }

    private fun failDailyCashNoteTask(reason: String) {
        if (dailyCashNoteState == DailyCashNoteState.IDLE ||
            dailyCashNoteState == DailyCashNoteState.RETURNING
        ) return
        logProgress("Daily-cash note task failed: $reason; returning to $TASK_PAGE_TITLE")
        capturingTaskApps = false
        taskApps.clear()
        externalTaskCandidate = null
        externalTaskCandidateHits = 0
        confirmedExternalTaskApp = null
        failCurrentTaskWithScreenshot(reason) { returnToTaskPage() }
    }

    /**
     * Accepts the "即将离开携程旅行打开…" confirmation if it appears. Not every task shows one, so a
     * miss just falls through to waiting for the other app.
     */
    private fun confirmLeaveApp(dwellSeconds: Int, attempt: Int = 1) {
        if (manualInterruptionDetected) return
        if (foregroundPackage() != targetPackageName) {
            // Already switched away, no confirmation was needed.
            waitForExternalApp(dwellSeconds)
            return
        }
        val confirm = currentRoots()
            .asSequence()
            .flatMap { collectTextNodes(it).asSequence() }
            .firstOrNull { node -> CONFIRM_LEAVE_TEXTS.any { node.text.trim() == it } }
        if (confirm != null) {
            val target = clickableSelfOrAncestor(confirm.node, maxDepth = 4)
            val clicked =
                if (target != null) tryPerformClick(target) else tryClickRect(confirm.bounds)
            if (clicked) {
                recordAction("Confirmed leaving the app ('${confirm.text}')")
                mainHandler.postDelayed({ waitForExternalApp(dwellSeconds) }, randomDelay(700, 1200))
                return
            }
        }
        if (attempt < CONFIRM_LEAVE_ATTEMPTS) {
            mainHandler.postDelayed({ confirmLeaveApp(dwellSeconds, attempt + 1) }, randomDelay(500, 900))
            return
        }
        logProgress("No leave-app confirmation appeared")
        waitForExternalApp(dwellSeconds)
    }

    private data class BrowserAppHandoffPrompt(
        val sourcePackage: String,
        val positive: TextNode,
        val negative: TextNode,
    )

    /** Finds only a website-originated app-open prompt with both reject and allow actions. */
    private fun findBrowserAppHandoffPrompt(sourcePackage: String): BrowserAppHandoffPrompt? {
        if (!expectingExternalApp || !capturingTaskApps || currentTaskTitle == null) return null
        if (!isPotentialTaskApp(sourcePackage)) return null
        for (root in currentRoots()) {
            if (root.packageName?.toString() != sourcePackage) continue
            val texts = collectTextNodes(root)
            val hasWebsiteRequest = texts.any {
                BROWSER_APP_HANDOFF_REQUEST_RE.containsMatchIn(it.text)
            }
            if (!hasWebsiteRequest) continue
            val negative = texts.firstOrNull {
                it.text.trim() in BROWSER_APP_HANDOFF_NEGATIVE_TEXTS
            } ?: continue
            val positive = texts.firstOrNull {
                it.text.trim() in BROWSER_APP_HANDOFF_POSITIVE_TEXTS
            } ?: continue
            return BrowserAppHandoffPrompt(sourcePackage, positive, negative)
        }
        return null
    }

    /** Clicks only the positive half of a strongly recognised browser handoff dialog. */
    private fun clickBrowserAppHandoffPrompt(prompt: BrowserAppHandoffPrompt): Boolean {
        val clickable = clickableSelfOrAncestor(prompt.positive.node, maxDepth = 4)
        if (clickable != null) {
            val bounds = Rect().also { runCatching { clickable.getBoundsInScreen(it) } }
            // Reject a common ancestor containing both buttons; tap the positive label itself instead.
            if (!bounds.isEmpty() && !Rect.intersects(bounds, prompt.negative.bounds)) {
                if (tryPerformClick(clickable)) return true
            }
        }
        return tryClickRect(prompt.positive.bounds)
    }

    private fun beginBrowserAppHandoff(
        prompt: BrowserAppHandoffPrompt,
        dwellSeconds: Int,
    ): Boolean {
        noteTaskApp(prompt.sourcePackage)
        if (!clickBrowserAppHandoffPrompt(prompt)) return false

        externalHandoffSourcePackage = prompt.sourcePackage
        externalHandoffDeadlineMs = SystemClock.uptimeMillis() + EXTERNAL_HANDOFF_TIMEOUT_MS
        externalHandoffClickAtMs = SystemClock.uptimeMillis()
        externalHandoffTargetCandidate = null
        externalHandoffTargetHits = 0
        externalTaskCandidate = null
        externalTaskCandidateHits = 0
        externalTaskCandidateSinceMs = 0L
        confirmedExternalTaskApp = null
        recordAction(
            "Accepted website request in ${prompt.sourcePackage} to open its target app " +
                    "('${prompt.positive.text}')"
        )
        noteProgress(EXTERNAL_HANDOFF_TIMEOUT_MS)
        mainHandler.postDelayed(
            { waitForBrowserHandoffTarget(dwellSeconds) },
            randomDelay(EXTERNAL_HANDOFF_POLL_MIN_MS, EXTERNAL_HANDOFF_POLL_MAX_MS)
        )
        return true
    }

    /** Waits until a stable package different from the browser becomes the final task destination. */
    private fun waitForBrowserHandoffTarget(dwellSeconds: Int) {
        val source = externalHandoffSourcePackage ?: return
        if (manualInterruptionDetected || !runActive || currentTaskTitle == null) return

        val now = SystemClock.uptimeMillis()
        val current = foregroundPackage()
        when {
            current == source -> {
                externalHandoffTargetCandidate = null
                externalHandoffTargetHits = 0
                // Some browsers keep the prompt visible after a dropped tap. Retry only the same
                // strongly recognised prompt, with a cooldown preventing event-burst double clicks.
                if (now - externalHandoffClickAtMs >= EXTERNAL_HANDOFF_CLICK_COOLDOWN_MS) {
                    val prompt = findBrowserAppHandoffPrompt(source)
                    if (prompt != null && clickBrowserAppHandoffPrompt(prompt)) {
                        externalHandoffClickAtMs = now
                        recordAction("Retried browser-to-app allow button in $source")
                    }
                }
            }
            current != null && current != source && isPotentialTaskApp(current) -> {
                if (externalHandoffTargetCandidate == current) {
                    externalHandoffTargetHits++
                } else {
                    externalHandoffTargetCandidate = current
                    externalHandoffTargetHits = 1
                }
                if (externalHandoffTargetHits >= EXTERNAL_APP_CONFIRMATIONS) {
                    noteTaskApp(current)
                    logProgress("Browser handoff reached confirmed target app $current")
                    startExternalAppDwell(current, dwellSeconds)
                    return
                }
            }
            else -> {
                externalHandoffTargetCandidate = null
                externalHandoffTargetHits = 0
            }
        }

        if (now >= externalHandoffDeadlineMs) {
            appRoot()?.let {
                dumpWindowForDiagnostics(it, "browser handoff did not open target app", force = true)
            }
            failBrowserAppHandoff(
                "browser accepted the app-open request but no target app appeared within " +
                        "${EXTERNAL_HANDOFF_TIMEOUT_MS / 1000}s",
                source
            )
            return
        }
        val remaining = (externalHandoffDeadlineMs - now).coerceAtLeast(0L)
        mainHandler.postDelayed(
            { waitForBrowserHandoffTarget(dwellSeconds) },
            minOf(
                randomDelay(EXTERNAL_HANDOFF_POLL_MIN_MS, EXTERNAL_HANDOFF_POLL_MAX_MS),
                remaining
            )
        )
    }

    private fun failBrowserAppHandoff(reason: String, recoveryPackage: String) {
        logProgress("Browser-to-app handoff failed: $reason")
        failCurrentTaskWithScreenshot(reason) {
            capturingTaskApps = false
            confirmedExternalTaskApp = recoveryPackage
            recoverConfirmedExternalWithBack()
        }
    }

    /** Starts the generic watcher immediately after a registry-supported task button is clicked. */
    private fun beginMiniProgramWatch(spec: MiniProgramTaskSpec) {
        resetMiniProgramSession()
        activeMiniProgramSpec = spec
        val token = miniProgramWatchToken
        logProgress(
            "Mini-program '${spec.id}' watcher started; waiting " +
                    "${MINI_PROGRAM_SETTLE_MS / 1000}s for the page to load"
        )
        noteProgress(
            MINI_PROGRAM_SETTLE_MS +
                    MINI_PROGRAM_MAX_ATTEMPTS * MINI_PROGRAM_POLL_MS
        )
        mainHandler.postDelayed(
            { pollMiniProgramPage(token, attempt = 1) },
            MINI_PROGRAM_SETTLE_MS,
        )
    }

    private fun pollMiniProgramPage(token: Long, attempt: Int) {
        val spec = activeMiniProgramSpec ?: return
        if (token != miniProgramWatchToken || miniProgramWatchFinished ||
            !runActive || manualInterruptionDetected ||
            !spec.taskTitle.matches(currentTaskTitle?.trim().orEmpty())
        ) return

        val roots = currentRoots()
        val observedPackage = miniProgramObservedPackage
        val externalRoot = roots.firstOrNull {
            it.packageName?.toString() in spec.expectedPackages
        } ?: observedPackage?.let { expected ->
            roots.firstOrNull { it.packageName?.toString() == expected }
        }

        if (externalRoot != null) {
            val capturedPackage = externalRoot.packageName?.toString().orEmpty()
            dumpWindowForDiagnostics(
                externalRoot,
                "Mini-program '${spec.id}' page for '${currentTaskTitle.orEmpty()}'",
                force = true,
            )
            miniProgramDumpCaptured = true
            miniProgramWatchFinished = true
            logProgress("Mini-program '${spec.id}' node dump captured from $capturedPackage")
            if (clickMiniProgramCta(spec, externalRoot)) {
                onMiniProgramCtaTapped(token, spec)
            } else {
                logProgress("Could not dispatch mini-program CTA ${spec.ctaDescription}")
            }
            return
        }

        // Some WeChat mini-programs expose package events but no readable root. Only after the
        // expected package is observed may the per-spec screenshot-calibrated fallback be used.
        if (observedPackage in spec.expectedPackages &&
            attempt >= MINI_PROGRAM_ROOTLESS_CLICK_ATTEMPT
        ) {
            miniProgramWatchFinished = true
            logProgress(
                "No readable $observedPackage root after $attempt attempts; " +
                        "using '${spec.id}' display-coordinate fallback"
            )
            if (clickMiniProgramCta(spec, root = null)) {
                onMiniProgramCtaTapped(token, spec)
            } else {
                logProgress("Could not dispatch the rootless ${spec.ctaDescription} tap")
            }
            return
        }

        if (attempt >= MINI_PROGRAM_MAX_ATTEMPTS) {
            miniProgramWatchFinished = true
            val visiblePackages = roots.mapNotNull { it.packageName?.toString() }.distinct()
            logProgress(
                "Mini-program '${spec.id}' page was not found after $attempt attempts; " +
                        "event package: ${observedPackage ?: "none"}, readable windows: " +
                        visiblePackages.ifEmpty { listOf("none") }.joinToString(", ")
            )
            return
        }

        if (attempt == 1 || attempt % MINI_PROGRAM_STATUS_EVERY_ATTEMPTS == 0) {
            val visiblePackages = roots.mapNotNull { it.packageName?.toString() }.distinct()
            logProgress(
                "Waiting for '${spec.id}' mini-program page ($attempt/$MINI_PROGRAM_MAX_ATTEMPTS); " +
                        "event package: ${observedPackage ?: "none"}, windows: " +
                        visiblePackages.ifEmpty { listOf("none") }.joinToString(", ")
            )
        }
        mainHandler.postDelayed(
            { pollMiniProgramPage(token, attempt + 1) },
            MINI_PROGRAM_POLL_MS,
        )
    }

    private fun normalizedBounds(space: Rect, normalized: NormalizedRect): Rect = Rect(
        space.left + (space.width() * normalized.left).toInt(),
        space.top + (space.height() * normalized.top).toInt(),
        space.left + (space.width() * normalized.right).toInt(),
        space.top + (space.height() * normalized.bottom).toInt(),
    )

    /** Clicks a registry-defined mini-program CTA by semantics, then its calibrated safe center. */
    private fun clickMiniProgramCta(
        spec: MiniProgramTaskSpec,
        root: AccessibilityNodeInfo?,
    ): Boolean {
        val textTarget = root?.let { readableRoot ->
            collectTextNodes(readableRoot).firstOrNull {
                spec.ctaText.matches(it.text.trim())
            }
        }
        if (textTarget != null && performClick(
                ClickTarget(
                    textTarget.node,
                    textTarget.bounds,
                    "CTA text '${textTarget.text.trim()}' for '${spec.id}'",
                )
            )
        ) {
            recordAction("Clicked '${textTarget.text.trim()}' by accessibility text")
            return true
        }

        val rootBounds = root?.let { readableRoot ->
            Rect().also { runCatching { readableRoot.getBoundsInScreen(it) } }
        }
        val coordinateSpace = rootBounds?.takeUnless { it.isEmpty } ?: Rect(
            0,
            0,
            resources.displayMetrics.widthPixels,
            resources.displayMetrics.heightPixels,
        )
        if (coordinateSpace.isEmpty) {
            logProgress("Display bounds were empty; '${spec.id}' CTA fallback unavailable")
            return false
        }
        val fallbackBounds = normalizedBounds(coordinateSpace, spec.ctaFallback)
        val clicked = tryClickRect(fallbackBounds)
        if (clicked) {
            val source = if (rootBounds == null || rootBounds.isEmpty) "display" else "window"
            recordAction(
                "Tapped ${spec.ctaDescription} by $source-coordinate fallback " +
                        fallbackBounds.toShortString()
            )
        }
        return clicked
    }

    /** Starts an optional native confirmation watcher after the landing-page CTA was dispatched. */
    private fun onMiniProgramCtaTapped(token: Long, spec: MiniProgramTaskSpec) {
        if (token != miniProgramWatchToken || activeMiniProgramSpec != spec) return
        miniProgramCtaTapped = true
        miniProgramPromptObserved = false
        val prompt = spec.prompt
        if (prompt == null) {
            miniProgramPromptFinished = true
            logProgress("Mini-program '${spec.id}' CTA dispatched; no confirmation is configured")
            return
        }
        miniProgramPromptFinished = false
        logProgress("Watching for the optional '${spec.id}' mini-program confirmation")
        noteProgress(MINI_PROGRAM_PROMPT_MAX_ATTEMPTS * MINI_PROGRAM_PROMPT_POLL_MS)
        mainHandler.postDelayed(
            { pollMiniProgramPrompt(token, attempt = 1) },
            MINI_PROGRAM_PROMPT_POLL_MS,
        )
    }

    private fun pollMiniProgramPrompt(token: Long, attempt: Int) {
        val spec = activeMiniProgramSpec ?: return
        val prompt = spec.prompt ?: return
        if (token != miniProgramWatchToken || miniProgramPromptFinished ||
            !miniProgramCtaTapped || !runActive || manualInterruptionDetected ||
            !spec.taskTitle.matches(currentTaskTitle?.trim().orEmpty())
        ) return

        var promptRootFound = false
        var promptActions: Pair<TextNode, TextNode>? = null
        for (root in currentRoots()) {
            val rootPackage = root.packageName?.toString()
            if (rootPackage !in spec.expectedPackages && rootPackage != miniProgramObservedPackage) continue
            val texts = collectTextNodes(root)
            // A variable-length mini-program title can wrap and move the buttons. Require every
            // title marker plus the two exact sibling actions in one WeChat window, not a coordinate.
            val promptVisible = prompt.markers.all { marker ->
                texts.any { node -> node.text.contains(marker) }
            }
            if (!promptVisible) continue
            promptRootFound = true
            miniProgramPromptObserved = true
            val negative = texts.firstOrNull { it.text.trim() == "取消" } ?: continue
            val positive = texts.firstOrNull { it.text.trim() == prompt.positiveText } ?: continue
            promptActions = positive to negative
            break
        }

        val actions = promptActions
        if (actions != null && clickMiniProgramPromptPositive(actions.first, actions.second)) {
            miniProgramPromptFinished = true
            recordAction(
                "Clicked '${prompt.positiveText}' on the '${spec.id}' mini-program prompt " +
                        "at ${actions.first.bounds.toShortString()}"
            )
            return
        }

        if (attempt >= MINI_PROGRAM_PROMPT_MAX_ATTEMPTS) {
            miniProgramPromptFinished = true
            if (promptRootFound || miniProgramPromptObserved) {
                logProgress(
                    "Mini-program '${spec.id}' prompt was detected but did not expose safe " +
                            "取消 / ${prompt.positiveText} controls"
                )
            } else {
                logProgress("No optional mini-program prompt appeared for '${spec.id}'")
            }
            return
        }

        mainHandler.postDelayed(
            { pollMiniProgramPrompt(token, attempt + 1) },
            MINI_PROGRAM_PROMPT_POLL_MS,
        )
    }

    /** Clicks only the right-hand positive action of a fully recognised mini-program launch prompt. */
    private fun clickMiniProgramPromptPositive(
        positive: TextNode,
        negative: TextNode,
    ): Boolean {
        val sameButtonRow = positive.bounds.bottom >= negative.bounds.top &&
                negative.bounds.bottom >= positive.bounds.top
        if (positive.bounds.isEmpty || negative.bounds.isEmpty || !sameButtonRow ||
            positive.bounds.centerX() <= negative.bounds.centerX()
        ) {
            return false
        }
        val clickable = clickableSelfOrAncestor(positive.node, maxDepth = 4)
        if (clickable != null) {
            val clickableBounds = Rect().also { runCatching { clickable.getBoundsInScreen(it) } }
            // A shared dialog/button-row ancestor can include 取消. Do not execute its action.
            if (!clickableBounds.isEmpty && !Rect.intersects(clickableBounds, negative.bounds) &&
                tryPerformClick(clickable)
            ) {
                return true
            }
        }
        // This uses the actual 允许 bounds exposed by WeChat, so title wrapping cannot shift it.
        return tryClickRect(positive.bounds)
    }

    /** Starts the timed stay only after the final external package has been verified. */
    private fun startExternalAppDwell(packageName: String, dwellSeconds: Int) {
        confirmedExternalTaskApp = packageName
        noteTaskApp(packageName)
        externalTaskCandidate = null
        externalTaskCandidateHits = 0
        clearExternalHandoffState()
        logProgress("Now in confirmed task app $packageName, staying ${dwellSeconds}s")
        noteProgress(dwellSeconds * 1000L)
        val title = currentTaskTitle
        val miniProgramSpec = activeMiniProgramSpec
        if (miniProgramSpec != null && packageName in miniProgramSpec.expectedPackages) {
            miniProgramObservedPackage = packageName
        }
        mainHandler.postDelayed(
            {
                if (runActive && !manualInterruptionDetected && currentTaskTitle == title) {
                    leaveTaskApp()
                }
            },
            dwellSeconds * 1000L
        )
    }

    /** Waits for a stable external app, or treats the destination as an in-app page. */
    private fun waitForExternalApp(dwellSeconds: Int, attempt: Int = 1) {
        if (manualInterruptionDetected || !runActive || currentTaskTitle == null) return

        // System-owned overlays are filtered by isPotentialTaskApp. Inspect every readable root rather
        // than trusting foregroundPackage(): Android can rank Ctrip's still-readable background
        // WebView ahead of the external app that is visibly on top.
        val current = readableExternalTaskPackage() ?: foregroundPackage()
        if (current != null && isPotentialTaskApp(current)) {
            // The same-package/root dialog guard below is what makes this click safe.
            val prompt = findBrowserAppHandoffPrompt(current)
            if (prompt != null) {
                externalTaskCandidate = null
                externalTaskCandidateHits = 0
                if (beginBrowserAppHandoff(prompt, dwellSeconds)) return
                logProgress("Found browser app-open prompt in $current but could not press allow")
                val promptRetryWindowOpen = externalTaskCandidateSinceMs > 0L &&
                        SystemClock.uptimeMillis() - externalTaskCandidateSinceMs <
                        EXTERNAL_HANDOFF_PROMPT_GRACE_MS
                if (attempt >= EXTERNAL_APP_WAIT_ATTEMPTS && !promptRetryWindowOpen) {
                    externalTaskCandidateSinceMs = 0L
                    failBrowserAppHandoff("browser app-open allow button was not clickable", current)
                    return
                }
            } else {
                if (externalTaskCandidate == current) {
                    externalTaskCandidateHits++
                } else {
                    externalTaskCandidate = current
                    externalTaskCandidateHits = 1
                    externalTaskCandidateSinceMs = SystemClock.uptimeMillis()
                    logProgress(
                        "Watching $current for a delayed website-to-app request for up to " +
                                "${EXTERNAL_HANDOFF_PROMPT_GRACE_MS / 1000}s"
                    )
                    noteProgress(EXTERNAL_HANDOFF_PROMPT_GRACE_MS)
                }
                // Give a newly opened browser a short window to render a website→app prompt before
                // accepting that browser as the task's final destination.
                val graceElapsed = SystemClock.uptimeMillis() - externalTaskCandidateSinceMs >=
                        EXTERNAL_HANDOFF_PROMPT_GRACE_MS
                if (externalTaskCandidateHits >= EXTERNAL_APP_CONFIRMATIONS && graceElapsed) {
                    startExternalAppDwell(current, dwellSeconds)
                    return
                }
            }
        } else {
            externalTaskCandidate = null
            externalTaskCandidateHits = 0
            externalTaskCandidateSinceMs = 0L
        }

        val delayedPromptWindowOpen = externalTaskCandidateSinceMs > 0L &&
                SystemClock.uptimeMillis() - externalTaskCandidateSinceMs <
                EXTERNAL_HANDOFF_PROMPT_GRACE_MS
        if (attempt < EXTERNAL_APP_WAIT_ATTEMPTS || delayedPromptWindowOpen) {
            // EXTERNAL_APP_WAIT_ATTEMPTS remains the bound for in-app/uncertain destinations. A
            // stable external browser is the deliberate exception: keep scanning until its complete
            // prompt grace elapses, because loading and startup ads can outlast the old retry count.
            mainHandler.postDelayed(
                { waitForExternalApp(dwellSeconds, attempt + 1) },
                randomDelay(600, 1000)
            )
            return
        }
        // No ordinary external app remained visible long enough to be confirmed. Even if a transient
        // overlay hid Ctrip during one sample, the safe recovery is BACK-until-签到任务, not HOME/kill.
        confirmedExternalTaskApp = null
        logProgress("Task destination stayed inside Ctrip or was uncertain; waiting ${dwellSeconds}s")
        noteProgress(dwellSeconds * 1000L)
        val title = currentTaskTitle
        mainHandler.postDelayed(
            {
                if (runActive && !manualInterruptionDetected && currentTaskTitle == title) {
                    leaveTaskApp()
                }
            },
            dwellSeconds * 1000L
        )
    }

    /**
     * Whether a task is one we deliberately do not press: either a built-in case the automation cannot
     * carry through, or something matching the user's own skip list. The user's entries are checked
     * against the title as well as the button, so an entry can name an app rather than a button label.
     */
    private fun isIgnoredRow(row: TaskRow): Boolean {
        // This schema has a dedicated in-app interaction flow, so it must not be excluded by a broad
        // user skip entry such as 去完成 or 关注.
        if (isPlanetFollowTask(row) || isHotelRankingTask(row) || isDailyCashNoteTask(row)) return false
        // Registry-supported mini-program tasks own their CTA interaction, so they bypass the broad
        // 去微信 exclusion without weakening that safety rule for unknown WeChat destinations.
        if (miniProgramSpecFor(row) != null) return false
        // The whitelist wins: 浏览能量大富翁15s is worth doing even though its 去完成 button reads like
        // something to skip. Matched on the title and description, i.e. the text in the row's left
        // half, because that is what identifies the task rather than the button's wording.
        if (AutomationSettings.matchesWhitelist(row.title, row.description)) return false
        return IGNORED_BUTTON_TEXTS.any { row.buttonText.contains(it) } ||
                AutomationSettings.matchesSkip(row.buttonText, row.title)
    }

    private fun clearExternalHandoffState() {
        externalTaskCandidateSinceMs = 0L
        externalHandoffSourcePackage = null
        externalHandoffDeadlineMs = 0L
        externalHandoffClickAtMs = 0L
        externalHandoffTargetCandidate = null
        externalHandoffTargetHits = 0
    }

    /** Records a package a task took us into, so it can be closed afterwards. */
    private fun noteTaskApp(pkg: String) {
        if (!capturingTaskApps || !isPotentialTaskApp(pkg)) return
        if (taskApps.add(pkg)) logProgress("Task app: $pkg")
    }

    /**
     * Chooses an external task package from every currently readable accessibility root.
     *
     * Android may keep Ctrip's background WebView readable and rank it ahead of the visibly open
     * browser. Preserve the package already being sampled when its root still exists; otherwise use
     * the first non-Ctrip, non-system application root in window order.
     */
    private fun readableExternalTaskPackage(): String? {
        val packages = currentRoots()
            .mapNotNull { it.packageName?.toString() }
            .distinct()
            .filter { isPotentialTaskApp(it) }
        externalTaskCandidate?.takeIf { it in packages }?.let { return it }
        confirmedExternalTaskApp?.takeIf { it in packages }?.let { return it }
        lastObservedPackage?.takeIf { it in packages }?.let { return it }
        return packages.firstOrNull()
    }

    /**
     * Filters transient system windows out of destination tracking. They can cover Ctrip briefly but
     * must never be enough to trigger HOME/kill/Recents recovery.
     */
    private fun isPotentialTaskApp(pkg: String): Boolean {
        if (pkg == targetPackageName || pkg == packageName || pkg == launcherPackage) return false
        if (pkg in NON_TASK_DESTINATION_PACKAGES || pkg in CHOOSER_PACKAGES) return false
        return try {
            packageManager.getApplicationInfo(pkg, 0).uid >= Process.FIRST_APPLICATION_UID
        } catch (_: Exception) {
            false
        }
    }

    /**
     * Ends a task: leave the app via HOME, close it, then bring 携程 back.
     *
     * HOME rather than BACK because the system performs a global action itself instead of dispatching
     * it to the focused window, so an app cannot swallow it — unlike BACK, and unlike the edge swipes,
     * which arrive as ordinary touch input that feed and video screens routinely consume. Closing has
     * to happen after leaving, because only background processes can be killed.
     */
    private fun leaveTaskApp() {
        if (manualInterruptionDetected) return
        // Stop recording packages here: everything seen from now on is the launcher or our own app.
        capturingTaskApps = false

        val targetInFront = foregroundPackage() == targetPackageName && targetAppRoot() != null
        val externalApp = confirmedExternalTaskApp
        if (targetInFront || externalApp == null) {
            // Internal Ctrip pages use BACK. If an external package was observed but never confirmed
            // (common for opaque WeChat mini-program windows), preserve taskApps: once BACK reaches
            // 签到任务, returnToTaskPage() will dismiss only those recorded Recents cards.
            externalTaskCandidate = null
            externalTaskCandidateHits = 0
            confirmedExternalTaskApp = null
            logProgress(
                if (targetInFront) {
                    "Task is back in Ctrip, going back until $TASK_PAGE_TITLE"
                } else {
                    "No external task app was confirmed, using BACK until $TASK_PAGE_TITLE"
                }
            )
            returnToTaskPage()
            return
        }

        logProgress(
            "Task done in $externalApp; trying BACK before HOME because the activity may be " +
                    "inside Ctrip's task stack"
        )
        recoverConfirmedExternalWithBack()
    }

    /**
     * Unwinds an external activity that may have been launched into Ctrip's Android task. Recents
     * restores a whole task, so using HOME first can reopen the same external top activity forever.
     * Several BACK presses are tried and verified; the original HOME/kill/Recents ladder remains the
     * bounded fallback for a true external app that consumes BACK.
     */
    private fun recoverConfirmedExternalWithBack(
        attempt: Int = 1,
        externalCloseAttempted: Boolean = false,
    ) {
        if (manualInterruptionDetected) return

        val targetInFront = foregroundPackage() == targetPackageName && targetAppRoot() != null
        if (targetInFront) {
            logProgress("BACK recovery revealed $targetPackageName; continuing until $TASK_PAGE_TITLE")
            // returnToTaskPage owns completion; once the list is visible it closes recorded Recents
            // cards before allowing the next task to start.
            returnToTaskPage()
            return
        }

        if (!externalCloseAttempted && clickForegroundExternalCloseControl()) {
            mainHandler.postDelayed(
                { recoverConfirmedExternalWithBack(attempt, externalCloseAttempted = true) },
                randomDelay(900, 1400)
            )
            return
        }

        if (attempt <= MAX_EXTERNAL_BACK_PRESSES) {
            logProgress(
                "External activity still on top; BACK ($attempt/$MAX_EXTERNAL_BACK_PRESSES)"
            )
            try { performGlobalAction(GLOBAL_ACTION_BACK) } catch (_: Exception) {}
            mainHandler.postDelayed(
                { recoverConfirmedExternalWithBack(attempt + 1, externalCloseAttempted) },
                randomDelay(900, 1400)
            )
            return
        }

        val externalApp = confirmedExternalTaskApp ?: "external task app"
        logProgress(
            "BACK did not reveal Ctrip after $MAX_EXTERNAL_BACK_PRESSES attempts; " +
                    "falling back to HOME for $externalApp"
        )
        try { performGlobalAction(GLOBAL_ACTION_HOME) } catch (_: Exception) {}
        mainHandler.postDelayed({
            if (taskApps.any { isSafeToKill(it) }) {
                closeTaskAppsViaRecentsThenReturn()
            } else {
                bringBackTargetApp()
            }
        }, KILL_DELAY_MS)
    }

    /**
     * Best-effort fallback used only when Recents cannot be opened.
     *
     * Android 14+ restricts `killBackgroundProcesses` to the caller's own UID, so it cannot close
     * any external package tracked here. Older Android versions merely accept a background-kill
     * request; that is not proof that the app stopped and must never be logged as a verified close.
     */
    private fun killTaskApps() {
        val packages = taskApps.toList()
        taskApps.clear()
        externalTaskCandidate = null
        externalTaskCandidateHits = 0
        confirmedExternalTaskApp = null
        if (packages.isEmpty()) return

        val safePackages = packages.filter { isSafeToKill(it) }
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.UPSIDE_DOWN_CAKE) {
            safePackages.forEach { pkg ->
                logProgress(
                    "Could not close $pkg with a background-kill request: Android " +
                            "${Build.VERSION.SDK_INT} only permits killing this app's own processes"
                )
            }
            return
        }

        val am = getSystemService(Context.ACTIVITY_SERVICE) as? ActivityManager
        if (am == null) {
            safePackages.forEach { logProgress("Could not request background kill for $it") }
            return
        }
        for (pkg in safePackages) {
            try {
                am.killBackgroundProcesses(pkg)
                logProgress("Background kill requested for $pkg (closure not verified)")
            } catch (e: Exception) {
                logProgress("Could not request background kill for $pkg: ${e.message}")
            }
        }
    }

    /**
     * Whether [pkg] may be killed. Our own app, 携程, the launcher and the system UI are never
     * candidates — pressing HOME makes the launcher the foreground app, so it must never be mistaken
     * for something a task opened.
     */
    private fun isSafeToKill(pkg: String): Boolean {
        if (pkg == packageName || pkg == targetPackageName) return false
        if (pkg == launcherPackage || pkg == "com.android.systemui" || pkg == "android") {
            logProgress("Not closing $pkg (system shell)")
            return false
        }
        return try {
            val uid = packageManager.getApplicationInfo(pkg, 0).uid
            if (uid < Process.FIRST_APPLICATION_UID) {
                logProgress("Leaving $pkg running (system UID $uid cannot be killed)")
                false
            } else {
                true
            }
        } catch (_: Exception) {
            false
        }
    }

    private data class RecentsCardTarget(
        val packageName: String,
        val label: String,
        val node: AccessibilityNodeInfo,
        val bounds: Rect,
    )

    /**
     * Removes only this task's allowlisted external cards from Recents, then returns to Ctrip.
     * Dismissing a card is the strongest cross-app cleanup available to an ordinary accessibility
     * service on Android 14+, where killBackgroundProcesses cannot kill another package.
     */
    private fun closeTaskAppsViaRecentsThenReturn() {
        if (taskAppCleanupInProgress) return
        val packages = taskApps.filter { isSafeToKill(it) }.distinct()
        if (packages.isEmpty()) {
            taskApps.clear()
            if (foregroundPackage() == targetPackageName) returnToTaskPage() else bringBackTargetApp()
            return
        }

        capturingTaskApps = false
        taskAppCleanupInProgress = true
        val token = ++taskAppCleanupToken
        logProgress("Opening Recents to close automation-opened apps: ${packages.joinToString(", ")}")
        val opened = runCatching { performGlobalAction(GLOBAL_ACTION_RECENTS) }.getOrDefault(false)
        if (!opened) {
            logProgress("Could not open Recents; falling back to a best-effort background-kill request")
            taskAppCleanupInProgress = false
            killTaskApps()
            if (foregroundPackage() == targetPackageName) returnToTaskPage() else bringBackTargetApp()
            return
        }
        mainHandler.postDelayed(
            { dismissNextTaskAppCard(token, packages, index = 0, attempt = 1) },
            RECENTS_SETTLE_MS,
        )
    }

    private fun dismissNextTaskAppCard(
        token: Long,
        packages: List<String>,
        index: Int,
        attempt: Int,
    ) {
        if (token != taskAppCleanupToken || !taskAppCleanupInProgress) return
        if (index >= packages.size) {
            finishTaskAppCleanup(token, packages)
            return
        }

        val pkg = packages[index]
        val cards = findRecentsCards(pkg)
        when {
            cards.isEmpty() -> {
                logProgress("No Recents card for $pkg (already gone or not exposed)")
                dismissNextTaskAppCard(token, packages, index + 1, attempt = 1)
            }
            cards.size > 1 -> {
                logProgress("Leaving $pkg alone: ${cards.size} matching Recents cards are ambiguous")
                dismissNextTaskAppCard(token, packages, index + 1, attempt = 1)
            }
            else -> {
                val card = cards.single()
                if (!dismissRecentsCard(card)) {
                    logProgress("Could not dispatch dismissal for ${card.label} ($pkg)")
                    dismissNextTaskAppCard(token, packages, index + 1, attempt = 1)
                    return
                }
                logProgress(
                    "Dismiss requested for ${card.label} ($pkg), verifying " +
                            "($attempt/$RECENTS_DISMISS_ATTEMPTS)"
                )
                mainHandler.postDelayed(
                    {
                        if (token != taskAppCleanupToken || !taskAppCleanupInProgress) return@postDelayed
                        val remaining = findRecentsCards(pkg)
                        if (remaining.isEmpty()) {
                            closedApps.add(pkg)
                            logProgress("Dismissed ${card.label} ($pkg) from Recents")
                            dismissNextTaskAppCard(token, packages, index + 1, attempt = 1)
                        } else if (remaining.size == 1 && attempt < RECENTS_DISMISS_ATTEMPTS) {
                            dismissNextTaskAppCard(token, packages, index, attempt + 1)
                        } else {
                            logProgress("Could not verify removal of ${card.label} ($pkg) from Recents")
                            dismissNextTaskAppCard(token, packages, index + 1, attempt = 1)
                        }
                    },
                    RECENTS_DISMISS_VERIFY_MS,
                )
            }
        }
    }

    private fun findRecentsCards(pkg: String): List<RecentsCardTarget> {
        val appInfo = runCatching { packageManager.getApplicationInfo(pkg, 0) }.getOrNull()
            ?: return emptyList()
        val label = packageManager.getApplicationLabel(appInfo).toString().trim()
        if (label.isEmpty()) return emptyList()
        val recentsRoots = currentRoots().filter { root ->
            val rootPackage = root.packageName?.toString()
            rootPackage == launcherPackage || rootPackage == "com.android.systemui"
        }
        return recentsRoots
            .asSequence()
            .flatMap { collectTextNodes(it).asSequence() }
            .filter {
                it.text.trim().equals(label, ignoreCase = true) ||
                        it.text.contains(pkg, ignoreCase = true)
            }
            .mapNotNull { findRecentsCardAncestor(pkg, label, it.node) }
            .distinctBy { it.bounds.toShortString() }
            .toList()
    }

    private fun findRecentsCardAncestor(
        pkg: String,
        label: String,
        labelNode: AccessibilityNodeInfo,
    ): RecentsCardTarget? {
        val screenWidth = resources.displayMetrics.widthPixels.toFloat()
        val screenHeight = resources.displayMetrics.heightPixels.toFloat()
        var current: AccessibilityNodeInfo? = labelNode
        var sizedCandidate: RecentsCardTarget? = null
        repeat(RECENTS_CARD_ANCESTOR_DEPTH) {
            val node = current ?: return@repeat
            val bounds = Rect().also { runCatching { node.getBoundsInScreen(it) } }
            if (!bounds.isEmpty()) {
                val widthFraction = bounds.width() / screenWidth
                val heightFraction = bounds.height() / screenHeight
                val candidate = RecentsCardTarget(pkg, label, node, bounds)
                val hasDismiss = runCatching {
                    node.actionList.any { it.id == AccessibilityNodeInfo.ACTION_DISMISS }
                }.getOrDefault(false)
                if (hasDismiss) return candidate
                if (sizedCandidate == null &&
                    widthFraction in RECENTS_CARD_MIN_WIDTH_FRACTION..RECENTS_CARD_MAX_WIDTH_FRACTION &&
                    heightFraction in RECENTS_CARD_MIN_HEIGHT_FRACTION..RECENTS_CARD_MAX_HEIGHT_FRACTION
                ) {
                    sizedCandidate = candidate
                }
            }
            current = runCatching { node.parent }.getOrNull()
        }
        return sizedCandidate
    }

    private fun dismissRecentsCard(card: RecentsCardTarget): Boolean {
        var current: AccessibilityNodeInfo? = card.node
        repeat(RECENTS_CARD_ANCESTOR_DEPTH) {
            val node = current ?: return@repeat
            val supportsDismiss = runCatching {
                node.actionList.any { it.id == AccessibilityNodeInfo.ACTION_DISMISS }
            }.getOrDefault(false)
            if (supportsDismiss && runCatching {
                    node.performAction(AccessibilityNodeInfo.ACTION_DISMISS)
                }.getOrDefault(false)
            ) return true
            current = runCatching { node.parent }.getOrNull()
        }

        val visibleBounds = Rect(card.bounds)
        if (!visibleBounds.intersect(
                0,
                0,
                resources.displayMetrics.widthPixels,
                resources.displayMetrics.heightPixels,
            )
        ) return false
        val startX = visibleBounds.centerX().toFloat()
        val startY = visibleBounds.top + visibleBounds.height() * 0.70f
        val endY = (visibleBounds.top - visibleBounds.height() * 0.45f).coerceAtLeast(1f)
        if (endY >= startY) return false
        val path = Path().apply {
            moveTo(startX, startY)
            lineTo(startX, endY)
        }
        return runCatching {
            dispatchGesture(
                GestureDescription.Builder()
                    .addStroke(
                        GestureDescription.StrokeDescription(
                            path,
                            0,
                            RECENTS_CARD_DISMISS_DURATION_MS,
                        )
                    )
                    .build(),
                null,
                null,
            )
        }.getOrDefault(false)
    }

    private fun finishTaskAppCleanup(token: Long, packages: List<String>) {
        if (token != taskAppCleanupToken || !taskAppCleanupInProgress) return
        taskApps.removeAll(packages.toSet())
        // Discard any rejected/unsafe observations too; this task's cleanup boundary is now complete.
        taskApps.clear()
        taskAppCleanupInProgress = false
        logProgress("Recents cleanup finished; returning to $targetPackageName")
        returnToTargetFromRecentsAfterCleanup()
    }

    private fun returnToTargetFromRecentsAfterCleanup() {
        val label = targetLabel
        val targetCard = if (label == null) null else currentRoots()
            .asSequence()
            .filter { root ->
                val rootPackage = root.packageName?.toString()
                rootPackage == launcherPackage || rootPackage == "com.android.systemui"
            }
            .flatMap { collectTextNodes(it).asSequence() }
            .firstOrNull { it.text.contains(label, ignoreCase = true) }
        val clicked = targetCard?.let { card ->
            val clickable = clickableSelfOrAncestor(card.node, maxDepth = 7)
            if (clickable != null) tryPerformClick(clickable) else tryClickRect(card.bounds)
        } == true
        if (clicked) {
            logProgress("Tapped the '$label' card after Recents cleanup")
            mainHandler.postDelayed({ returnToTaskPage() }, randomDelay(1200, 1800))
            return
        }

        logProgress("Could not select '$label' after cleanup; returning via HOME/Recents recovery")
        runCatching { performGlobalAction(GLOBAL_ACTION_HOME) }
        mainHandler.postDelayed({ bringBackTargetApp() }, RECENTS_SETTLE_MS)
    }

    /**
     * Brings 携程 back to the front once the task app has been closed.
     *
     * Recents is tried before relaunching. After HOME we are on the launcher, so `startActivity` from
     * here is a *background* activity start, which Android blocks unless the app is exempt — on MIUI
     * that means the 后台弹出界面 permission. Tapping the app's card in Recents needs no such permission,
     * because it is all accessibility actions, and it resumes the existing task so the 签到任务 page
     * comes back exactly as it was instead of being reloaded.
     *
     * Back gestures are deliberately not part of this ladder: on the launcher there is nothing to go
     * back from, which is why the previous version burned three BACK presses and two edge swipes to no
     * effect before giving up.
     */
    private fun bringBackTargetApp(stage: Int = 1) {
        if (manualInterruptionDetected) return
        if (foregroundPackage() == targetPackageName) {
            logProgress("Back in $targetPackageName; verifying $TASK_PAGE_TITLE before completing the task")
            // A returned task can land on another internal Ctrip page. Let the verified Back loop own
            // completion so the task is never marked done before 签到任务 is actually visible.
            returnToTaskPage()
            return
        }
        when (stage) {
            in 1..RECENTS_ATTEMPTS -> {
                logProgress("Returning via Recents ($stage/$RECENTS_ATTEMPTS)")
                try { performGlobalAction(GLOBAL_ACTION_RECENTS) } catch (_: Exception) {}
                mainHandler.postDelayed({ tapTargetCardInRecents(stage) }, RECENTS_SETTLE_MS)
                return
            }
            RECENTS_ATTEMPTS + 1 -> {
                logProgress("Recents did not work, trying a relaunch")
                relaunchTargetApp()
                mainHandler.postDelayed({
                    // Relaunching can bring the dual-app picker back up.
                    handleAppChooserIfPresent()
                    mainHandler.postDelayed({ bringBackTargetApp(stage + 1) }, randomDelay(1200, 1800))
                }, randomDelay(1000, 1500))
                return
            }
            else -> {
                failCurrentTaskWithScreenshot("could not get back from the task app") {
                    finishTaskLoop(
                        "could not return to $targetPackageName — grant this app 后台弹出界面 " +
                                "(background pop-up) so it may bring the app forward",
                        allowClaimRescan = false
                    )
                }
                return
            }
        }
    }

    /** Taps the 携程 card in the Recents overview, then lets [bringBackTargetApp] re-check. */
    private fun tapTargetCardInRecents(stage: Int) {
        if (manualInterruptionDetected) return
        val label = targetLabel
        val card = if (label == null) null else currentRoots()
            .asSequence()
            .flatMap { collectTextNodes(it).asSequence() }
            .firstOrNull { it.text.contains(label) }

        if (card != null) {
            val clickable = clickableSelfOrAncestor(card.node, maxDepth = 6)
            val clicked =
                if (clickable != null) tryPerformClick(clickable) else tryClickRect(card.bounds)
            logProgress(
                if (clicked) "Tapped the '$label' card in Recents"
                else "Found the '$label' card but could not tap it"
            )
        } else {
            logProgress("No '$label' card in Recents")
        }
        mainHandler.postDelayed({ bringBackTargetApp(stage + 1) }, randomDelay(1200, 1800))
    }

    /**
     * Tries an exact close affordance in the actual foreground external app.
     *
     * This must not use [appRoot], which deliberately prefers Ctrip even when a modal from another
     * package is visibly on top. The package and root are sampled together and checked again before
     * clicking, so a stale callback cannot close something in Ctrip or a system window.
     */
    private fun clickForegroundExternalCloseControl(): Boolean {
        val externalPackage = readableExternalTaskPackage() ?: return false
        val externalRoot = currentRoots().firstOrNull {
            it.packageName?.toString() == externalPackage
        } ?: return false

        val candidate = collectTextNodes(externalRoot)
            .filter { it.text.trim() in EXTERNAL_CLOSE_LABELS }
            .sortedWith(
                compareByDescending<TextNode> { it.node.isClickable }
                    .thenBy { it.bounds.width() * it.bounds.height() }
            )
            .firstOrNull() ?: return false
        if (currentRoots().none { it.packageName?.toString() == externalPackage }) return false

        val clicked = if (candidate.node.isClickable) {
            tryPerformClick(candidate.node)
        } else {
            tryClickRect(candidate.bounds)
        }
        if (clicked) {
            recordAction(
                "Clicked external close '${candidate.text}' in $externalPackage " +
                        candidate.bounds.toShortString()
            )
        }
        return clicked
    }

    /**
     * Returns from a task destination to the verified 签到任务 page.
     * A foreground external modal gets one exact close attempt before the bounded BACK ladder.
     */
    private fun returnToTaskPage(stage: Int = 1, externalCloseAttempted: Boolean = false) {
        if (manualInterruptionDetected) return
        val targetRoot = targetAppRoot()
        if (foregroundPackage() == targetPackageName &&
            targetRoot != null &&
            isOnTaskPage(collectTextNodes(targetRoot))
        ) {
            if (!taskAppCleanupInProgress && taskApps.any { isSafeToKill(it) }) {
                logProgress(
                    "Back on $TASK_PAGE_TITLE; closing ${taskApps.size} automation-opened app card(s) " +
                            "before the next task"
                )
                closeTaskAppsViaRecentsThenReturn()
                return
            }
            val miniProgramSpec = activeMiniProgramSpec
            if (miniProgramSpec != null && !miniProgramCtaTapped) {
                val reason = "mini-program CTA ${miniProgramSpec.ctaDescription} was not dispatched"
                logProgress("Back on $TASK_PAGE_TITLE, but '$currentTaskTitle' failed: $reason")
                expectingExternalApp = false
                externalTaskCandidate = null
                externalTaskCandidateHits = 0
                confirmedExternalTaskApp = null
                markCurrentTaskDone(reason)
                mainHandler.postDelayed({ resumeTaskLoop() }, randomDelay(1000, 1600))
                return
            }
            expectingExternalApp = false
            externalTaskCandidate = null
            externalTaskCandidateHits = 0
            confirmedExternalTaskApp = null
            markCurrentTaskDone(TASK_OUTCOME_DONE)
            logProgress("Back on $TASK_PAGE_TITLE")
            mainHandler.postDelayed({ resumeTaskLoop() }, randomDelay(1000, 1600))
            return
        }

        // Some external task apps place a non-cancelable update/interstitial dialog over their page.
        // BACK and edge gestures are consumed by that window, but its accessibility tree exposes a
        // real close button. Try it once, then re-sample instead of immediately spending a BACK retry.
        if (!externalCloseAttempted && clickForegroundExternalCloseControl()) {
            mainHandler.postDelayed(
                { returnToTaskPage(stage, externalCloseAttempted = true) },
                randomDelay(900, 1400)
            )
            return
        }

        when {
            stage <= MAX_IN_APP_BACK_PRESSES -> {
                logProgress("Going back to $TASK_PAGE_TITLE: BACK ($stage/$MAX_IN_APP_BACK_PRESSES)")
                try { performGlobalAction(GLOBAL_ACTION_BACK) } catch (_: Exception) {}
            }
            stage == MAX_IN_APP_BACK_PRESSES + 1 -> {
                logProgress("Going back to $TASK_PAGE_TITLE: back gesture (left edge)")
                swipeBackFromEdge(fromLeft = true)
            }
            else -> {
                currentRoots().firstOrNull()?.let {
                    dumpWindowForDiagnostics(it, "could not get back to $TASK_PAGE_TITLE")
                }
                failCurrentTaskWithScreenshot("could not get back to $TASK_PAGE_TITLE") {
                    finishTaskLoop(
                        "could not get back to $TASK_PAGE_TITLE",
                        allowClaimRescan = false
                    )
                }
                return
            }
        }
        mainHandler.postDelayed(
            { returnToTaskPage(stage + 1, externalCloseAttempted) },
            randomDelay(900, 1400)
        )
    }

    private fun relaunchTargetApp() {
        val pkg = targetPackageName ?: return
        val launch = packageManager.getLaunchIntentForPackage(pkg) ?: return
        launch.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
        logProgress("Relaunching $pkg")
        try {
            startActivity(launch)
        } catch (e: Exception) {
            // A blocked background start usually fails silently rather than throwing, so this only
            // catches the loud cases — but when it does throw, the reason is worth having.
            logProgress("Relaunch threw: ${e.message}")
            Log.e(TAG, "relaunch failed", e)
        }
    }

    /**
     * The system-wide back gesture: a horizontal swipe starting on the very edge of the screen. Some
     * apps intercept GLOBAL_ACTION_BACK but still honour this, since it arrives as ordinary touch
     * input handled by the system's gesture navigation.
     */
    private fun swipeBackFromEdge(fromLeft: Boolean): Boolean {
        try {
            val w = resources.displayMetrics.widthPixels
            val h = resources.displayMetrics.heightPixels
            val startX = if (fromLeft) 1f else (w - 1).toFloat()
            val endX = if (fromLeft) w * 0.6f else w * 0.4f
            val path = Path().apply {
                moveTo(startX, h * 0.5f)
                lineTo(endX, h * 0.5f)
            }
            val stroke = GestureDescription.StrokeDescription(path, 0, EDGE_SWIPE_DURATION_MS)
            return dispatchGesture(GestureDescription.Builder().addStroke(stroke).build(), null, null)
        } catch (e: Exception) {
            Log.e(TAG, "edge swipe error", e)
        }
        return false
    }

    /**
     * Picks the flow back up after a task, carrying on from wherever the page happens to be. Finished
     * rows are remembered, so re-covering ground costs a scroll and nothing else.
     */
    private fun resumeTaskLoop() {
        if (manualInterruptionDetected) return
        val root = appRoot()
        if (root == null || !isOnTaskPage(collectTextNodes(root))) {
            // Resuming can land on a different page of the app; step back to the list first.
            logProgress("Not on $TASK_PAGE_TITLE after returning, stepping back")
            returnToTaskPage()
            return
        }
        taskScrolls = 0
        lastPageSignature = emptySet()
        processNextTask()
    }

    /** How long to stay in the other app, and why. */
    private data class DwellPlan(val seconds: Int, val statedSeconds: Int?, val capped: Boolean)

    /**
     * Works out how long to stay for a task.
     *
     * A stated duration is a *minimum* — "浏览30s以上", "浏览30s" and "浏览30秒" all mean at least 30
     * seconds — and the other app only starts counting once its own page has loaded, which is later
     * than our click. Matching the stated value exactly would therefore fall short, so it is padded
     * by [DWELL_SAFETY_MARGIN_SECONDS].
     */
    private fun planDwell(description: String, title: String): DwellPlan {
        // The description is where durations live; the title is only a fallback because digits there
        // are usually version numbers or reward amounts.
        val stated = statedSeconds(description) ?: statedSeconds(title)
            ?: return DwellPlan(DEFAULT_DWELL_SECONDS, null, false)
        val padded = stated + DWELL_SAFETY_MARGIN_SECONDS
        val seconds = padded.coerceIn(MIN_DWELL_SECONDS, MAX_DWELL_SECONDS)
        return DwellPlan(seconds, stated, seconds < padded)
    }

    /**
     * Largest duration stated in [text], in seconds. Handles 30s, 30S, 30秒, 30秒钟 and 1分钟.
     *
     * A bare 分 is deliberately not a unit: it would misread 积分 / 评分 / 分享 as minutes.
     */
    private fun statedSeconds(text: String): Int? =
        DURATION_RE.findAll(text)
            .mapNotNull { match ->
                val value = match.groupValues[1].toDoubleOrNull() ?: return@mapNotNull null
                val seconds = if (match.groupValues[2] == "分钟") value * 60 else value
                seconds.toInt().takeIf { it > 0 }
            }
            .maxOrNull()

    /**
     * Scrolls the task list by one controlled drag.
     *
     * ACTION_SCROLL_BACKWARD / _FORWARD used to be tried first, and that is what silently broke the
     * upward hunt for tasks: the action reports success while scrolling a *nested* container that is
     * already at its own end, so the outer page never moves — three attempts in a row logged an
     * identical screen and the run concluded it had reached the top. A dispatched gesture moves the
     * page the user is looking at, so that is all this does now.
     *
     * A slow stroke on purpose: this is a drag, not a fling, so it lands where it is told and cannot
     * coast past a screenful of tasks that were never examined.
     */
    private fun scrollTaskList(down: Boolean = true): Boolean =
        if (down) {
            swipeVertical(PAGE_DRAG_FAR_FRACTION, PAGE_DRAG_NEAR_FRACTION, PAGE_DRAG_DURATION_MS)
        } else {
            swipeVertical(PAGE_DRAG_NEAR_FRACTION, PAGE_DRAG_FAR_FRACTION, PAGE_DRAG_DURATION_MS)
        }

    /**
     * A vertical swipe. [durationMs] decides the character of it: a long stroke is a *drag* that stops
     * dead where the finger lifts, while a short one is a *fling* that keeps coasting afterwards. That
     * distinction is why reaching the end of a long page needs a fling.
     */
    private fun swipeVertical(
        fromFraction: Float,
        toFraction: Float,
        durationMs: Long = SWIPE_DURATION_MS,
    ): Boolean {
        try {
            val w = resources.displayMetrics.widthPixels
            val h = resources.displayMetrics.heightPixels
            val path = Path().apply {
                moveTo(w / 2f, h * fromFraction)
                lineTo(w / 2f, h * toFraction)
            }
            val stroke = GestureDescription.StrokeDescription(path, 0, durationMs)
            return dispatchGesture(GestureDescription.Builder().addStroke(stroke).build(), null, null)
        } catch (e: Exception) {
            Log.e(TAG, "swipe error", e)
        }
        return false
    }

    /**
     * Resolves the `积分` counter in the profile page's counters row.
     *
     * The row is 收藏 / 浏览历史 / 积分 / 优惠券, each a stacked value-over-label pair, with a
     * 价值￥xx badge above the 积分 value. Matching the label text alone is not enough: the label is a
     * small, non-clickable TextView, and the nearest clickable ancestor is often the card that spans
     * all four counters — tapping that lands on whichever counter the tap point happens to fall in.
     * So the cell is identified structurally (numeric value directly above the label, sibling
     * counters on the same row, 价值 badge above) and the tap is aimed at that cell only.
     */
    private fun findPointsCounterCell(root: AccessibilityNodeInfo): ClickTarget? {
        val texts = collectTextNodes(root)
        val labels = texts.filter { it.text == "积分" }

        if (labels.isEmpty()) {
            // Some builds render the value and label as a single node, e.g. "4,414积分".
            val combined = texts.firstOrNull { COMBINED_POINTS_RE.matches(it.text) }
            if (combined != null) {
                logProgress("积分 counter found as a combined label '${combined.text}'")
                return ClickTarget(null, combined.bounds, "combined counter label")
            }
            logProgress("No exact 积分 label on screen")
            return null
        }

        // Score each 积分 label by how much it looks like the counters row.
        var bestScore = -1
        var bestCell: Rect? = null
        var bestLabel: TextNode? = null
        for (label in labels) {
            val value = texts.firstOrNull { candidate ->
                NUMERIC_RE.matches(candidate.text) &&
                        candidate.bounds.bottom <= label.bounds.top &&
                        label.bounds.top - candidate.bounds.bottom <= COUNTER_VALUE_MAX_GAP_PX &&
                        abs(candidate.bounds.centerX() - label.bounds.centerX()) <=
                        maxOf(label.bounds.width(), candidate.bounds.width())
            } ?: continue

            val peers = texts.count { peer ->
                peer.text in COUNTER_PEER_LABELS &&
                        abs(peer.bounds.centerY() - label.bounds.centerY()) <= COUNTER_ROW_TOLERANCE_PX
            }
            val hasValueBadge = texts.any { badge ->
                badge.text.contains("价值") &&
                        badge.bounds.bottom <= value.bounds.top + COUNTER_ROW_TOLERANCE_PX &&
                        value.bounds.top - badge.bounds.bottom <= COUNTER_BADGE_MAX_GAP_PX &&
                        abs(badge.bounds.centerX() - value.bounds.centerX()) <=
                        maxOf(value.bounds.width(), badge.bounds.width()) * 2
            }
            // Require at least one corroborating signal so we never click a stray 积分 label that
            // merely happens to have a number above it.
            if (peers == 0 && !hasValueBadge) continue

            val score = peers * 2 + if (hasValueBadge) 3 else 0
            if (score > bestScore) {
                bestScore = score
                bestCell = Rect(label.bounds).apply { union(value.bounds) }
                bestLabel = label
            }
        }

        val cell = bestCell
        val label = bestLabel
        if (cell == null || label == null) {
            logProgress("Found ${labels.size} 积分 label(s) but none inside a counters row")
            return null
        }
        logProgress("积分 counter cell ${cell.toShortString()} (score $bestScore)")

        // Use a clickable ancestor only when it is about the size of one cell; a wider one is the
        // card holding every counter and would make the tap position decide which counter is hit.
        val clickable = clickableSelfOrAncestor(label.node, maxDepth = 6)
        if (clickable != null) {
            val b = Rect().also { runCatching { clickable.getBoundsInScreen(it) } }
            if (!b.isEmpty() && b.width() <= cell.width() * MAX_CELL_CONTAINER_WIDTH_RATIO) {
                return ClickTarget(clickable, b, "counter cell container")
            }
            logProgress("Clickable ancestor ${b.toShortString()} spans the whole row, tapping the cell instead")
        }
        return ClickTarget(null, cell, "counter cell area")
    }

    private data class TextNode(val node: AccessibilityNodeInfo, val bounds: Rect, val text: String)

    /**
     * Collects text/content-description nodes from the hierarchy.
     *
     * The default remains strictly visible-only for every existing finder and click path. Task-list
     * planning can opt into off-screen nodes because Ctrip exposes document-relative coordinates;
     * those nodes are used only with ACTION_SHOW_ON_SCREEN and are never clicked directly.
     */
    private fun collectTextNodes(
        root: AccessibilityNodeInfo,
        includeOffscreen: Boolean = false,
    ): List<TextNode> {
        val out = mutableListOf<TextNode>()
        val queue = ArrayDeque<AccessibilityNodeInfo>()
        queue.add(root)
        while (queue.isNotEmpty()) {
            val n = queue.removeFirst()
            try {
                val text = (n.text?.toString() ?: n.contentDescription?.toString())?.trim()
                if (!text.isNullOrEmpty()) {
                    val r = Rect().also { runCatching { n.getBoundsInScreen(it) } }
                    // Ctrip's WebView exposes the whole document, but clips an off-screen node's
                    // bottom edge to the viewport. Preserve those inverted rectangles for planning;
                    // only the default path is allowed to return nodes that can actually be clicked.
                    val hasDocumentPosition = r.right > r.left && r.top != r.bottom
                    if ((includeOffscreen && hasDocumentPosition) || isBoundsVisible(r)) {
                        out.add(TextNode(n, r, text))
                    }
                }
                for (i in 0 until n.childCount) n.getChild(i)?.let { queue.add(it) }
            } catch (_: Exception) {}
        }
        return out
    }

    private fun isBoundsVisible(bounds: Rect): Boolean =
        !bounds.isEmpty &&
                bounds.left < resources.displayMetrics.widthPixels && bounds.right > 0 &&
                bounds.top < resources.displayMetrics.heightPixels && bounds.bottom > 0

    /** Taps inside [r] when there is no clickable node to use. */
    private fun tryClickRect(r: Rect): Boolean {
        try {
            jitterBeforeClick()
            if (manualInterruptionDetected) return false
            val (x, y) = randomPointInRect(r)
            val path = Path().apply { moveTo(x, y) }
            val stroke = GestureDescription.StrokeDescription(path, 20, 60)
            return dispatchGesture(GestureDescription.Builder().addStroke(stroke).build(), null, null)
        } catch (e: Exception) {
            Log.e(TAG, "rect click error", e)
        }
        return false
    }

    /**
     * Resolves the node a [step] should click, honouring its exact/region/pick constraints.
     *
     * Matching is done in-process over [collectTextNodes] rather than through
     * `AccessibilityNodeInfo.findAccessibilityNodeInfosByText`. That API's substring search depends on
     * the target app's node provider implementing it, and a Compose hierarchy returns nothing for a
     * partial query — so a prefix target like `最高赚` (label: `最高赚121`) would never be found even
     * though the node is right there on screen.
     */
    private fun findStepTarget(root: AccessibilityNodeInfo, step: FlowStep): ClickTarget? {
        val bottomBarTop = resources.displayMetrics.heightPixels * BOTTOM_BAR_FRACTION
        val texts = collectTextNodes(root)
        // Earlier entries in `texts` take priority, so return at the first candidate that matched.
        for (candidate in step.texts) {
            val matches = texts
                .filter { node ->
                    val hit =
                        if (step.exact) node.text == candidate
                        else node.text.contains(candidate, ignoreCase = true)
                    hit && !(step.region == Region.BOTTOM_BAR && node.bounds.centerY() < bottomBarTop)
                }
                .distinctBy { it.bounds.toShortString() }
            val chosen = when (step.pick) {
                Pick.RIGHT_MOST -> matches.maxByOrNull { it.bounds.centerX() }
                Pick.TOP_MOST -> matches.minByOrNull { it.bounds.top }
            } ?: continue
            return ClickTarget(chosen.node, chosen.bounds, "text match '${chosen.text}'")
        }
        return null
    }

    private fun findAndClickCloseButton(): Boolean {
        val root = appRoot() ?: return false
        val closeTexts = listOf("关闭", "取消", "×", "✖", "关闭窗口", "关闭弹窗")
        for (t in closeTexts) {
            val n = findExactTextNode(root, t)
            if (n != null && tryPerformClick(n)) { recordAction("Clicked close: $t"); return true }
        }
        // search contentDesc or text for 'close' or '关闭'
        val queue = ArrayDeque<AccessibilityNodeInfo>()
        queue.add(root)
        while (queue.isNotEmpty()) {
            val n = queue.removeFirst()
            try {
                val cd = n.contentDescription?.toString() ?: ""
                val txt = n.text?.toString() ?: ""
                if (cd.contains("close", ignoreCase = true) || cd.contains("关闭") || txt == "×" || txt == "✖") {
                    if (tryPerformClick(n)) { recordAction("Clicked close via desc/text"); return true }
                }
                for (i in 0 until n.childCount) n.getChild(i)?.let { queue.add(it) }
            } catch (_: Exception) {}
        }
        return false
    }

    private fun tryPerformClick(node: AccessibilityNodeInfo): Boolean {
        try {
            // Delay a bit before imitating the click so actions aren't too fast
            jitterBeforeClick()
            if (manualInterruptionDetected) return false
            if (node.isClickable) return node.performAction(AccessibilityNodeInfo.ACTION_CLICK)
            val parent = node.parent
            if (parent != null && parent.isClickable) return parent.performAction(AccessibilityNodeInfo.ACTION_CLICK)
            val b = Rect().also { node.getBoundsInScreen(it) }
            if (!b.isEmpty) {
                val (x, y) = randomPointInRect(b)
                val path = Path().apply { moveTo(x, y) }
                val stroke = GestureDescription.StrokeDescription(path, 20, 50)
                val gesture = GestureDescription.Builder().addStroke(stroke).build()
                val dispatched = dispatchGesture(gesture, object : GestureResultCallback() {}, null)
                return dispatched
            }
        } catch (e: Exception) { Log.e(TAG, "click error", e) }
        return false
    }

    private fun findExactTextNode(root: AccessibilityNodeInfo, exact: String): AccessibilityNodeInfo? {
        val nodes = root.findAccessibilityNodeInfosByText(exact)
        if (nodes != null && nodes.isNotEmpty()) {
            for (n in nodes) {
                val t = n.text?.toString()?.trim()
                val cd = n.contentDescription?.toString()?.trim()
                if (t == exact || cd == exact) return n
            }
        }
        val q = ArrayDeque<AccessibilityNodeInfo>()
        q.add(root)
        while (q.isNotEmpty()) {
            val n = q.removeFirst()
            try {
                val t = n.text?.toString()?.trim()
                val cd = n.contentDescription?.toString()?.trim()
                if (t == exact || cd == exact) return n
                for (i in 0 until n.childCount) n.getChild(i)?.let { q.add(it) }
            } catch (_: Exception) {}
        }
        return null
    }

    private fun randomPointInRect(rect: Rect): Pair<Float, Float> {
        // Clamp to the display: a partially scrolled row can extend past the edge, and a tap outside
        // the screen is silently dropped.
        val r = Rect(rect)
        if (!r.intersect(0, 0, resources.displayMetrics.widthPixels, resources.displayMetrics.heightPixels)) {
            r.set(rect)
        }
        val paddingX = max(1, (r.width() * 0.1).toInt())
        val paddingY = max(1, (r.height() * 0.1).toInt())
        val left = r.left + paddingX
        val right = r.right - paddingX
        val top = r.top + paddingY
        val bottom = r.bottom - paddingY
        val x = Random.nextInt(left, (right).coerceAtLeast(left + 1)) .toFloat()
        val y = Random.nextInt(top, (bottom).coerceAtLeast(top + 1)) .toFloat()
        return Pair(x, y)
    }

    private fun randomDelay(minMs: Int, maxMs: Int): Long = Random.nextLong(from = minMs.toLong(), until = maxMs.toLong())

    private fun showForegroundNotification(label: String) {
        try {
            val nm = getSystemService(Context.NOTIFICATION_SERVICE) as NotificationManager
            if (android.os.Build.VERSION.SDK_INT >= android.os.Build.VERSION_CODES.O) {
                val ch = NotificationChannel(NOTIF_CHANNEL_ID, "Automation", NotificationManager.IMPORTANCE_LOW)
                nm.createNotificationChannel(ch)
            }
            val pending = PendingIntent.getActivity(this, 0, Intent(this, MainActivity::class.java).apply { addFlags(Intent.FLAG_ACTIVITY_NEW_TASK) }, PendingIntent.FLAG_IMMUTABLE or PendingIntent.FLAG_UPDATE_CURRENT)
            // PendingIntent to stop automation via the service
            val stopIntent = Intent(this, LauncherAccessibilityService::class.java).apply { action = ACTION_STOP_AUTOMATION }
            val pendingStop = PendingIntent.getService(this, 1, stopIntent, PendingIntent.FLAG_IMMUTABLE or PendingIntent.FLAG_UPDATE_CURRENT)
            val notif = NotificationCompat.Builder(this, NOTIF_CHANNEL_ID)
                .setContentTitle("Automation running")
                .setContentText("Running: $label")
                .setSmallIcon(android.R.drawable.ic_dialog_info)
                .setContentIntent(pending)
                .addAction(android.R.drawable.ic_menu_close_clear_cancel, "Stop", pendingStop)
                .setOngoing(true)
                .build()
            // Use notify instead of startForeground to avoid manifest changes
            // On Android 13+ we need POST_NOTIFICATIONS permission; if it is missing we simply skip
            // the notification. No toast here on purpose: an on-screen toast covers the app being
            // automated and hides what the accessibility service is doing.
            if (android.os.Build.VERSION.SDK_INT >= android.os.Build.VERSION_CODES.TIRAMISU) {
                val has = ContextCompat.checkSelfPermission(this, Manifest.permission.POST_NOTIFICATIONS) == PackageManager.PERMISSION_GRANTED
                if (has) {
                    nm.notify(NOTIF_ID, notif)
                    notificationShown = true
                } else {
                    logProgress("Notification permission not granted; progress is only shown here")
                    notificationShown = false
                }
            } else {
                nm.notify(NOTIF_ID, notif)
                notificationShown = true
            }
        } catch (e: Exception) {
            Log.w(TAG, "Failed to show notification", e)
        }
    }

    private fun hideForegroundNotification() {
        try {
            if (notificationShown) {
                val nm = getSystemService(Context.NOTIFICATION_SERVICE) as NotificationManager
                nm.cancel(NOTIF_ID)
                notificationShown = false
            }
        } catch (e: Exception) {
            Log.w(TAG, "Failed to hide notification", e)
        }
    }

    private fun finishTaskWithResult(result: String) {
        // Single exit for a run: stop the watchdog, write the summary, then put our own app back in
        // front on the Logging tab so the outcome is waiting for the user.
        val finishingMode = activeAutomationMode
        runActive = false
        unlikeUnfollowToken++
        resetUnlikeUnfollowManualState()
        taskAppCleanupToken++
        taskAppCleanupInProgress = false
        capturingTaskApps = false
        taskApps.clear()
        externalTaskCandidate = null
        externalTaskCandidateHits = 0
        confirmedExternalTaskApp = null
        clearExternalHandoffState()
        startupRecoveryActive = false
        startupUnknownSignature = emptySet()
        startupUnknownHits = 0
        mainHandler.removeCallbacks(watchdogTick)
        try {
            hideForegroundNotification()
        } catch (_: Exception) {}
        result.lineSequence().forEach { line ->
            if (line.isNotBlank()) AutomationLog.append(line)
        }
        if (finishingMode == AutomationMode.COLLECT_AWARDS) {
            logRunSummary()
        }
        AutomationLog.endRun("${finishingMode?.displayName ?: "Automation"} finished")
        AutomationLog.setActiveMode(null)
        activeAutomationMode = null
        shouldClickElement = false
        targetLabel = null
        targetPackageName = null
        // The destination activity displays completion feedback after it reaches the foreground;
        // showing a service toast immediately before this transition is unreliable on newer Android.
        showLogInApp(AUTOMATION_FINISHED_MESSAGE)
    }

    // Called when the current app's flow completes; continue with next package or finish overall
    private fun finishCurrentApp(resultForApp: String) {
        resetUnlikeUnfollowManualState()
        startupRecoveryActive = false
        startupUnknownSignature = emptySet()
        startupUnknownHits = 0
        val pkg = targetPackageName ?: "(unknown)"
        logProgress("[$pkg] $resultForApp")
        overallResults.add("$pkg: $resultForApp")
        // short delay and then proceed to next
        proceedToNextPackage()
    }

    companion object {
        private const val TAG = "LauncherAccessibility"
        private const val AUTOMATION_FINISHED_MESSAGE =
            "Automation finished. Opening the automation log."
        // Upper bound for "keep looking for this node" retry loops so a missing element cannot spin
        // forever (and flood the log).
        private const val MAX_SEARCH_ATTEMPTS = 12
        // How long we poll for the launched app to reach the foreground (chooser included).
        private const val MAX_FOREGROUND_WAIT_ATTEMPTS = 20
        private const val MAX_STARTUP_UNREADABLE_POLLS = 12
        private const val MAX_STARTUP_BACK_PRESSES = 8
        private const val STARTUP_UNKNOWN_CONFIRMATIONS = 2
        private const val STARTUP_RECOVERY_POLL_MIN_MS = 450
        private const val STARTUP_RECOVERY_POLL_MAX_MS = 750
        private const val STARTUP_BACK_SETTLE_MIN_MS = 800
        private const val STARTUP_BACK_SETTLE_MAX_MS = 1_200
        private const val TASK_ENTRY_SOURCE_PAGE_TITLE = "携程会员签到"
        private const val TASK_ENTRY_SOURCE_PAGE_ID = "LEGAO-membersignin2021"
        private const val TASK_LIST_PAGE_ID = "LEGAO-task_list"
        private const val TASK_ENTRY_BUTTON_TEXT = "做任务赚积分"
        private val TASK_ENTRY_PAGE_MARKERS = listOf(
            TASK_ENTRY_BUTTON_TEXT, "最高赚", "立即赚更多"
        )
        private val POINTS_SHELL_LABELS_CJK = setOf(
            "会员中心", "签到任务", "我的积分", "会员商城", "积多分"
        )
        private const val CJK_POINTS = "积分"
        private val MINE_COUNTER_LABELS_CJK = setOf("收藏", "浏览历史", "优惠券")
        private const val CHOOSER_CLICK_COOLDOWN_MS = 2000L
        // WebView hierarchies can spend ~60 interesting nodes on the page shell before reaching card
        // descendants. Keep enough nodes for the waterfall while still bounding log/memory usage.
        private const val MAX_DUMP_NODES = 120
        /** Manual captures are deliberate and should retain more detail-page descendants. */
        private const val MANUAL_DUMP_MAX_NODES = 320
        private const val DUMP_TOOL_BUTTON_SIZE_DP = 48
        private const val DUMP_TOOL_ICON_PADDING_DP = 12
        private const val DUMP_TOOL_BUTTON_GAP_DP = 6
        private const val DUMP_TOOL_CARD_PADDING_HORIZONTAL_DP = 7
        private const val DUMP_TOOL_CARD_PADDING_VERTICAL_DP = 6
        private const val DUMP_TOOL_CARD_RADIUS_DP = 18
        private const val DUMP_TOOL_BUTTON_RADIUS_DP = 14
        private const val DUMP_TOOL_ELEVATION_DP = 12
        private const val DUMP_TOOL_STROKE_DP = 1
        private const val DUMP_TOOL_EDGE_MARGIN_DP = 8
        private const val DUMP_TOOL_MARGIN_DP = 12
        private const val DUMP_TOOL_TOP_DP = 96
        // The initial task-list hierarchy is the refactoring input, so retain more card descendants.
        private const val TASK_LIST_DUMP_MAX_NODES = 240
        private const val DUMP_FIELD_MAX_CHARS = 160
        private const val FAILURE_SCREENSHOT_TIMEOUT_MS = 2_500L
        private const val FAILURE_SCREENSHOT_MAX_EDGE_PX = 960
        // A node is considered part of the bottom tab bar when its centre sits below this fraction
        // of the screen height.
        private const val BOTTOM_BAR_FRACTION = 0.85f
        // Jitter before a synthetic click: enough to not fire instantly, not enough to be felt.
        private const val CLICK_JITTER_MIN_MS = 60L
        private const val CLICK_JITTER_MAX_MS = 180L
        // Settle time after a step's click before looking for the next step's target.
        private const val STEP_SETTLE_MIN_MS = 400
        private const val STEP_SETTLE_MAX_MS = 700
        // Polling cadence while a step's target has not appeared yet. Short and frequent, so a page
        // that is already loaded is acted on immediately instead of after a fixed wait.
        private const val STEP_RETRY_MIN_MS = 300
        private const val STEP_RETRY_MAX_MS = 500
        private const val STEP_RETRY_ATTEMPTS = 24
        // How long to wait for a step's result before deciding the click did not register.
        private const val STEP_VERIFY_POLLS = 8
        // Times a single step may be clicked before giving up on it.
        private const val STEP_MAX_CLICKS = 3

        // --- Unlike & Unfollow diagnostic navigation ---
        private const val UNLIKE_STEP_MAX_ATTEMPTS = 24
        private const val UNLIKE_STATUS_EVERY_ATTEMPTS = 6
        private const val UNLIKE_STEP_POLL_MIN_MS = 350
        private const val UNLIKE_STEP_POLL_MAX_MS = 550
        private const val UNLIKE_STEP_SETTLE_MIN_MS = 700
        private const val UNLIKE_STEP_SETTLE_MAX_MS = 1_100
        private const val UNLIKE_DUMP_INITIAL_SETTLE_MS = 900L
        private const val UNLIKE_DUMP_POLL_MS = 500L
        private const val UNLIKE_DUMP_SETTLE_ATTEMPTS = 8
        private const val UNLIKE_DUMP_STABLE_SAMPLES = 2
        private const val UNLIKE_MAX_TARGET_WIDTH_FRACTION = 0.75f
        private const val UNLIKE_MAX_TARGET_HEIGHT_FRACTION = 0.25f

        // Attempt on which a step tries to dismiss a covering banner/modal before retrying.
        private const val DISMISS_POPUP_ON_ATTEMPT_FAST = 6

        // --- Geometry of the profile page's counters row (收藏 / 浏览历史 / 积分 / 优惠券) ---
        // Vertical gap allowed between a counter's value and the label underneath it.
        private const val COUNTER_VALUE_MAX_GAP_PX = 140
        // Vertical slack when deciding whether two counters share a row.
        private const val COUNTER_ROW_TOLERANCE_PX = 60
        // Vertical gap allowed between the 价值￥xx badge and the value below it.
        private const val COUNTER_BADGE_MAX_GAP_PX = 170
        // A clickable ancestor wider than this multiple of the cell is the whole-row card, not a cell.
        private const val MAX_CELL_CONTAINER_WIDTH_RATIO = 2.0
        private val COUNTER_PEER_LABELS = setOf("收藏", "浏览历史", "优惠券")
        // A counter value such as "0", "12" or "4,414".
        private val NUMERIC_RE = Regex("^\\d[\\d,，.]*$")
        // Value and label rendered as one node, e.g. "4,414积分".
        private val COMBINED_POINTS_RE = Regex("^\\d[\\d,，.]*\\s*积分$")

        // --- task list geometry ---
        // Action buttons live in the right-hand column; task titles start with 去 too, so the column
        // is what separates them (去七猫 the button vs 去七猫免费看小说短剧 the title).
        private const val ACTION_COLUMN_MIN_X_FRACTION = 0.62f
        // Captured task titles start at x≈244 on a 1080px screen; section labels start near x≈156.
        private const val TASK_CONTENT_MIN_X_FRACTION = 0.20f
        // In every captured row the title top precedes the action top by roughly 42px. Keep bounded
        // slack for density/layout variation without reverting to unsafe center-Y-only pairing.
        private const val TASK_TITLE_MAX_LEAD_PX = 100
        private const val TASK_DESC_MAX_GAP_PX = 90
        private const val TASK_DESC_MAX_INDENT_PX = 140
        // Right-column geometry already distinguishes actions from titles, so allow longer partner
        // names instead of silently dropping a valid 去… button after six characters.
        private val ACTION_BUTTON_RE = Regex("^去\\S{1,12}$")
        private const val TASK_LIST_END_TEXT = "暂时没有更多了"
        private const val TASK_SHOW_ON_SCREEN_SETTLE_MS = 450L
        // Interactive in-app task: launch the 星球号 page, press its header follow button, then Back.
        private val PLANET_FOLLOW_TASK_RE = Regex("^关注.+星球号$")
        private const val PLANET_FOLLOW_ACTION = "去完成"
        private const val PLANET_FOLLOW_CONTROL = "关注"
        private const val PLANET_FOLLOW_TIMEOUT_MS = 12_000L
        private const val PLANET_FOLLOW_POLL_MIN_MS = 450
        private const val PLANET_FOLLOW_POLL_MAX_MS = 750
        private const val PLANET_FOLLOW_SETTLE_MIN_MS = 900
        private const val PLANET_FOLLOW_SETTLE_MAX_MS = 1_300
        private const val PLANET_FOLLOW_MIN_X_FRACTION = 0.60f
        private const val PLANET_FOLLOW_MAX_Y_FRACTION = 0.22f
        private const val PLANET_FOLLOW_MAX_WIDTH_FRACTION = 0.45f
        private const val PLANET_FOLLOW_MAX_HEIGHT_FRACTION = 0.18f
        // Interactive in-app task: open the hotel ranking, wait for its data, tap the bottom image,
        // verify that another page opened, and only then Back to 签到任务.
        private const val HOTEL_RANKING_TASK_TITLE = "点击浏览任意上榜酒店"
        private const val HOTEL_RANKING_ACTION = "去完成"
        private const val HOTEL_RANKING_DATA_SETTLE_MS = 2_000L
        private const val HOTEL_RANKING_TIMEOUT_MS = 18_000L
        private const val HOTEL_RANKING_VERIFY_POLL_MIN_MS = 450
        private const val HOTEL_RANKING_VERIFY_POLL_MAX_MS = 700
        private const val HOTEL_RANKING_NAVIGATION_CONFIRMATIONS = 2
        private const val HOTEL_RANKING_POLLS_PER_TAP = 3
        private const val HOTEL_RANKING_RETRY_SETTLE_MS = 500L
        private const val HOTEL_RANKING_DETAIL_SETTLE_MIN_MS = 700
        private const val HOTEL_RANKING_DETAIL_SETTLE_MAX_MS = 1_000
        private const val HOTEL_RANKING_MARKER_SUFFIX = "酒店榜"
        private const val HOTEL_RANKING_MAX_CLICKABLE_DUMP_NODES = 16
        // First hotel image measured from the supplied 478x1080 screenshot: approximately
        // [15,753]–[466,954]. The deterministic center/left/right points avoid badges and edges.
        private const val HOTEL_IMAGE_LEFT_FRACTION = 0.03f
        private const val HOTEL_IMAGE_TOP_FRACTION = 0.70f
        private const val HOTEL_IMAGE_RIGHT_FRACTION = 0.97f
        private const val HOTEL_IMAGE_BOTTOM_FRACTION = 0.88f
        private val HOTEL_IMAGE_TAP_POINTS = listOf(
            0.50f to 0.79f,
            0.30f to 0.79f,
            0.70f to 0.79f,
        )
        // Dedicated same-app flow shown in the supplied screenshots: enter 天天领现金, scroll once,
        // skip the first visible card row, open a card from the next proven two-column row, then dwell.
        private const val DAILY_CASH_NOTE_TASK_TITLE = "天天领现金-浏览笔记"
        private const val DAILY_CASH_NOTE_DESCRIPTION = "浏览任意一篇笔记"
        private const val DAILY_CASH_NOTE_ACTION = "去参与"
        private const val DAILY_CASH_DESTINATION_MARKER = "天天领现金"
        // IDs confirmed by the supplied WebView hierarchy dump.
        private const val DAILY_CASH_BROWSE_PANEL_ID = "pageBrowseNote"
        private val DAILY_CASH_WATERFALL_IDS = listOf("waterfall", "waterfallBox")
        private const val DAILY_CASH_NOTE_GRID_ANCHOR = "继续领现金"
        private const val DAILY_CASH_INITIAL_SETTLE_MS = 2_000L
        private const val DAILY_CASH_NOTE_TIMEOUT_MS = 25_000L
        private const val DAILY_CASH_POLL_MIN_MS = 400
        private const val DAILY_CASH_POLL_MAX_MS = 650
        private const val DAILY_CASH_DESTINATION_CONFIRMATIONS = 2
        private const val DAILY_CASH_ANCHOR_STABLE_TOLERANCE_PX = 12
        private const val DAILY_CASH_MIN_SCROLL_FRACTION = 0.08f
        private const val DAILY_CASH_SCROLL_SETTLE_MS = 1_100L
        private const val DAILY_CASH_CARD_SETTLE_MS = 600L
        private const val DAILY_CASH_NAVIGATION_SETTLE_MS = 900L
        private const val DAILY_CASH_NAVIGATION_CONFIRMATIONS = 2
        private const val DAILY_CASH_REQUIRED_CARD_ROWS = 2
        private const val DAILY_CASH_CARD_MIN_WIDTH_FRACTION = 0.32f
        private const val DAILY_CASH_CARD_MAX_WIDTH_FRACTION = 0.58f
        private const val DAILY_CASH_CARD_MIN_HEIGHT_FRACTION = 0.14f
        private const val DAILY_CASH_CARD_MAX_HEIGHT_FRACTION = 0.62f
        private const val DAILY_CASH_CARD_MIN_CENTER_Y_FRACTION = 0.20f
        private const val DAILY_CASH_CARD_CENTER_GUTTER_FRACTION = 0.04f
        private const val DAILY_CASH_CARD_ROW_TOP_TOLERANCE_FRACTION = 0.09f
        private const val DAILY_CASH_CARD_MAX_WIDTH_RATIO = 1.35
        private const val DAILY_CASH_CARD_DUPLICATE_OVERLAP = 0.82
        private const val DAILY_CASH_GRID_TOP_TOLERANCE_PX = 24
        private const val DAILY_CASH_MIN_NOTE_CONTENT_NODES = 3
        private const val DAILY_CASH_MIN_NOTE_TEXT_LENGTH = 4
        private const val DAILY_CASH_MAX_NOTE_SIGNATURE_NODES = 24
        // A note-detail back affordance must remain in the compact top-left header area.
        private const val DAILY_CASH_BACK_MAX_X_FRACTION = 0.22f
        private const val DAILY_CASH_BACK_MAX_Y_FRACTION = 0.18f
        private const val DAILY_CASH_BACK_MAX_WIDTH_FRACTION = 0.22f
        private const val DAILY_CASH_BACK_MAX_HEIGHT_FRACTION = 0.16f
        private val DAILY_CASH_BACK_LABELS = listOf("返回", "back")
        private val DAILY_CASH_NON_CONTENT_MARKERS = listOf(
            "加载中", "正在加载", "网络异常", "加载失败", "重新加载", "出错", "暂无内容"
        )
        private val DAILY_CASH_NOTE_CHROME_TEXTS = listOf(
            DAILY_CASH_DESTINATION_MARKER, DAILY_CASH_NOTE_GRID_ANCHOR,
            "返回", "分享", "收藏", "点赞", "评论"
        )
        private val DAILY_CASH_REJECTED_CARD_TEXTS = listOf(
            "活动规则", "立即邀请", "去提现", "去看笔记", "去评论", "继续领现金", "福利任务"
        )
        // Data-driven WeChat mini-program interactions. Adding another same-style task should only
        // require one registry entry with title/CTA patterns and a screenshot-calibrated safe center.
        private const val WECHAT_PACKAGE = "com.tencent.mm"
        private const val MINI_PROGRAM_ROOTLESS_CLICK_ATTEMPT = 1
        private const val MINI_PROGRAM_SETTLE_MS = 10_000L
        private const val MINI_PROGRAM_POLL_MS = 700L
        private const val MINI_PROGRAM_MAX_ATTEMPTS = 24
        private const val MINI_PROGRAM_STATUS_EVERY_ATTEMPTS = 5
        private const val MINI_PROGRAM_PROMPT_POLL_MS = 600L
        private const val MINI_PROGRAM_PROMPT_MAX_ATTEMPTS = 14
        private const val MINI_PROGRAM_PROMPT_ROOTLESS_CLICK_ATTEMPT = 3
        private val MINI_PROGRAM_TASK_SPECS = listOf(
            MiniProgramTaskSpec(
                id = "Tencent game benefits",
                taskTitle = Regex("^腾讯游戏送福利$"),
                ctaText = Regex("^立即前往$"),
                ctaDescription = "'立即前往'",
                // Supplied Tencent screenshot: safe center of the broad blue CTA.
                ctaFallback = NormalizedRect(0.36f, 0.82f, 0.64f, 0.88f),
                prompt = MiniProgramPromptSpec(
                    markers = listOf("即将打开", "腾讯游戏人生"),
                    positiveText = "允许",
                ),
            ),
            MiniProgramTaskSpec(
                id = "Didi ride coupon",
                // Keep the destination robust to small campaign-title changes while remaining narrow.
                taskTitle = Regex("^去微信领.*(?:滴滴)?打车券$"),
                ctaText = Regex("^点击立领.*券包$"),
                ctaDescription = "'点击立领…券包'",
                // Supplied 480×1024 screenshot: orange CTA spans about x=76..404, y=740..792.
                // This central rectangle avoids the rounded edges and the lower-left 返回APP control.
                ctaFallback = NormalizedRect(0.30f, 0.73f, 0.70f, 0.78f),
                // The title is campaign-dependent and can wrap, so the dialog must be recognised
                // semantically rather than with a display-coordinate approval tap.
                prompt = MiniProgramPromptSpec(
                    markers = listOf("即将打开", "小程序"),
                    positiveText = "允许",
                ),
            ),
        )
        // Finished, award pending / finished and collected: both are skipped.
        private val SKIP_BUTTON_TEXTS = setOf("领奖励", "已完成", "已领取", "明日再来")
        // Buttons we deliberately leave alone. These are not finished tasks — they lead somewhere the
        // automation cannot carry through, such as a WeChat mini-program or a page that needs real
        // interaction rather than a timed visit. Matched as a substring so a longer label still counts.
        private val IGNORED_BUTTON_TEXTS = listOf("去微信", "去参与", "去浏览")
        private val CONFIRM_LEAVE_TEXTS = listOf("允许", "继续", "打开", "确定", "始终允许")
        private const val CONFIRM_LEAVE_ATTEMPTS = 5
        private const val EXTERNAL_APP_WAIT_ATTEMPTS = 8
        // A browser can render before its website→app confirmation. Keep sampling briefly instead of
        // accepting that browser as the task destination and starting the dwell too early.
        private const val EXTERNAL_HANDOFF_PROMPT_GRACE_MS = 15_000L
        private const val EXTERNAL_HANDOFF_TIMEOUT_MS = 12_000L
        private const val EXTERNAL_HANDOFF_POLL_MIN_MS = 500
        private const val EXTERNAL_HANDOFF_POLL_MAX_MS = 900
        private const val EXTERNAL_HANDOFF_CLICK_COOLDOWN_MS = 1_500L
        // This exact combination prevents a generic camera/location/notification permission dialog
        // from ever being interpreted as the browser asking to launch another installed app.
        private val BROWSER_APP_HANDOFF_REQUEST_RE = Regex(
            "(?:网页|网站).{0,16}(?:请求|尝试).{0,16}(?:打开|启动|唤起).+"
        )
        private val BROWSER_APP_HANDOFF_NEGATIVE_TEXTS = setOf("拒绝")
        private val BROWSER_APP_HANDOFF_POSITIVE_TEXTS = setOf("允许", "打开", "继续打开")
        // Exact controls that may dismiss a foreground external app's non-cancelable interstitial.
        // Deliberately excludes generic 取消 and substring matching to avoid arbitrary page actions.
        private val EXTERNAL_CLOSE_LABELS = setOf("关闭", "Close", "×", "✖")
        // A package must be the stable non-Ctrip foreground for this many samples before HOME/kill is
        // allowed. One sample can be a chooser, permission window or other transient system overlay.
        private const val EXTERNAL_APP_CONFIRMATIONS = 2
        // A reported external package may actually be an activity stacked above Ctrip in the same
        // Android task. Probe BACK several times before HOME/kill/Recents, verifying after each one.
        private const val MAX_EXTERNAL_BACK_PRESSES = 5
        // BACK presses allowed while stepping back to 签到任务 from a page inside the app. Every press
        // is followed by page verification, so this cannot continue past the task page.
        private const val MAX_IN_APP_BACK_PRESSES = 8
        // Recents taps come before a relaunch, because they need no background-launch permission.
        private const val RECENTS_ATTEMPTS = 2
        private const val RECENTS_SETTLE_MS = 1_200L
        private const val RECENTS_DISMISS_ATTEMPTS = 2
        private const val RECENTS_DISMISS_VERIFY_MS = 900L
        private const val RECENTS_CARD_ANCESTOR_DEPTH = 8
        private const val RECENTS_CARD_MIN_WIDTH_FRACTION = 0.25f
        private const val RECENTS_CARD_MAX_WIDTH_FRACTION = 0.98f
        private const val RECENTS_CARD_MIN_HEIGHT_FRACTION = 0.20f
        private const val RECENTS_CARD_MAX_HEIGHT_FRACTION = 0.90f
        private const val RECENTS_CARD_DISMISS_DURATION_MS = 350L
        // A run that logs nothing for this long is considered stuck. Deliberate stays inside a task
        // app extend the deadline, so this only fires on genuine inactivity.
        private const val STALL_TIMEOUT_MS = 60_000L
        private const val WATCHDOG_TICK_MS = 5_000L
        private const val TASK_OUTCOME_DONE = "done"
        private const val EDGE_SWIPE_DURATION_MS = 260L
        private const val KILL_DELAY_MS = 800L
        private const val TASK_PAGE_TITLE = "签到任务"
        // 做任务赚积分 button from the supplied 1080×2400 hierarchy: [264,1196][816,1344].
        // Fractions are relative to the accessibility root rather than display metrics, preserving
        // physical coordinates when Android reports a display height excluding navigation insets.
        private const val TASK_ENTRY_LEFT_FRACTION = 0.2444f
        private const val TASK_ENTRY_TOP_FRACTION = 0.4983f
        private const val TASK_ENTRY_RIGHT_FRACTION = 0.7556f
        private const val TASK_ENTRY_BOTTOM_FRACTION = 0.5600f
        private const val TASK_ENTRY_EXPECTED_CENTER_X_FRACTION = 0.50f
        private const val TASK_ENTRY_EXPECTED_CENTER_Y_FRACTION = 0.529f
        private const val TASK_ENTRY_MIN_WIDTH_FRACTION = 0.40f
        private const val TASK_ENTRY_MAX_WIDTH_FRACTION = 0.65f
        private const val TASK_ENTRY_MIN_HEIGHT_FRACTION = 0.04f
        private const val TASK_ENTRY_MAX_HEIGHT_FRACTION = 0.10f
        private const val TASK_ENTRY_MIN_CENTER_X_FRACTION = 0.35f
        private const val TASK_ENTRY_MAX_CENTER_X_FRACTION = 0.65f
        private const val TASK_ENTRY_MIN_CENTER_Y_FRACTION = 0.45f
        private const val TASK_ENTRY_MAX_CENTER_Y_FRACTION = 0.60f
        // One wall-clock budget includes node lookup, clicks, waits and destination verification.
        private const val TASK_ENTRY_STEP_TIMEOUT_MS = 8_000L
        private const val TASK_ENTRY_VERIFY_POLLS = 3
        private const val TASK_ENTRY_MAX_CLICKS = 3
        // Subtitle of the 签到·任务 card on 我的积分; plain text when WebView exposes it separately.
        private const val SIGN_IN_CARD_SUBTITLE = "签到赚积分"
        // Marked upper-left card from the supplied 480×1024 screenshot, expressed as root fractions.
        private const val SIGN_IN_CARD_LEFT_FRACTION = 0.03f
        private const val SIGN_IN_CARD_TOP_FRACTION = 0.35f
        private const val SIGN_IN_CARD_RIGHT_FRACTION = 0.50f
        private const val SIGN_IN_CARD_BOTTOM_FRACTION = 0.43f
        private const val SIGN_IN_CARD_MAX_LABEL_WIDTH_FRACTION = 0.55f
        private const val SIGN_IN_CARD_MAX_LABEL_HEIGHT_FRACTION = 0.12f
        private const val SIGN_IN_CARD_MAX_CENTER_X_FRACTION = 0.55f
        private const val SIGN_IN_CARD_MIN_CENTER_Y_FRACTION = 0.34f
        private const val SIGN_IN_CARD_MAX_CENTER_Y_FRACTION = 0.45f
        // Marked second tab; the hierarchy exposes it near [214,2255][434,2401] on 1080×2400.
        private const val SIGN_IN_TAB_LEFT_FRACTION = 0.19f
        private const val SIGN_IN_TAB_TOP_FRACTION = 0.94f
        private const val SIGN_IN_TAB_RIGHT_FRACTION = 0.41f
        private const val SIGN_IN_TAB_BOTTOM_FRACTION = 1.00f
        // A bottom-bar item is at most this fraction of the screen width; anything wider is the bar.
        private const val MAX_BOTTOM_TAB_WIDTH_FRACTION = 0.4f
        // Only used to recognise the 签到任务 page by its tab row.
        private val TASK_GROUP_NAMES = setOf("推荐任务", "日常任务", "挑战任务", "合作任务")
        private val TASK_GROUP_NAMES_CJK = TASK_GROUP_NAMES
        // Group names sharing one line are the tab row; a name alone on its line is a section header.
        private const val TAB_ROW_TOLERANCE_PX = 40
        // Consecutive identical samples needed before believing the page has stopped.
        private const val END_OF_PAGE_CONFIRMATIONS = 2
        // One controlled drag: most of a screen, slow enough not to fling and skip content.
        private const val PAGE_DRAG_NEAR_FRACTION = 0.22f
        private const val PAGE_DRAG_FAR_FRACTION = 0.82f
        private const val PAGE_DRAG_DURATION_MS = 450L
        // Reward summary card confirmed by the captured full WebView hierarchy. Its claim control is
        // exact-labelled and sits on the right side; substring/global matching is fallback-only.
        private const val CLAIM_REWARD_MODULE_ID = "module_228543D"
        private val CLAIM_ALL_LABELS = setOf("一键领", "一键领取")
        private val NO_CLAIM_REWARD_TEXTS = listOf("暂无可领取奖励")
        private val CLAIM_CARD_TEXT_PREFIXES = listOf("您共有", "待领取", "可领取奖励")
        private val CLAIM_PENDING_COUNT_RE = Regex("您共有\\s*(\\d+)\\s*.*待领取")
        private const val CLAIM_MODULE_ACTION_MIN_X_FRACTION = 0.62f
        private const val CLAIM_FALLBACK_MIN_X_FRACTION = 0.62f
        private const val CLAIM_MAX_TARGET_WIDTH_FRACTION = 0.50f
        // The complete opening/final claim check, including rendering and refresh waits, must not hold
        // the task flow for longer than this when the button remains visible but has nothing to give.
        private const val CLAIM_ATTEMPT_TIMEOUT_MS = 5_000L
        // Times to look for the claim button before deciding there is nothing to collect. The deadline
        // above can end this polling earlier.
        private const val CLAIM_POLLS = 8
        private const val CLAIM_POLL_MIN_MS = 500
        private const val CLAIM_POLL_MAX_MS = 900
        // Deliberate pause before the very first look, for the same reason.
        private const val CLAIM_FIRST_LOOK_MIN_MS = 1_200
        private const val CLAIM_FIRST_LOOK_MAX_MS = 1_600
        // A successful claim refreshes the list. Wait for it, then run the next asynchronous loop
        // iteration with absence polling reset to its first look.
        private const val CLAIM_REFRESH_MIN_MS = 1_200
        private const val CLAIM_REFRESH_MAX_MS = 1_700
        // Not a normal round limit: this only prevents a permanently visible/stale clickable node from
        // running forever. Ordinary completion requires CLAIM_POLLS consecutive misses after refresh.
        private const val MAX_CLAIM_CLICKS_SAFETY = 50
        // Independent outer-cycle guard for pages that continually reveal new unique tasks after
        // every claim. This bounds claim/rescan cycling without limiting tasks in a normal scan.
        private const val MAX_FINAL_CLAIM_PASSES = 13
        // After 一键领, wait for semantic task-row content to change and settle. This budget starts
        // after claiming ends; it is intentionally separate from CLAIM_ATTEMPT_TIMEOUT_MS.
        private const val TASK_LIST_REFRESH_TIMEOUT_MS = 5_000L
        private const val TASK_LIST_REFRESH_POLL_MIN_MS = 350
        private const val TASK_LIST_REFRESH_POLL_MAX_MS = 550
        private const val TASK_LIST_REFRESH_STABLE_SAMPLES = 2
        private const val POST_CLAIM_RESCAN_SETTLE_MS = 500L
        private const val MAX_TASK_SCROLLS = 25
        private const val SWIPE_DURATION_MS = 320L
        // How long to stay in the other app. The task text wins when it states a duration.
        private const val MIN_DWELL_SECONDS = 12
        private const val DEFAULT_DWELL_SECONDS = 20
        private const val MAX_DWELL_SECONDS = 180
        // A stated duration is a minimum, and the other app's timer starts after its page loads, so
        // always overshoot it a little.
        private const val DWELL_SAFETY_MARGIN_SECONDS = 5
        // "浏览30s以上", "浏览页面10s", "停留15秒", "观看30秒钟", "看1分钟".
        private val DURATION_RE = Regex("(\\d+(?:\\.\\d+)?)\\s*(秒钟|秒|分钟|s|S)")
        // Vertical bucket used to group chooser entries into rows before sorting left-to-right.
        private const val CHOOSER_ROW_TOLERANCE_PX = 120
        // Titles used by stock Android and by OEM "dual apps" pickers.
        private val CHOOSER_TITLE_KEYS = listOf(
            "请选择要使用的应用", "选择要使用的应用", "请选择应用", "选择应用",
            "使用以下方式打开", "打开方式", "选择要使用的程序",
            "Open with", "Select an app", "Choose an app"
        )
        private val CANCEL_KEYS = listOf("取消", "Cancel", "关闭", "Close")
        // Markers of the "leaving this app" confirmation, which must never be read as an app chooser.
        private val LEAVE_APP_MARKERS = listOf("即将离开", "即将打开", "将要离开")
        // Packages known to host an app-selection dialog. On MIUI / HyperOS the "dual apps" picker
        // is XSpaceResolveActivity inside com.miui.securitycore, and `android` is the AOSP resolver.
        private val CHOOSER_PACKAGES = listOf(
            "com.miui.securitycore", "com.miui.securityadd", "com.miui.securitycenter", "android"
        )
        // System-owned overlays that may temporarily become the first accessibility window during a
        // task. They are neither task destinations nor safe evidence that Ctrip was left.
        private val NON_TASK_DESTINATION_PACKAGES = setOf(
            "android",
            "com.android.systemui",
            "com.android.permissioncontroller",
            "com.google.android.permissioncontroller",
            "com.miui.packageinstaller"
        )
        // Markers MIUI puts on the cloned entry ("XSpace" is its internal name for dual apps). The
        // original app carries none of these, which is how we prefer it over the clone.
        private val CLONE_MARKER_KEYS = listOf(
            "双开", "分身", "克隆", "第二空间", "副应用", "xspace", "x空间", "dual"
        )
        const val ACTION_START_AUTOMATION =
            "com.example.myapplication.ACTION_START_AUTOMATION"
        const val ACTION_OPEN_LAST_APP = "com.example.myapplication.ACTION_OPEN_LAST_APP"
        const val ACTION_STOP_AUTOMATION = "com.example.myapplication.ACTION_STOP_AUTOMATION"
        const val ACTION_SHOW_DUMP_TOOL =
            "com.example.myapplication.ACTION_SHOW_DUMP_TOOL"
        const val ACTION_HIDE_DUMP_TOOL =
            "com.example.myapplication.ACTION_HIDE_DUMP_TOOL"
        const val EXTRA_AUTOMATION_MODE = "automation_mode"
        const val EXTRA_TARGET_LABEL = "target_label"
    }
}

package com.example.myapplication

import android.Manifest
import android.content.ClipData
import android.content.ClipboardManager
import android.content.Context
import android.content.Intent
import android.content.pm.PackageManager
import android.os.Bundle
import android.provider.Settings
import android.widget.Toast
import androidx.core.content.ContextCompat
import androidx.core.content.FileProvider
import androidx.activity.ComponentActivity
import androidx.activity.compose.BackHandler
import androidx.activity.compose.rememberLauncherForActivityResult
import androidx.activity.compose.setContent
import androidx.activity.enableEdgeToEdge
import androidx.activity.result.contract.ActivityResultContracts
import androidx.compose.foundation.Image
import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.height
import androidx.compose.foundation.layout.heightIn
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.layout.width
import androidx.compose.foundation.rememberScrollState
import androidx.compose.foundation.text.selection.SelectionContainer
import androidx.compose.foundation.verticalScroll
import androidx.compose.foundation.lazy.LazyColumn
import androidx.compose.foundation.lazy.items
import androidx.compose.foundation.lazy.itemsIndexed
import androidx.compose.foundation.lazy.rememberLazyListState
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.automirrored.filled.List
import androidx.compose.material.icons.filled.*
import androidx.compose.material3.Button
import androidx.compose.material3.ButtonDefaults
import androidx.compose.material3.HorizontalDivider
import androidx.compose.material3.OutlinedTextField
import androidx.compose.material3.Icon
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.Scaffold
import androidx.compose.material3.Text
import androidx.compose.material3.TextButton
import androidx.compose.material3.adaptive.navigationsuite.NavigationSuiteScaffold
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.collectAsState
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.asImageBitmap
import androidx.compose.ui.graphics.vector.ImageVector
import androidx.compose.ui.layout.ContentScale
import androidx.compose.ui.platform.LocalContext
import androidx.compose.ui.text.font.FontFamily
import androidx.compose.ui.text.font.FontWeight
import androidx.compose.ui.tooling.preview.Preview
import androidx.compose.ui.tooling.preview.PreviewScreenSizes
import androidx.compose.ui.unit.dp
import com.example.myapplication.ui.theme.MyApplicationTheme
import com.example.myapplication.utils.DeviceUtils
import java.io.File
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.launch
import kotlinx.coroutines.withContext

class MainActivity : ComponentActivity() {
    private var pendingCompletionToast: String? = null

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        handleNavigationIntent(intent)
        AutomationSettings.init(this)
        enableEdgeToEdge()
        setContent {
            MyApplicationTheme {
                MyApplicationApp()
            }
        }
    }

    override fun onNewIntent(intent: Intent) {
        super.onNewIntent(intent)
        setIntent(intent)
        handleNavigationIntent(intent)
        // A top activity does not reliably receive onPostResume again after onNewIntent.
        // Consume and post the one-shot feedback here; onPostResume remains the cold-start path.
        showPendingCompletionToast()
    }

    override fun onPostResume() {
        super.onPostResume()
        showPendingCompletionToast()
    }

    private fun showPendingCompletionToast() {
        val message = pendingCompletionToast ?: return
        pendingCompletionToast = null
        // Post after the current lifecycle callback so the foreground Logging screen is drawn first.
        window.decorView.post {
            Toast.makeText(this, message, Toast.LENGTH_LONG).show()
        }
    }

    private fun handleNavigationIntent(intent: Intent?) {
        if (intent?.action != ACTION_SHOW_AUTOMATION_LOG) return
        AutomationLog.requestShowLog()
        intent.getStringExtra(EXTRA_COMPLETION_TOAST)
            ?.takeIf { it.isNotBlank() }
            ?.let { pendingCompletionToast = it }
        // Consume the one-shot destination and feedback so an activity recreation does not force
        // Logging again or repeat the completion toast after the user changes tabs.
        intent.action = null
        intent.removeExtra(EXTRA_COMPLETION_TOAST)
    }

    companion object {
        const val ACTION_SHOW_AUTOMATION_LOG =
            "com.example.myapplication.ACTION_SHOW_AUTOMATION_LOG"
        const val EXTRA_COMPLETION_TOAST =
            "com.example.myapplication.EXTRA_COMPLETION_TOAST"
    }
}

@PreviewScreenSizes
@Composable
fun MyApplicationApp() {
    var currentDestination by rememberSaveable { mutableStateOf(AppDestinations.HOME) }
    var selectedDumpEntryId by rememberSaveable { mutableStateOf<Long?>(null) }
    val logEntries by AutomationLog.entries.collectAsState()

    BackHandler(enabled = selectedDumpEntryId != null) {
        selectedDumpEntryId = null
    }

    // The service asks for the log to be shown when a run ends, so the summary is on screen without
    // the user having to go looking for it.
    val showLogRequest by AutomationLog.showLogRequests.collectAsState()
    LaunchedEffect(showLogRequest) {
        if (showLogRequest > 0) {
            selectedDumpEntryId = null
            currentDestination = AppDestinations.LOGGING
        }
    }

    NavigationSuiteScaffold(
        navigationSuiteItems = {
            AppDestinations.entries.forEach {
                item(
                    icon = {
                        Icon(
                            it.icon,
                            contentDescription = it.label
                        )
                    },
                    label = { Text(it.label) },
                    selected = it == currentDestination,
                    onClick = {
                        selectedDumpEntryId = null
                        currentDestination = it
                    }
                )
            }
        }
    ) {
        Scaffold(modifier = Modifier.fillMaxSize()) { innerPadding ->
            when (currentDestination) {
                AppDestinations.HOME -> DeviceControlsScreen(modifier = Modifier.padding(innerPadding))
                AppDestinations.LOGGING -> {
                    val selectedEntry = selectedDumpEntryId?.let { selectedId ->
                        logEntries.firstOrNull { it.id == selectedId }
                    }
                    if (selectedDumpEntryId != null) {
                        DumpDetailScreen(
                            entry = selectedEntry,
                            onBack = { selectedDumpEntryId = null },
                            modifier = Modifier.padding(innerPadding),
                        )
                    } else {
                        LoggingScreen(
                            onOpenDump = { selectedDumpEntryId = it },
                            modifier = Modifier.padding(innerPadding),
                        )
                    }
                }
                AppDestinations.ACCESSIBILITY -> AccessibilityScreen(modifier = Modifier.padding(innerPadding))
            }
        }
    }
}

enum class AppDestinations(
    val label: String,
    val icon: ImageVector,
) {
    HOME("Home", Icons.Default.Home),
    // Replaces the old FAVORITES tab: shows the live automation log instead.
    LOGGING("Logging", Icons.AutoMirrored.Filled.List),
    // Changed PROFILE to ACCESSIBILITY
    ACCESSIBILITY("Accessibility", Icons.Default.Home),
}

/**
 * Live view of [AutomationLog]. New entries are appended as the accessibility service runs and the
 * list follows the tail automatically, which replaces the toasts/dialogs that used to cover the
 * screen during a run.
 */
@Composable
fun LoggingScreen(
    onOpenDump: (Long) -> Unit,
    modifier: Modifier = Modifier,
) {
    val entries by AutomationLog.entries.collectAsState()
    val activeMode by AutomationLog.activeMode.collectAsState()
    val listState = rememberLazyListState()
    val context = LocalContext.current
    val coroutineScope = rememberCoroutineScope()
    var shareInProgress by remember { mutableStateOf(false) }
    var sharingDumpEntryId by remember { mutableStateOf<Long?>(null) }

    val shareDump: (AutomationLog.Entry) -> Unit = { entry ->
        val dump = entry.windowDump
        if (dump != null && !shareInProgress) {
            val snapshot = entry.copy(windowDump = dump.copy(nodes = dump.nodes.toList()))
            shareInProgress = true
            sharingDumpEntryId = entry.id
            coroutineScope.launch {
                try {
                    shareWindowDumpEntry(context, snapshot)
                } catch (e: Exception) {
                    Toast.makeText(
                        context,
                        "Could not create dump file: ${e.message ?: "unknown error"}",
                        Toast.LENGTH_LONG,
                    ).show()
                } finally {
                    sharingDumpEntryId = null
                    shareInProgress = false
                }
            }
        }
    }

    // A screenshot updates an existing row without changing list size, so observe the final entry
    // itself rather than only entries.size.
    LaunchedEffect(entries.lastOrNull()) {
        if (entries.isNotEmpty()) listState.animateScrollToItem(entries.lastIndex)
    }

    Column(
        modifier = modifier
            .fillMaxSize()
            .padding(16.dp)
    ) {
        Row(
            modifier = Modifier.fillMaxWidth(),
            verticalAlignment = Alignment.CenterVertically
        ) {
            Text(
                text = activeMode?.let { "Automation log (${it.displayName} running)" }
                    ?: "Automation log",
                style = MaterialTheme.typography.titleMedium,
                modifier = Modifier.weight(1f)
            )
            TextButton(
                enabled = entries.isNotEmpty(),
                onClick = {
                    val clipboard = context.getSystemService(Context.CLIPBOARD_SERVICE) as ClipboardManager
                    clipboard.setPrimaryClip(
                        ClipData.newPlainText("Automation log", AutomationLog.plainText(entries))
                    )
                    Toast.makeText(context, "Log copied", Toast.LENGTH_SHORT).show()
                }
            ) {
                Text("Copy all")
            }
            TextButton(
                enabled = entries.isNotEmpty() && !shareInProgress,
                onClick = {
                    val snapshot = entries.toList()
                    shareInProgress = true
                    coroutineScope.launch {
                        try {
                            val file = withContext(Dispatchers.IO) {
                                writeAutomationLogFile(context, snapshot)
                            }
                            shareAutomationLogFile(context, file)
                        } catch (e: Exception) {
                            Toast.makeText(
                                context,
                                "Could not create log file: ${e.message ?: "unknown error"}",
                                Toast.LENGTH_LONG,
                            ).show()
                        } finally {
                            shareInProgress = false
                        }
                    }
                },
            ) {
                Text(if (shareInProgress) "Preparing…" else "Share .txt")
            }
            TextButton(onClick = { AutomationLog.clear() }) {
                Text("Clear")
            }
        }

        HorizontalDivider(modifier = Modifier.padding(vertical = 8.dp))

        if (entries.isEmpty()) {
            Text(
                text = "No entries yet. Start a task from the Accessibility tab and the steps will appear here.",
                style = MaterialTheme.typography.bodyMedium
            )
        } else {
            LazyColumn(
                state = listState,
                modifier = Modifier.fillMaxSize()
            ) {
                items(items = entries, key = { it.id }) { entry ->
                    LogRow(
                        entry = entry,
                        onOpenDump = onOpenDump,
                        onShareDump = shareDump,
                        shareEnabled = !shareInProgress,
                        shareInProgress = sharingDumpEntryId == entry.id,
                    )
                }
            }
        }
    }
}

/** Writes UTF-8 text under the only cache directory exposed by the app's FileProvider. */
private fun writeSharedTextFile(context: Context, fileName: String, content: String): File {
    val directory = File(context.cacheDir, "shared_logs")
    check(directory.exists() || directory.mkdirs()) {
        "Could not create the shared log directory"
    }
    return File(directory, fileName).apply {
        writeText(content, Charsets.UTF_8)
    }
}

/** Writes the complete retained log, including structured node dumps, to app-private cache. */
private fun writeAutomationLogFile(
    context: Context,
    entries: List<AutomationLog.Entry>,
): File = writeSharedTextFile(
    context = context,
    fileName = "automation-log-${System.currentTimeMillis()}.txt",
    content = AutomationLog.plainText(entries),
)

/** Writes one standalone structured node dump, including its containing log metadata. */
private fun writeWindowDumpFile(context: Context, entry: AutomationLog.Entry): File {
    val dump = checkNotNull(entry.windowDump) { "The selected log entry has no node dump" }
    val content = buildString {
        appendLine("${entry.timestamp} ${entry.message}")
        append(AutomationLog.windowDumpPlainText(dump))
        appendLine()
    }
    return writeSharedTextFile(
        context = context,
        fileName = "accessibility-node-dump-${entry.id}-${System.currentTimeMillis()}.txt",
        content = content,
    )
}

/** Shares a cache-backed text file through a temporary read-only content URI. */
private fun shareTextFile(
    context: Context,
    file: File,
    subject: String,
    chooserTitle: String,
) {
    val uri = FileProvider.getUriForFile(
        context,
        "${context.packageName}.fileprovider",
        file,
    )
    val sendIntent = Intent(Intent.ACTION_SEND).apply {
        type = "text/plain"
        putExtra(Intent.EXTRA_STREAM, uri)
        putExtra(Intent.EXTRA_SUBJECT, subject)
        clipData = ClipData.newRawUri(subject, uri)
        addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION)
    }
    context.startActivity(Intent.createChooser(sendIntent, chooserTitle))
}

private fun shareAutomationLogFile(context: Context, file: File) {
    shareTextFile(context, file, "Automation log", "Share automation log")
}

/** Prepares one immutable dump snapshot off the main thread, then opens Android's share sheet. */
private suspend fun shareWindowDumpEntry(context: Context, entry: AutomationLog.Entry) {
    val file = withContext(Dispatchers.IO) { writeWindowDumpFile(context, entry) }
    shareTextFile(context, file, "Accessibility node dump", "Share node dump")
}

/** Renders one selectable log row and its optional inline failure screenshot. */
@Composable
private fun LogRow(
    entry: AutomationLog.Entry,
    onOpenDump: (Long) -> Unit,
    onShareDump: (AutomationLog.Entry) -> Unit,
    shareEnabled: Boolean,
    shareInProgress: Boolean,
) {
    val colors = MaterialTheme.colorScheme
    val color = when (entry.kind) {
        AutomationLog.Kind.RUN, AutomationLog.Kind.RUN_END -> colors.primary
        AutomationLog.Kind.SECTION -> colors.tertiary
        AutomationLog.Kind.ERROR -> colors.error
        AutomationLog.Kind.INFO -> colors.onSurface
    }
    val weight = when (entry.kind) {
        AutomationLog.Kind.RUN -> FontWeight.Bold
        AutomationLog.Kind.SECTION, AutomationLog.Kind.RUN_END -> FontWeight.SemiBold
        else -> FontWeight.Normal
    }
    val prefix = when (entry.kind) {
        AutomationLog.Kind.RUN -> "▶ "
        AutomationLog.Kind.RUN_END -> "■ "
        else -> ""
    }

    Column(modifier = Modifier.fillMaxWidth()) {
        if (entry.kind == AutomationLog.Kind.RUN) {
            HorizontalDivider(
                thickness = 2.dp,
                color = colors.primary,
                modifier = Modifier.padding(top = 12.dp, bottom = 4.dp)
            )
        }

        SelectionContainer {
            Row(modifier = Modifier.padding(vertical = 2.dp)) {
                Text(
                    text = entry.timestamp,
                    style = MaterialTheme.typography.bodySmall,
                    fontFamily = FontFamily.Monospace,
                    color = colors.onSurfaceVariant
                )
                Spacer(modifier = Modifier.width(8.dp))
                Text(
                    text = "$prefix${entry.message}",
                    style = MaterialTheme.typography.bodySmall,
                    fontFamily = FontFamily.Monospace,
                    fontWeight = weight,
                    color = color,
                    modifier = Modifier.weight(1f)
                )
            }
        }

        entry.windowDump?.let { dump ->
            Row(modifier = Modifier.padding(start = 40.dp)) {
                TextButton(onClick = { onOpenDump(entry.id) }) {
                    Text(
                        "View node dump (${dump.nodes.size}${if (dump.truncated) "+" else ""})"
                    )
                }
                TextButton(
                    enabled = shareEnabled,
                    onClick = { onShareDump(entry) },
                ) {
                    Text(if (shareInProgress) "Preparing…" else "Share dump")
                }
            }
        }

        when (val screenshot = entry.screenshot) {
            AutomationLog.ScreenshotState.Pending -> Text(
                text = "Capturing failure screenshot…",
                style = MaterialTheme.typography.bodySmall,
                color = colors.onSurfaceVariant,
                modifier = Modifier.padding(start = 8.dp, bottom = 6.dp)
            )
            is AutomationLog.ScreenshotState.Ready -> Image(
                bitmap = screenshot.bitmap.asImageBitmap(),
                contentDescription = "Screen captured when the task failed",
                contentScale = ContentScale.Fit,
                modifier = Modifier
                    .fillMaxWidth()
                    .heightIn(max = 420.dp)
                    .padding(vertical = 6.dp)
            )
            is AutomationLog.ScreenshotState.Unavailable -> Text(
                text = "Screenshot unavailable: ${screenshot.reason}",
                style = MaterialTheme.typography.bodySmall,
                color = colors.error,
                modifier = Modifier.padding(start = 8.dp, bottom = 6.dp)
            )
            AutomationLog.ScreenshotState.Released -> Text(
                text = "Screenshot released to limit memory use",
                style = MaterialTheme.typography.bodySmall,
                color = colors.onSurfaceVariant,
                modifier = Modifier.padding(start = 8.dp, bottom = 6.dp)
            )
            null -> Unit
        }
    }
}

/** Dedicated, selectable and scrollable view for one structured accessibility hierarchy. */
@Composable
private fun DumpDetailScreen(
    entry: AutomationLog.Entry?,
    onBack: () -> Unit,
    modifier: Modifier = Modifier,
) {
    val dump = entry?.windowDump
    val context = LocalContext.current
    val coroutineScope = rememberCoroutineScope()
    var shareInProgress by remember(entry?.id) { mutableStateOf(false) }

    Column(
        modifier = modifier
            .fillMaxSize()
            .padding(16.dp)
    ) {
        Row(
            modifier = Modifier.fillMaxWidth(),
            verticalAlignment = Alignment.CenterVertically,
        ) {
            TextButton(onClick = onBack) {
                Text("‹ Logging")
            }
            Text(
                text = "Accessibility node dump",
                style = MaterialTheme.typography.titleMedium,
                modifier = Modifier.weight(1f),
            )
            TextButton(
                enabled = dump != null,
                onClick = {
                    val currentDump = dump ?: return@TextButton
                    val clipboard = context.getSystemService(Context.CLIPBOARD_SERVICE) as ClipboardManager
                    clipboard.setPrimaryClip(
                        ClipData.newPlainText(
                            "Accessibility node dump",
                            AutomationLog.windowDumpPlainText(currentDump),
                        )
                    )
                    Toast.makeText(context, "Dump copied", Toast.LENGTH_SHORT).show()
                }
            ) {
                Text("Copy")
            }
            TextButton(
                enabled = entry != null && dump != null && !shareInProgress,
                onClick = {
                    val currentEntry = entry ?: return@TextButton
                    val currentDump = dump ?: return@TextButton
                    val snapshot = currentEntry.copy(
                        windowDump = currentDump.copy(nodes = currentDump.nodes.toList())
                    )
                    shareInProgress = true
                    coroutineScope.launch {
                        try {
                            shareWindowDumpEntry(context, snapshot)
                        } catch (e: Exception) {
                            Toast.makeText(
                                context,
                                "Could not create dump file: ${e.message ?: "unknown error"}",
                                Toast.LENGTH_LONG,
                            ).show()
                        } finally {
                            shareInProgress = false
                        }
                    }
                },
            ) {
                Text(if (shareInProgress) "Preparing…" else "Share .txt")
            }
        }

        HorizontalDivider(modifier = Modifier.padding(bottom = 12.dp))

        if (entry == null || dump == null) {
            Text(
                text = "This dump is no longer available. It may have been cleared or evicted.",
                style = MaterialTheme.typography.bodyMedium,
                color = MaterialTheme.colorScheme.onSurfaceVariant,
            )
            return@Column
        }

        LazyColumn(modifier = Modifier.fillMaxSize()) {
            item {
                SelectionContainer {
                    Column(modifier = Modifier.fillMaxWidth()) {
                        Text(
                            text = dump.reason,
                            style = MaterialTheme.typography.titleSmall,
                            fontWeight = FontWeight.SemiBold,
                        )
                        Spacer(modifier = Modifier.height(8.dp))
                        DumpMetadataLine("Captured", entry.timestamp)
                        DumpMetadataLine("Window", dump.windowPackage)
                        DumpMetadataLine("Root bounds", dump.rootBounds.shortString())
                        DumpMetadataLine("Nodes", dump.nodes.size.toString())
                        DumpMetadataLine(
                            "Traversal",
                            if (dump.truncated) "Truncated at the safety limit" else "Complete",
                        )
                    }
                }
                HorizontalDivider(modifier = Modifier.padding(vertical = 12.dp))
            }

            itemsIndexed(dump.nodes) { index, node ->
                DumpNodeRow(index = index, node = node)
                if (index < dump.nodes.lastIndex) {
                    HorizontalDivider(modifier = Modifier.padding(vertical = 6.dp))
                }
            }
        }
    }
}

@Composable
private fun DumpMetadataLine(label: String, value: String) {
    Row(modifier = Modifier.padding(vertical = 2.dp)) {
        Text(
            text = "$label:",
            style = MaterialTheme.typography.bodySmall,
            fontWeight = FontWeight.SemiBold,
            modifier = Modifier.width(92.dp),
        )
        Text(
            text = value,
            style = MaterialTheme.typography.bodySmall,
            fontFamily = FontFamily.Monospace,
            modifier = Modifier.weight(1f),
        )
    }
}

@Composable
private fun DumpNodeRow(index: Int, node: AutomationLog.DumpNode) {
    val colors = MaterialTheme.colorScheme
    val indent = (node.depth * 12).coerceAtMost(72).dp
    SelectionContainer {
        Column(
            modifier = Modifier
                .fillMaxWidth()
                .padding(start = indent, top = 3.dp, bottom = 3.dp)
        ) {
            Row(verticalAlignment = Alignment.CenterVertically) {
                Text(
                    text = "#${index + 1}  ${node.className}",
                    style = MaterialTheme.typography.bodyMedium,
                    fontFamily = FontFamily.Monospace,
                    fontWeight = FontWeight.SemiBold,
                    modifier = Modifier.weight(1f),
                )
                if (node.clickable) {
                    Text(
                        text = "CLICKABLE",
                        style = MaterialTheme.typography.labelSmall,
                        color = colors.primary,
                    )
                }
            }
            Text(
                text = "depth=${node.depth}  bounds=${node.bounds.shortString()}",
                style = MaterialTheme.typography.bodySmall,
                fontFamily = FontFamily.Monospace,
                color = colors.onSurfaceVariant,
            )
            if (node.text.isNotEmpty()) DumpNodeField("text", node.text)
            if (node.contentDescription.isNotEmpty()) {
                DumpNodeField("description", node.contentDescription)
            }
            if (node.viewId.isNotEmpty()) DumpNodeField("id", node.viewId)
        }
    }
}

@Composable
private fun DumpNodeField(label: String, value: String) {
    Text(
        text = "$label: $value",
        style = MaterialTheme.typography.bodySmall,
        fontFamily = FontFamily.Monospace,
        modifier = Modifier.padding(top = 2.dp),
    )
}

@Composable
fun DeviceControlsScreen(modifier: Modifier = Modifier) {
    val context = LocalContext.current
    var isFlashlightOn by remember { mutableStateOf(false) }

    // Permission launcher for flashlight
    val flashlightPermissionLauncher = rememberLauncherForActivityResult(
        contract = ActivityResultContracts.RequestPermission()
    ) { isGranted ->
        if (isGranted) {
            isFlashlightOn = !isFlashlightOn
            DeviceUtils.toggleFlashlight(context, isFlashlightOn)
        }
    }

    // Permission launcher specifically for opening camera
    val openCameraLauncher = rememberLauncherForActivityResult(
        contract = ActivityResultContracts.RequestPermission()
    ) { isGranted ->
        if (isGranted) {
            DeviceUtils.openCamera(context)
        }
    }

    // Check flashlight availability
    val isFlashlightAvailable = remember {
        DeviceUtils.isFlashlightAvailable(context)
    }

    Column(
        modifier = modifier
            .fillMaxSize()
            .padding(16.dp),
        horizontalAlignment = Alignment.CenterHorizontally,
        verticalArrangement = Arrangement.Center
    ) {
        Text(
            text = "Device Controls",
            modifier = Modifier.padding(bottom = 32.dp)
        )

        // Flashlight Button
        if (isFlashlightAvailable) {
            Button(
                onClick = {
                    // Check if we have camera permission (needed for flashlight)
                    if (ContextCompat.checkSelfPermission(context, Manifest.permission.CAMERA)
                        == PackageManager.PERMISSION_GRANTED) {
                        // Permission already granted, toggle flashlight
                        isFlashlightOn = !isFlashlightOn
                        DeviceUtils.toggleFlashlight(context, isFlashlightOn)
                    } else {
                        // Request permission
                        flashlightPermissionLauncher.launch(Manifest.permission.CAMERA)
                    }
                },
                modifier = Modifier
                    .fillMaxWidth()
                    .height(56.dp)
            ) {
                Icon(
                    imageVector = Icons.Default.Favorite,
                    contentDescription = "Flashlight",
                    modifier = Modifier.padding(end = 8.dp)
                )
                Text(if (isFlashlightOn) "Turn Off Flashlight" else "Turn On Flashlight")
            }
        } else {
            Text(
                text = "Flashlight not available",
                modifier = Modifier.padding(bottom = 16.dp)
            )
        }

        Spacer(modifier = Modifier.height(16.dp))

        // Camera Button
        Button(
            onClick = {
                // Check if we have camera permission
                if (ContextCompat.checkSelfPermission(context, Manifest.permission.CAMERA)
                    == PackageManager.PERMISSION_GRANTED) {
                    // Permission already granted, open camera
                    DeviceUtils.openCamera(context)
                } else {
                    // Request permission
                    openCameraLauncher.launch(Manifest.permission.CAMERA)
                }
            },
            modifier = Modifier
                .fillMaxWidth()
                .height(56.dp)
        ) {
            Icon(
                imageVector = Icons.Default.Home,
                contentDescription = "Camera",
                modifier = Modifier.padding(end = 8.dp)
            )
            Text("Open Camera")
        }

        Spacer(modifier = Modifier.height(16.dp))

        // Amap Navigation Button
        Button(
            onClick = {
                // Open Amap navigation to a default destination (you can customize this)
                DeviceUtils.openAmapNavigation(context, "北京市天安门")
            },
            modifier = Modifier
                .fillMaxWidth()
                .height(56.dp)
        ) {
            Icon(
                imageVector = Icons.Default.AccountBox,
                contentDescription = "Navigation",
                modifier = Modifier.padding(end = 8.dp)
            )
            Text("Open Amap Navigation")
        }

        Spacer(modifier = Modifier.height(16.dp))

        // Amap Navigation with Coordinates Button
        Button(
            onClick = {
                // Example: Navigate to Beijing (39.9042, 116.4074)
                DeviceUtils.openAmapNavigation(
                    context,
                    latitude = 39.9042,
                    longitude = 116.4074,
                    poiName = "天安门"
                )
            },
            modifier = Modifier
                .fillMaxWidth()
                .height(56.dp)
        ) {
            Icon(
                imageVector = Icons.Default.AccountBox,
                contentDescription = "Navigation",
                modifier = Modifier.padding(end = 8.dp)
            )
            Text("Navigate to Coordinates")
        }
    }
}

@Composable
fun AccessibilityScreen(modifier: Modifier = Modifier) {
    val context = LocalContext.current
    val activeMode by AutomationLog.activeMode.collectAsState()
    val skipTextsRaw by AutomationSettings.skipTextsRaw.collectAsState()
    val skipTexts by AutomationSettings.skipTexts.collectAsState()
    val whitelistTextsRaw by AutomationSettings.whitelistTextsRaw.collectAsState()
    val whitelistTexts by AutomationSettings.whitelistTexts.collectAsState()

    Column(
        modifier = modifier
            .fillMaxSize()
            .verticalScroll(rememberScrollState())
            .padding(16.dp),
        horizontalAlignment = Alignment.CenterHorizontally
    ) {
        Text(
            text = "Accessibility Service",
            style = MaterialTheme.typography.titleMedium,
            modifier = Modifier.padding(vertical = 16.dp)
        )

        Button(
            onClick = {
                context.startActivity(Intent(Settings.ACTION_ACCESSIBILITY_SETTINGS).apply {
                    addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
                })
            },
            modifier = Modifier.fillMaxWidth().height(56.dp)
        ) {
            Text("Open Accessibility Settings")
        }

        Spacer(modifier = Modifier.height(16.dp))

        AutomationModeButton(
            context = context,
            mode = AutomationMode.COLLECT_AWARDS,
            activeMode = activeMode,
        )

        Spacer(modifier = Modifier.height(12.dp))

        AutomationModeButton(
            context = context,
            mode = AutomationMode.UNLIKE_UNFOLLOW,
            activeMode = activeMode,
        )

        Spacer(modifier = Modifier.height(8.dp))

        Button(
            onClick = {
                context.startService(
                    Intent(context, LauncherAccessibilityService::class.java).apply {
                        action = LauncherAccessibilityService.ACTION_SHOW_DUMP_TOOL
                    }
                )
            },
            modifier = Modifier.fillMaxWidth().height(48.dp),
        ) {
            Text("Start Dump")
        }
        Text(
            text = "Shows draggable floating Close / Dump icons for optional diagnostics. " +
                    "Unlike & Unfollow now detects video/article details and processes them automatically.",
            style = MaterialTheme.typography.bodySmall,
            color = MaterialTheme.colorScheme.onSurfaceVariant,
            modifier = Modifier.fillMaxWidth().padding(top = 4.dp),
        )

        HorizontalDivider(modifier = Modifier.padding(vertical = 24.dp))

        Text(
            text = "Non-skip text match (whitelist)",
            style = MaterialTheme.typography.titleSmall,
            modifier = Modifier.align(Alignment.Start)
        )
        Text(
            text = "One entry per line, or separated by commas. Matches the task title or description " +
                    "on the left side. A match always runs the task, overriding every skip rule.",
            style = MaterialTheme.typography.bodySmall,
            color = MaterialTheme.colorScheme.onSurfaceVariant,
            modifier = Modifier.align(Alignment.Start).padding(top = 4.dp, bottom = 8.dp)
        )
        OutlinedTextField(
            value = whitelistTextsRaw,
            onValueChange = { AutomationSettings.setWhitelistTextsRaw(it) },
            label = { Text("Non-skip texts") },
            placeholder = { Text(AutomationSettings.DEFAULT_WHITELIST) },
            minLines = 3,
            maxLines = 6,
            modifier = Modifier.fillMaxWidth()
        )
        Text(
            text = if (whitelistTexts.isEmpty()) {
                "Whitelist is empty — no task overrides skip rules."
            } else {
                "${whitelistTexts.size} entr${if (whitelistTexts.size == 1) "y" else "ies"}: " +
                        whitelistTexts.joinToString(" · ")
            },
            style = MaterialTheme.typography.bodySmall,
            color = MaterialTheme.colorScheme.onSurfaceVariant,
            modifier = Modifier.align(Alignment.Start).padding(top = 8.dp)
        )

        HorizontalDivider(modifier = Modifier.padding(vertical = 24.dp))

        Text(
            text = "Skip text match",
            style = MaterialTheme.typography.titleSmall,
            modifier = Modifier.align(Alignment.Start)
        )
        Text(
            text = "One entry per line, or separated by commas. Matched against each task's title and " +
                    "its button. 去微信, 去参与 and 去浏览 are normally skipped, except for supported " +
                    "dedicated flows such as registered WeChat mini-program offers and 天天领现金-浏览笔记.",
            style = MaterialTheme.typography.bodySmall,
            color = MaterialTheme.colorScheme.onSurfaceVariant,
            modifier = Modifier.align(Alignment.Start).padding(top = 4.dp, bottom = 8.dp)
        )
        OutlinedTextField(
            value = skipTextsRaw,
            onValueChange = { AutomationSettings.setSkipTextsRaw(it) },
            label = { Text("Skip texts") },
            placeholder = { Text("去QQ阅读\n百度\n去领取") },
            minLines = 3,
            maxLines = 6,
            modifier = Modifier.fillMaxWidth()
        )
        Text(
            text = if (skipTexts.isEmpty()) {
                "No custom entries — only the built-in ones are skipped."
            } else {
                "${skipTexts.size} entr${if (skipTexts.size == 1) "y" else "ies"}: " +
                        skipTexts.joinToString(" · ")
            },
            style = MaterialTheme.typography.bodySmall,
            color = MaterialTheme.colorScheme.onSurfaceVariant,
            modifier = Modifier.align(Alignment.Start).padding(top = 8.dp, bottom = 24.dp)
        )
    }
}

@Composable
private fun AutomationModeButton(
    context: Context,
    mode: AutomationMode,
    activeMode: AutomationMode?,
) {
    val isRunning = activeMode == mode
    val anotherModeRunning = activeMode != null && !isRunning
    Button(
        onClick = {
            context.startService(
                Intent(context, LauncherAccessibilityService::class.java).apply {
                    if (isRunning) {
                        action = LauncherAccessibilityService.ACTION_STOP_AUTOMATION
                    } else {
                        action = LauncherAccessibilityService.ACTION_START_AUTOMATION
                        putExtra(
                            LauncherAccessibilityService.EXTRA_AUTOMATION_MODE,
                            mode.wireValue,
                        )
                        putExtra(LauncherAccessibilityService.EXTRA_TARGET_LABEL, "携程旅行")
                    }
                }
            )
        },
        enabled = !anotherModeRunning,
        colors = if (isRunning) {
            ButtonDefaults.buttonColors(
                containerColor = MaterialTheme.colorScheme.error,
                contentColor = MaterialTheme.colorScheme.onError,
            )
        } else {
            ButtonDefaults.buttonColors()
        },
        modifier = Modifier.fillMaxWidth().height(56.dp),
    ) {
        Text(if (isRunning) "Stop ${mode.displayName}" else "Start ${mode.displayName}")
    }
    Text(
        text = when {
            isRunning -> "Running — tap the same button to stop"
            anotherModeRunning -> "${activeMode?.displayName} is running"
            else -> "Idle"
        },
        style = MaterialTheme.typography.bodySmall,
        color = MaterialTheme.colorScheme.onSurfaceVariant,
        modifier = Modifier.fillMaxWidth().padding(top = 4.dp),
    )
}

@Composable
fun Greeting(name: String, modifier: Modifier = Modifier) {
    Text(
        text = "Hello $name!",
        modifier = modifier
    )
}

@Preview(showBackground = true)
@Composable
fun GreetingPreview() {
    MyApplicationTheme {
        Greeting("Android")
    }
}
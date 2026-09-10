package com.example.myapplication

import android.view.accessibility.AccessibilityNodeInfo

object SearchUtils {
    /**
     * Find an AccessibilityNodeInfo matching any of the provided target strings.
     * - checks text and contentDescription (case-insensitive, exact or substring)
     * - prefers clickable nodes, or their clickable parent
     * - safe against exceptions in traversal
     */
    fun findNodeByTexts(root: AccessibilityNodeInfo?, targets: List<String>): AccessibilityNodeInfo? {
        if (root == null) return null

        // 1) try findAccessibilityNodeInfosByText for each target and prefer clickable
        for (t in targets) {
            try {
                val found = root.findAccessibilityNodeInfosByText(t)
                if (!found.isNullOrEmpty()) {
                    for (n in found) {
                        try {
                            val txt = n.text?.toString() ?: n.contentDescription?.toString() ?: ""
                            if (txt.equals(t, ignoreCase = true) || txt.contains(t, ignoreCase = true)) {
                                if (n.isClickable) return n
                                n.parent?.let { if (it.isClickable) return it }
                                return n
                            }
                        } catch (_: Exception) {
                        }
                    }
                }
            } catch (_: Exception) {
            }
        }

        // 2) Full BFS through tree checking text/contentDescription substrings
        val q = ArrayDeque<AccessibilityNodeInfo>()
        q.add(root)
        while (q.isNotEmpty()) {
            val n = q.removeFirst()
            try {
                val txt = n.text?.toString() ?: n.contentDescription?.toString() ?: ""
                for (t in targets) {
                    if (txt.equals(t, ignoreCase = true) || txt.contains(t, ignoreCase = true)) {
                        if (n.isClickable) return n
                        n.parent?.let { if (it.isClickable) return it }
                        return n
                    }
                }
                for (i in 0 until n.childCount) n.getChild(i)?.let { q.add(it) }
            } catch (_: Exception) {
            }
        }

        return null
    }

    // (no vararg overload to avoid unused-function warnings)

    /**
     * Vararg convenience overload — allows calling with multiple targets directly.
     * Example: SearchUtils.findNodeByTexts(root, "我的", "我的tab")
     */
    fun findNodeByTexts(root: AccessibilityNodeInfo?, vararg targets: String): AccessibilityNodeInfo? =
        findNodeByTexts(root, targets.toList())
}

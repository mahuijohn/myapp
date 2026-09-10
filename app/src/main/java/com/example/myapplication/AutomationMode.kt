package com.example.myapplication

enum class AutomationMode(
    val wireValue: String,
    val displayName: String,
) {
    COLLECT_AWARDS("collect_awards", "Collect Awards"),
    UNLIKE_UNFOLLOW("unlike_unfollow", "Unlike & Unfollow");

    companion object {
        fun fromWireValue(value: String?): AutomationMode? =
            entries.firstOrNull { it.wireValue == value }
    }
}

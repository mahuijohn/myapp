package com.example.myapplication.utils

import android.content.Context
import android.content.Intent
import android.hardware.camera2.CameraManager
import android.net.Uri
import android.provider.MediaStore
import androidx.core.content.ContextCompat

object DeviceUtils {
    
    /**
     * Toggle flashlight on/off
     */
    fun toggleFlashlight(context: Context, isOn: Boolean): Boolean {
        return try {
            val cameraManager = context.getSystemService(Context.CAMERA_SERVICE) as CameraManager
            val cameraId = cameraManager.cameraIdList[0]
            cameraManager.setTorchMode(cameraId, isOn)
            true
        } catch (e: Exception) {
            e.printStackTrace()
            false
        }
    }
    
    /**
     * Check if flashlight is available
     */
    fun isFlashlightAvailable(context: Context): Boolean {
        return try {
            val cameraManager = context.getSystemService(Context.CAMERA_SERVICE) as CameraManager
            cameraManager.cameraIdList.isNotEmpty() && 
            cameraManager.getCameraCharacteristics(cameraManager.cameraIdList[0])
                .get(android.hardware.camera2.CameraCharacteristics.FLASH_INFO_AVAILABLE) == true
        } catch (e: Exception) {
            false
        }
    }
    
    /**
     * Open camera app
     */
    fun openCamera(context: Context) {
        val intent = Intent(MediaStore.ACTION_IMAGE_CAPTURE)
        if (intent.resolveActivity(context.packageManager) != null) {
            ContextCompat.startActivity(context, intent, null)
        }
    }
    
    /**
     * Open Amap (高德地图) for navigation
     * @param destination Destination address or coordinates (e.g., "北京市天安门" or "39.9042,116.4074")
     */
    fun openAmapNavigation(context: Context, destination: String = "") {
        try {
            // Try to open Amap app first
            val amapIntent = Intent().apply {
                action = Intent.ACTION_VIEW
                data = Uri.parse("androidamap://navi?sourceApplication=myapp&poiname=$destination&lat=&lon=&dev=0")
                setPackage("com.autonavi.minimap")
            }
            
            if (amapIntent.resolveActivity(context.packageManager) != null) {
                ContextCompat.startActivity(context, amapIntent, null)
            } else {
                // If Amap is not installed, try to open in browser or show a message
                // You can also open Google Maps or other map apps as fallback
                val webIntent = Intent(Intent.ACTION_VIEW).apply {
                    data = Uri.parse("https://uri.amap.com/navigation?to=$destination")
                }
                if (webIntent.resolveActivity(context.packageManager) != null) {
                    ContextCompat.startActivity(context, webIntent, null)
                }
            }
        } catch (e: Exception) {
            e.printStackTrace()
        }
    }
    
    /**
     * Open Amap with specific coordinates for navigation
     */
    fun openAmapNavigation(context: Context, latitude: Double, longitude: Double, poiName: String = "") {
        try {
            val amapIntent = Intent().apply {
                action = Intent.ACTION_VIEW
                data = Uri.parse("androidamap://navi?sourceApplication=myapp&poiname=$poiName&lat=$latitude&lon=$longitude&dev=0")
                setPackage("com.autonavi.minimap")
            }
            
            if (amapIntent.resolveActivity(context.packageManager) != null) {
                ContextCompat.startActivity(context, amapIntent, null)
            } else {
                val webIntent = Intent(Intent.ACTION_VIEW).apply {
                    data = Uri.parse("https://uri.amap.com/navigation?to=$longitude,$latitude&toname=$poiName")
                }
                if (webIntent.resolveActivity(context.packageManager) != null) {
                    ContextCompat.startActivity(context, webIntent, null)
                }
            }
        } catch (e: Exception) {
            e.printStackTrace()
        }
    }
}


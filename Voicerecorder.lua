require "import"
import "android.media.MediaRecorder"
import "android.media.MediaPlayer"
import "android.media.AudioManager"
import "android.media.AudioRecord"
import "android.media.AudioFormat"
import "android.media.audiofx.AutomaticGainControl"
import "android.os.Environment"
import "android.os.Handler"
import "android.os.Looper"
import "android.app.AlertDialog"
import "android.widget.EditText"
import "android.widget.TextView"
import "android.widget.Button"
import "android.widget.LinearLayout"
import "android.widget.ScrollView"
import "android.content.Context"
import "android.content.Intent"
import "android.net.Uri"
import "android.content.ContentValues"
import "android.provider.MediaStore"
import "android.content.ContentUris"
import "android.content.ClipData"
import "android.view.WindowManager"
import "android.view.ViewGroup"
import "android.view.Gravity"
import "android.os.Build"
import "android.os.StrictMode"
import "android.os.Vibrator"
import "android.os.VibrationEffect"
import "java.io.File"
import "java.io.FileOutputStream"
import "java.io.FileInputStream"
import "java.io.RandomAccessFile"
import "java.io.BufferedReader"
import "java.io.InputStreamReader"
import "java.net.URL"
import "java.net.HttpURLConnection"
import "java.lang.Thread"
import "java.lang.Runnable"
import "java.lang.String"
import "java.lang.reflect.Array"
import "java.lang.Byte"
import "java.text.SimpleDateFormat"
import "java.util.Date"
import "java.util.Locale"
import "org.json.JSONObject"

local mainHandler = Handler(Looper.getMainLooper())

local APP_TITLE = "Perekam Suara by Novan"
local SCRIPT_VERSION = "1.2"
local UPDATE_URL = "https://raw.githubusercontent.com/novanblind/Perekam-suara/main/Voicerecorder.lua"

-- Status runtime perekam & pemutar
_G.voiceRecorderState = _G.voiceRecorderState or {
  recorder = nil,
  audioRecord = nil,
  recordThread = nil,
  agcEffect = nil,
  timerRunnable = nil,
  isWav = false,
  pcmTotalBytes = 0,
  pcmSampleRate = 44100,
  pcmChannels = 1,
  player = nil,
  isRecording = false,
  isPaused = false,
  isPlaying = false,
  currentFilePath = nil,
  lastRecordedPath = nil
}
local state = _G.voiceRecorderState

-- Referensi dialog overlay yang sedang aktif di layar
local activeOverlayDialog = nil

-- ====================================================================
-- SISTEM PENYIMPANAN PENGATURAN PERMANEN
-- ====================================================================
local sp = service.getSharedPreferences("voice_recorder_config", Context.MODE_PRIVATE)
local backupConfigFile = File(service.getFilesDir(), "voice_recorder_settings.json")

local function savePref(key, value)
  local strVal = tostring(value)
  pcall(function()
    sp.edit().putString(key, strVal).commit()
  end)

  pcall(function()
    local json = JSONObject()
    if backupConfigFile.exists() then
      local fis = FileInputStream(backupConfigFile)
      local reader = BufferedReader(InputStreamReader(fis, "UTF-8"))
      local sb = {}
      local line = reader.readLine()
      while line ~= nil do
        table.insert(sb, line)
        line = reader.readLine()
      end
      reader.close()
      fis.close()
      pcall(function() json = JSONObject(table.concat(sb, "\n")) end)
    end
    json.put(key, strVal)
    local fos = FileOutputStream(backupConfigFile)
    fos.write(String(json.toString()).getBytes("UTF-8"))
    fos.flush()
    fos.close()
  end)
end

local function loadPref(key, defaultVal)
  local result = nil
  pcall(function()
    if sp.contains(key) then
      result = sp.getString(key, tostring(defaultVal))
    end
  end)

  if result == nil or result == "" then
    pcall(function()
      if backupConfigFile.exists() then
        local fis = FileInputStream(backupConfigFile)
        local reader = BufferedReader(InputStreamReader(fis, "UTF-8"))
        local sb = {}
        local line = reader.readLine()
        while line ~= nil do
          table.insert(sb, line)
          line = reader.readLine()
        end
        reader.close()
        fis.close()
        local json = JSONObject(table.concat(sb, "\n"))
        if json.has(key) then
          result = json.optString(key, tostring(defaultVal))
        end
      end
    end)
  end

  if result == nil or result == "" then
    result = tostring(defaultVal)
  end
  return result
end

-- Getter & Setter Pengaturan (Format audio default: MP3)
local function getAudioFormat() return loadPref("audio_format", "mp3") end
local function setAudioFormat(f) savePref("audio_format", f) end

local function getAudioBitrate() return tonumber(loadPref("audio_bitrate", "128000")) or 128000 end
local function setAudioBitrate(b) savePref("audio_bitrate", tostring(b)) end

local function getAudioSampleRate() return tonumber(loadPref("audio_samplerate", "44100")) or 44100 end
local function setAudioSampleRate(r) savePref("audio_samplerate", tostring(r)) end

local function getAudioChannels() return tonumber(loadPref("audio_channels", "1")) or 1 end
local function setAudioChannels(c) savePref("audio_channels", tostring(c)) end

local function getNoiseReduction() return loadPref("noise_reduction", "false") == "true" end
local function setNoiseReduction(n) savePref("noise_reduction", tostring(n)) end

local function getGainControl() return loadPref("gain_control", "false") == "true" end
local function setGainControl(g) savePref("gain_control", tostring(g)) end

local function getRecordTimerSeconds() return tonumber(loadPref("record_timer_sec", "0")) or 0 end
local function setRecordTimerSeconds(s) savePref("record_timer_sec", tostring(s)) end

local function getStopBehavior() return loadPref("stop_behavior", "direct") end
local function setStopBehavior(b) savePref("stop_behavior", b) end

local function getVibrationLevel() return loadPref("vibration_level", "low") end
local function setVibrationLevel(v) savePref("vibration_level", tostring(v)) end

local function getRecordPrefix() return loadPref("record_prefix", "REC") end
local function setRecordPrefix(p) savePref("record_prefix", tostring(p)) end

-- Helper Ukuran Berkas
local function formatFileSize(sizeBytes)
  if not sizeBytes or sizeBytes <= 0 then return "0 B" end
  if sizeBytes < 1024 then return sizeBytes .. " B" end
  if sizeBytes < 1048576 then return string.format("%.1f KB", sizeBytes / 1024) end
  return string.format("%.2f MB", sizeBytes / 1048576)
end

-- Audio Focus Management
local function requestRecorderAudioFocus()
  pcall(function()
    local am = service.getSystemService(Context.AUDIO_SERVICE)
    if am then
      am.requestAudioFocus(nil, AudioManager.STREAM_MUSIC, AudioManager.AUDIOFOCUS_GAIN_TRANSIENT_EXCLUSIVE)
    end
  end)
end

local function abandonRecorderAudioFocus()
  pcall(function()
    local am = service.getSystemService(Context.AUDIO_SERVICE)
    if am then
      am.abandonAudioFocus(nil)
    end
  end)
end

-- Helper Header WAV
local function writeIntLE(raf, val)
  val = math.floor(val or 0)
  raf.write(val % 256)
  raf.write(math.floor(val / 256) % 256)
  raf.write(math.floor(val / 65536) % 256)
  raf.write(math.floor(val / 16777216) % 256)
end

local function writeShortLE(raf, val)
  val = math.floor(val or 0)
  raf.write(val % 256)
  raf.write(math.floor(val / 256) % 256)
end

local function updateWavHeader(filePath, totalAudioLen, sampleRate, channels)
  pcall(function()
    local raf = RandomAccessFile(filePath, "rw")
    raf.seek(0)
    raf.writeBytes("RIFF")
    writeIntLE(raf, totalAudioLen + 36)
    raf.writeBytes("WAVE")
    raf.writeBytes("fmt ")
    writeIntLE(raf, 16)
    writeShortLE(raf, 1)
    writeShortLE(raf, channels)
    writeIntLE(raf, sampleRate)
    local byteRate = sampleRate * channels * 2
    writeIntLE(raf, byteRate)
    writeShortLE(raf, channels * 2)
    writeShortLE(raf, 16)
    raf.writeBytes("data")
    writeIntLE(raf, totalAudioLen)
    raf.close()
  end)
end

-- Helper Getaran
local function triggerVibration(multiplier)
  local level = getVibrationLevel()
  if level == "off" then return end

  local baseMs = 25
  local baseAmp = 40

  if level == "medium" then
    baseMs = 50
    baseAmp = 110
  elseif level == "high" then
    baseMs = 90
    baseAmp = 220
  end

  local mult = multiplier or 1
  local ms = math.floor(baseMs * mult)
  local amp = math.min(255, math.floor(baseAmp * mult))

  pcall(function()
    local vibrator = service.getSystemService(Context.VIBRATOR_SERVICE)
    if vibrator and vibrator.hasVibrator() then
      if Build.VERSION.SDK_INT >= 26 then
        vibrator.vibrate(VibrationEffect.createOneShot(ms, amp))
      else
        vibrator.vibrate(ms)
      end
    end
  end)
end

-- Direktori Penyimpanan
local function getRecordingsDir()
  local dir = File(Environment.getExternalStorageDirectory().getAbsolutePath() .. "/" .. APP_TITLE)
  if not dir.exists() then
    if not dir.mkdirs() then
      dir = File(service.getExternalFilesDir(nil), APP_TITLE)
      if not dir.exists() then dir.mkdirs() end
    end
  end
  return dir
end

-- Dialog Overlay
local function displayOverlayDialog(builder)
  local dialog = builder.create()
  local window = dialog.getWindow()
  if window then
    window.setType(WindowManager.LayoutParams.TYPE_ACCESSIBILITY_OVERLAY)
  end
  dialog.show()
  activeOverlayDialog = dialog
  return dialog
end

-- Deklarasi Fungsi Navigasi
local showSettingsDialog
local showFormatDialog
local showBitrateDialog
local showSampleRateDialog
local showChannelsDialog
local showNoiseReductionDialog
local showGainControlDialog
local showRecordTimerDialog
local showStopBehaviorDialog
local showVibrationDialog
local showPrefixDialog
local showResetConfirmDialog
local showRecordedFileActionDialog
local showPauseDialog
local showHistoryDialog
local checkForUpdate
local stopRecording
local startRecording

-- Pengelola Timer Otomatis
local function clearAutoStopTimer()
  if state.timerRunnable then
    pcall(function() mainHandler.removeCallbacks(state.timerRunnable) end)
    state.timerRunnable = nil
  end
end

local function setupAutoStopTimer()
  clearAutoStopTimer()
  local timerSec = getRecordTimerSeconds()
  if timerSec > 0 then
    state.timerRunnable = Runnable{
      run = function()
        if state.isRecording then
          triggerVibration(1.5)
          service.speak("Batas waktu rekaman tercapai. Rekaman otomatis disimpan.")
          stopRecording()
        end
      end
    }
    mainHandler.postDelayed(state.timerRunnable, timerSec * 1000)
  end
end

-- Helper Pembaruan Script
local function getCurrentScriptFile()
  local info = debug.getinfo(1, "S")
  if info and info.source and info.source:sub(1, 1) == "@" then
    local path = info.source:sub(2)
    local f = File(path)
    if f.exists() and f.isFile() then
      return f
    end
  end
  return nil
end

local function compareVersions(v1, v2)
  local p1 = {}
  for num in tostring(v1):gmatch("%d+") do table.insert(p1, tonumber(num)) end
  local p2 = {}
  for num in tostring(v2):gmatch("%d+") do table.insert(p2, tonumber(num)) end
  local len = math.max(#p1, #p2)
  for i = 1, len do
    local n1 = p1[i] or 0
    local n2 = p2[i] or 0
    if n1 > n2 then return 1 end
    if n1 < n2 then return -1 end
  end
  return 0
end

local function openUrlInBrowser(urlStr)
  pcall(function()
    local intent = Intent(Intent.ACTION_VIEW, Uri.parse(urlStr))
    intent.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
    service.startActivity(intent)
  end)
end

checkForUpdate = function()
  service.speak("Memeriksa versi baru...")
  triggerVibration(0.8)

  Thread(Runnable{
    run = function()
      local success = false
      local responseText = nil
      local errMsg = nil

      pcall(function()
        local url = URL(UPDATE_URL)
        local conn = url.openConnection()
        conn.setRequestMethod("GET")
        conn.setConnectTimeout(10000)
        conn.setReadTimeout(10000)
        conn.setUseCaches(false)
        conn.setRequestProperty("User-Agent", "Mozilla/5.0 (Android)")
        conn.connect()

        local responseCode = conn.getResponseCode()
        if responseCode == 200 then
          local is = conn.getInputStream()
          local reader = BufferedReader(InputStreamReader(is, "UTF-8"))
          local sb = {}
          local line = reader.readLine()
          while line ~= nil do
            table.insert(sb, line)
            line = reader.readLine()
          end
          reader.close()
          is.close()
          responseText = table.concat(sb, "\n")
          success = true
        else
          errMsg = "HTTP " .. responseCode
        end
        conn.disconnect()
      end)

      mainHandler.post(Runnable{
        run = function()
          if not success or not responseText or responseText == "" then
            triggerVibration(1.0)
            service.speak("Gagal memeriksa pembaruan. Pastikan ada koneksi internet.")
            return
          end

          local remoteVersion = responseText:match('SCRIPT_VERSION%s*=%s*"([^"]+)"')
            or responseText:match('CURRENT_VERSION%s*=%s*"([^"]+)"')
            or responseText:match('VERSION%s*=%s*"([^"]+)"')

          local hasUpdate = false
          if remoteVersion then
            hasUpdate = (compareVersions(remoteVersion, SCRIPT_VERSION) > 0)
          else
            local curFile = getCurrentScriptFile()
            if curFile and curFile.exists() then
              if math.abs(curFile.length() - #responseText) > 10 then
                hasUpdate = true
                remoteVersion = "Terbaru (Online)"
              end
            end
          end

          if hasUpdate then
            triggerVibration(1.2)
            service.speak("Versi baru ditemukan: " .. tostring(remoteVersion or "Terbaru"))

            local updateBuilder = AlertDialog.Builder(service)
              .setTitle("Pembaruan Tersedia")
              .setMessage(string.format("Versi saat ini: %s\nVersi baru: %s\n\nApakah Anda ingin memperbarui script ini sekarang?", SCRIPT_VERSION, tostring(remoteVersion or "Baru")))
              .setPositiveButton("Perbarui Sekarang", function()
                triggerVibration(1.0)
                service.speak("Sedang mengunduh pembaruan...")

                Thread(Runnable{
                  run = function()
                    local targetFile = getCurrentScriptFile()
                    local updated = false
                    if targetFile and targetFile.canWrite() then
                      pcall(function()
                        local fos = FileOutputStream(targetFile)
                        fos.write(String(responseText).getBytes("UTF-8"))
                        fos.flush()
                        fos.close()
                        updated = true
                      end)
                    end

                    local finishMessage = ""
                    if updated then
                      finishMessage = string.format("Pembaruan versi %s berhasil diunduh dan dipasang.\n\nSilakan jalankan ulang script untuk menerapkan perubahan.", tostring(remoteVersion or "baru"))
                    else
                      local backupFile = File(getRecordingsDir(), "Voicerecorder_Update.lua")
                      pcall(function()
                        local fos = FileOutputStream(backupFile)
                        fos.write(String(responseText).getBytes("UTF-8"))
                        fos.flush()
                        fos.close()
                      end)
                      finishMessage = string.format("Pembaruan versi %s selesai diunduh dan disimpan di:\n%s", tostring(remoteVersion or "baru"), tostring(backupFile.getAbsolutePath()))
                    end

                    mainHandler.post(Runnable{
                      run = function()
                        triggerVibration(1.2)
                        service.speak("Pengunduhan selesai.")
                        local doneBuilder = AlertDialog.Builder(service)
                          .setTitle("Unduhan Selesai")
                          .setMessage(finishMessage)
                          .setPositiveButton("OK", function()
                            triggerVibration(1.0)
                          end)
                        displayOverlayDialog(doneBuilder)
                      end
                    })
                  end
                }).start()
              end)
              .setNeutralButton("Buka Tautan", function()
                triggerVibration(1.0)
                openUrlInBrowser(UPDATE_URL)
              end)
              .setNegativeButton("Nanti", function()
                showSettingsDialog()
              end)

            displayOverlayDialog(updateBuilder)
          else
            triggerVibration(0.8)
            service.speak("Anda sudah menggunakan versi terbaru (v" .. SCRIPT_VERSION .. ").")
            showSettingsDialog()
          end
        end
      })
    end
  }).start()
end

-- Buka File Manager Plus langsung ke folder penyimpanan rekaman
local function openFileManagerPlus(targetDir)
  if activeOverlayDialog then
    pcall(function() activeOverlayDialog.dismiss() end)
    activeOverlayDialog = nil
  end

  local folder = targetDir or getRecordingsDir()
  if folder.isFile() then
    folder = folder.getParentFile()
  end

  if not folder.exists() then
    folder.mkdirs()
  end

  pcall(function()
    local StrictModeClass = luajava.bindClass("android.os.StrictMode")
    local m = StrictModeClass.getDeclaredMethod("disableDeathOnFileUriExposure", nil)
    m.setAccessible(true)
    m.invoke(nil, nil)
  end)
  pcall(function()
    local BuilderClass = luajava.bindClass("android.os.StrictMode$VmPolicy$Builder")
    StrictMode.setVmPolicy(BuilderClass().build())
  end)

  local folderUri = Uri.fromFile(folder)
  local folderPath = tostring(folder.getAbsolutePath())
  local opened = false

  -- 1. Jalur Utama: Target MainActivity dengan URI berkas dan format MIME */*
  pcall(function()
    local intent = Intent(Intent.ACTION_VIEW)
    intent.setClassName("com.alphainventor.filemanager", "com.alphainventor.filemanager.activity.MainActivity")
    intent.setDataAndType(folderUri, "*/*")
    intent.putExtra("path", folderPath)
    intent.putExtra("folder_path", folderPath)
    intent.putExtra("current_path", folderPath)
    intent.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
    service.startActivity(intent)
    opened = true
    service.speak("Membuka folder di File Manager Plus.")
  end)

  -- 2. Jalur Alternatif via package intent
  if not opened then
    pcall(function()
      local intent = Intent(Intent.ACTION_VIEW)
      intent.setPackage("com.alphainventor.filemanager")
      intent.setDataAndType(folderUri, "*/*")
      intent.putExtra("path", folderPath)
      intent.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
      service.startActivity(intent)
      opened = true
      service.speak("Membuka folder di File Manager Plus.")
    end)
  end

  -- 3. Jalur Cadangan Launcher jika pemanggilan intent langsung ditolak
  if not opened then
    pcall(function()
      local pm = service.getPackageManager()
      local launchIntent = pm.getLaunchIntentForPackage("com.alphainventor.filemanager")
      if launchIntent ~= nil then
        launchIntent.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
        service.startActivity(launchIntent)
        opened = true
        service.speak("Membuka File Manager Plus.")
      end
    end)
  end

  -- 4. Jalur Terakhir: Pemilih aplikasi pengelola berkas sistem
  if not opened then
    pcall(function()
      local intent = Intent(Intent.ACTION_VIEW)
      intent.setDataAndType(folderUri, "*/*")
      intent.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
      service.startActivity(Intent.createChooser(intent, "Buka Folder Rekaman").addFlags(Intent.FLAG_ACTIVITY_NEW_TASK))
      opened = true
      service.speak("Membuka pengelola berkas.")
    end)
  end

  if not opened then
    service.speak("Gagal membuka penyimpanan. Pastikan File Manager Plus sudah terpasang.")
  end
end

-- Pemutar Audio
local function stopPlayback()
  if state.player then
    pcall(function()
      if state.player.isPlaying() then state.player.stop() end
      state.player.release()
    end)
    state.player = nil
    state.isPlaying = false
  end
end

local function seekPlayback(deltaMs)
  if state.player and state.isPlaying then
    pcall(function()
      local cur = state.player.getCurrentPosition()
      local total = state.player.getDuration()
      local target = math.max(0, math.min(total, cur + deltaMs))
      state.player.seekTo(target)
      local detik = math.abs(math.floor(deltaMs / 1000))
      service.speak((deltaMs > 0 and "Maju " or "Mundur ") .. detik .. " detik")
    end)
  else
    service.speak("Putar audio terlebih dahulu untuk menggeser.")
  end
end

local function playAudioFile(path, onFinish)
  stopPlayback()
  local file = File(path)
  if not file.exists() then
    service.speak("Berkas audio tidak ditemukan.")
    return
  end

  local ok, err = pcall(function()
    state.player = MediaPlayer()
    state.player.setDataSource(path)
    state.player.prepare()
    state.player.start()
    state.isPlaying = true
    service.speak("Memutar rekaman.")

    state.player.setOnCompletionListener(MediaPlayer.OnCompletionListener{
      onCompletion = function(mp)
        stopPlayback()
        service.speak("Pemutaran selesai.")
        if onFinish then onFinish() end
      end
    })
  end)

  if not ok then
    service.speak("Gagal memutar audio: " .. tostring(err))
    stopPlayback()
  end
end

-- Berbagi Berkas Rekaman
local function shareAudioFile(filePath)
  local file = File(filePath)
  if not file.exists() then
    service.speak("Berkas tidak ditemukan.")
    return
  end

  pcall(function()
    local builderClass = luajava.bindClass("android.os.StrictMode$VmPolicy$Builder")
    StrictMode.setVmPolicy(builderClass().build())
  end)

  local absPath = tostring(file.getAbsolutePath())
  local fileName = tostring(file.getName())
  local ext = fileName:match("%.([^.]+)$")
  local mimeType = "audio/*"
  if ext then
    ext = ext:lower()
    if ext == "m4a" or ext == "aac" then
      mimeType = "audio/mp4"
    elseif ext == "mp3" then
      mimeType = "audio/mpeg"
    elseif ext == "wav" then
      mimeType = "audio/wav"
    elseif ext == "ogg" then
      mimeType = "audio/ogg"
    elseif ext == "3gp" or ext == "amr" then
      mimeType = "audio/3gpp"
    end
  end

  local shareUri = nil

  pcall(function()
    local FileProviderClass = nil
    pcall(function() FileProviderClass = luajava.bindClass("androidx.core.content.FileProvider") end)
    if not FileProviderClass then
      pcall(function() FileProviderClass = luajava.bindClass("android.support.v4.content.FileProvider") end)
    end

    if FileProviderClass then
      local pkg = service.getPackageName()
      local authorities = {
        pkg .. ".fileprovider",
        pkg .. ".provider",
        pkg .. ".FileProvider",
        pkg
      }
      for _, auth in ipairs(authorities) do
        local ok, res = pcall(function()
          return FileProviderClass.getUriForFile(service, auth, file)
        end)
        if ok and res ~= nil then
          shareUri = res
          break
        end
      end
    end
  end)

  if not shareUri then
    pcall(function()
      local cursor = service.getContentResolver().query(
        MediaStore.Audio.Media.EXTERNAL_CONTENT_URI,
        nil,
        MediaStore.Audio.Media.DATA .. "='" .. absPath:gsub("'", "''") .. "'",
        nil,
        nil
      )
      if cursor then
        if cursor.moveToFirst() then
          local idIdx = cursor.getColumnIndex(MediaStore.Audio.Media._ID)
          if idIdx >= 0 then
            local id = cursor.getLong(idIdx)
            shareUri = ContentUris.withAppendedId(MediaStore.Audio.Media.EXTERNAL_CONTENT_URI, id)
          end
        end
        cursor.close()
      end
    end)
  end

  if not shareUri then
    pcall(function()
      local values = ContentValues()
      values.put(MediaStore.Audio.Media.DATA, absPath)
      values.put(MediaStore.Audio.Media.TITLE, fileName)
      values.put(MediaStore.Audio.Media.DISPLAY_NAME, fileName)
      values.put(MediaStore.Audio.Media.MIME_TYPE, mimeType)
      shareUri = service.getContentResolver().insert(MediaStore.Audio.Media.EXTERNAL_CONTENT_URI, values)
    end)
  end

  if not shareUri then
    shareUri = Uri.fromFile(file)
  end

  pcall(function()
    local intent = Intent(Intent.ACTION_SEND)
    intent.setType(mimeType)
    intent.putExtra(Intent.EXTRA_STREAM, shareUri)
    intent.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
    intent.addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION)

    pcall(function()
      intent.setClipData(ClipData.newRawUri("", shareUri))
    end)

    local chooser = Intent.createChooser(intent, "Bagikan Rekaman")
    chooser.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
    chooser.addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION)
    service.startActivity(chooser)
    service.speak("Membuka menu bagikan.")
  end)
end

local function showRenameDialog(file, onRenamed)
  local fullName = tostring(file.getName())
  local baseName = fullName:gsub("%.[^.]+$", "")
  local ext = fullName:match("%.[^.]+$") or ""

  local input = EditText(service)
  input.setText(baseName)
  input.setHint("Masukkan nama baru...")
  input.selectAll()

  local builder = AlertDialog.Builder(service)
    .setTitle("Ubah Nama Rekaman")
    .setView(input)
    .setPositiveButton("Simpan", function()
      local newBase = tostring(input.getText()):gsub("^%s*(.-)%s*$", "%1")
      if newBase ~= "" and newBase ~= baseName then
        local newFile = File(file.getParentFile(), newBase .. ext)
        if file.renameTo(newFile) then
          service.speak("Nama berkas diubah menjadi " .. tostring(newFile.getName()))
          state.lastRecordedPath = tostring(newFile.getAbsolutePath())
          if onRenamed then onRenamed(newFile) end
        else
          service.speak("Gagal mengubah nama berkas.")
          if onRenamed then onRenamed(file) end
        end
      else
        if onRenamed then onRenamed(file) end
      end
    end)
    .setNegativeButton("Batal", function()
      if onRenamed then onRenamed(file) end
    end)

  displayOverlayDialog(builder)
end

-- Dialog Tindakan Rekaman Selesai
showRecordedFileActionDialog = function(file)
  if not file or not file.exists() then
    service.speak("Berkas rekaman tidak valid.")
    return
  end

  local dialogRef = nil
  local currentFile = file

  local layout = LinearLayout(service)
  layout.setOrientation(LinearLayout.VERTICAL)
  layout.setPadding(30, 20, 30, 20)

  local scrollView = ScrollView(service)
  local container = LinearLayout(service)
  container.setOrientation(LinearLayout.VERTICAL)

  local infoText = TextView(service)
  infoText.setTextSize(14)
  infoText.setPadding(10, 5, 10, 15)
  local function updateInfoLabel()
    local nameStr = tostring(currentFile.getName())
    local ext = nameStr:match("%.([^.]+)$") or ""
    infoText.setText("Ukuran: " .. formatFileSize(currentFile.length()) .. " | Format: " .. ext:upper())
  end
  updateInfoLabel()
  container.addView(infoText)

  local function createActionButton(label)
    local btn = Button(service)
    btn.setText(label)
    btn.setTextSize(16)
    btn.setGravity(Gravity.START | Gravity.CENTER_VERTICAL)
    local lp = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT)
    lp.setMargins(0, 6, 0, 6)
    btn.setLayoutParams(lp)
    return btn
  end

  local btnPlay = createActionButton(state.isPlaying and "1. Hentikan Pemutaran" or "1. Putar Rekaman")

  local seekLayout = LinearLayout(service)
  seekLayout.setOrientation(LinearLayout.HORIZONTAL)
  local seekLp = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT)
  seekLp.setMargins(0, 4, 0, 6)
  seekLayout.setLayoutParams(seekLp)

  local btnRewind = Button(service)
  btnRewind.setText("<< Mundur 10d")
  local rwLp = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1.0)
  rwLp.setMargins(0, 0, 6, 0)
  btnRewind.setLayoutParams(rwLp)

  local btnForward = Button(service)
  btnForward.setText("Maju 10d >>")
  local fwLp = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1.0)
  fwLp.setMargins(6, 0, 0, 0)
  btnForward.setLayoutParams(fwLp)

  seekLayout.addView(btnRewind)
  seekLayout.addView(btnForward)

  local btnShare = createActionButton("2. Bagikan Rekaman")
  local btnDelete = createActionButton("3. Hapus Rekaman")
  local btnRename = createActionButton("4. Ubah Nama Berkas")
  local btnHistory = createActionButton("5. Buka Riwayat Rekaman")
  local btnSettings = createActionButton("6. Buka Pengaturan")
  local btnFM = createActionButton("7. Buka Folder di File Manager Plus")

  container.addView(btnPlay)
  container.addView(seekLayout)
  container.addView(btnShare)
  container.addView(btnDelete)
  container.addView(btnRename)
  container.addView(btnHistory)
  container.addView(btnSettings)
  container.addView(btnFM)
  scrollView.addView(container)
  layout.addView(scrollView)

  btnPlay.setOnClickListener(function()
    triggerVibration(1.0)
    if state.isPlaying then
      stopPlayback()
      btnPlay.setText("1. Putar Rekaman")
      service.speak("Pemutaran dihentikan.")
    else
      btnPlay.setText("1. Hentikan Pemutaran")
      playAudioFile(currentFile.getAbsolutePath(), function()
        mainHandler.post(Runnable{
          run = function()
            pcall(function()
              btnPlay.setText("1. Putar Rekaman")
            end)
          end
        })
      end)
    end
  end)

  btnRewind.setOnClickListener(function()
    triggerVibration(0.8)
    seekPlayback(-10000)
  end)

  btnForward.setOnClickListener(function()
    triggerVibration(0.8)
    seekPlayback(10000)
  end)

  btnShare.setOnClickListener(function()
    triggerVibration(1.0)
    stopPlayback()
    if dialogRef then
      dialogRef.dismiss()
    end
    shareAudioFile(currentFile.getAbsolutePath())
  end)

  btnDelete.setOnClickListener(function()
    triggerVibration(1.0)
    local confirmBuilder = AlertDialog.Builder(service)
      .setTitle("Konfirmasi Hapus")
      .setMessage("Yakin ingin menghapus " .. tostring(currentFile.getName()) .. "?")
      .setPositiveButton("Hapus", function()
        stopPlayback()
        triggerVibration(1.2)
        local curPath = tostring(currentFile.getAbsolutePath())
        if currentFile.delete() then
          service.speak("Berkas rekaman berhasil dihapus.")
          if state.lastRecordedPath == curPath then
            state.lastRecordedPath = nil
          end
          if dialogRef then dialogRef.dismiss() end
        else
          service.speak("Gagal menghapus berkas.")
        end
      end)
      .setNegativeButton("Batal", nil)
    displayOverlayDialog(confirmBuilder)
  end)

  btnRename.setOnClickListener(function()
    triggerVibration(1.0)
    showRenameDialog(currentFile, function(renamedFile)
      currentFile = renamedFile
      updateInfoLabel()
      if dialogRef then
        pcall(function() dialogRef.setTitle(tostring(currentFile.getName())) end)
      end
    end)
  end)

  btnHistory.setOnClickListener(function()
    triggerVibration(1.0)
    stopPlayback()
    if dialogRef then dialogRef.dismiss() end
    showHistoryDialog()
  end)

  btnSettings.setOnClickListener(function()
    triggerVibration(1.0)
    stopPlayback()
    if dialogRef then dialogRef.dismiss() end
    showSettingsDialog()
  end)

  btnFM.setOnClickListener(function()
    triggerVibration(1.0)
    stopPlayback()
    if dialogRef then dialogRef.dismiss() end
    openFileManagerPlus(currentFile.getParentFile())
  end)

  local builder = AlertDialog.Builder(service)
    .setTitle(tostring(currentFile.getName()))
    .setView(layout)
    .setNegativeButton("Tutup", function()
      stopPlayback()
    end)

  dialogRef = displayOverlayDialog(builder)
  dialogRef.setOnDismissListener(function()
    stopPlayback()
  end)
end

-- ====================================================================
-- RIWAYAT REKAMAN
-- ====================================================================
showHistoryDialog = function()
  stopPlayback()
  local recordList = {}
  local seenPaths = {}

  local dirsToScan = {
    getRecordingsDir(),
    File(service.getExternalFilesDir(nil), APP_TITLE),
    File(Environment.getExternalStorageDirectory().getAbsolutePath() .. "/" .. APP_TITLE)
  }

  for _, dir in ipairs(dirsToScan) do
    if dir and dir.exists() and dir.isDirectory() then
      local files = dir.listFiles()
      if files then
        local count = 0
        pcall(function() count = Array.getLength(files) end)
        if count == 0 then
          pcall(function() count = #files end)
        end

        for i = 0, count - 1 do
          local f = nil
          pcall(function() f = files[i] end)
          if not f then
            pcall(function() f = Array.get(files, i) end)
          end

          if f and f.isFile() then
            local path = tostring(f.getAbsolutePath())
            if not seenPaths[path] then
              seenPaths[path] = true
              local name = tostring(f.getName()):lower()
              if name:match("%.m4a$") or name:match("%.wav$") or name:match("%.mp3$") or
                 name:match("%.aac$") or name:match("%.ogg$") or name:match("%.webm$") or
                 name:match("%.3gp$") or name:match("%.amr$") then
                table.insert(recordList, f)
              end
            end
          end
        end
      end
    end
  end

  if #recordList == 0 then
    service.speak("Belum ada file dalam riwayat rekaman.")
    local emptyDialogRef = nil
    local emptyBuilder = AlertDialog.Builder(service)
      .setTitle("Riwayat Rekaman")
      .setMessage("Belum ada berkas rekaman yang tersimpan di folder.")
      .setPositiveButton("Buka di FM Plus", function(dialog)
        if emptyDialogRef then pcall(function() emptyDialogRef.dismiss() end) end
        if dialog then pcall(function() dialog.dismiss() end) end
        triggerVibration(1.0)
        openFileManagerPlus(getRecordingsDir())
      end)
      .setNegativeButton("Tutup", function()
        triggerVibration(1.0)
      end)
    emptyDialogRef = displayOverlayDialog(emptyBuilder)
    return
  end

  table.sort(recordList, function(a, b)
    local timeA = tonumber(tostring(a.lastModified())) or 0
    local timeB = tonumber(tostring(b.lastModified())) or 0
    return timeA > timeB
  end)

  local displayItems = {}
  local sdf = SimpleDateFormat("dd/MM/yyyy HH:mm", Locale.getDefault())
  for i, f in ipairs(recordList) do
    local dateStr = tostring(sdf.format(Date(f.lastModified())))
    local fileName = tostring(f.getName())
    local fileSize = tostring(formatFileSize(f.length()))
    local itemText = string.format("%d. %s\n   [%s | %s]", i, fileName, fileSize, dateStr)
    table.insert(displayItems, itemText)
  end

  local historyDialogRef = nil
  local builder = AlertDialog.Builder(service)
    .setTitle("Riwayat Rekaman (" .. #recordList .. " Berkas)")
    .setItems(displayItems, function(dialog, which)
      dialog.dismiss()
      triggerVibration(1.0)
      local selectedFile = recordList[which + 1]
      if selectedFile and selectedFile.exists() then
        showRecordedFileActionDialog(selectedFile)
      else
        service.speak("Berkas sudah tidak tersedia.")
      end
    end)
    .setPositiveButton("Buka di FM Plus", function(dialog)
      if historyDialogRef then pcall(function() historyDialogRef.dismiss() end) end
      if dialog then pcall(function() dialog.dismiss() end) end
      triggerVibration(1.0)
      openFileManagerPlus(getRecordingsDir())
    end)
    .setNegativeButton("Tutup", function()
      triggerVibration(1.0)
    end)

  historyDialogRef = displayOverlayDialog(builder)
end

-- Penghentian Rekaman
stopRecording = function()
  if not state.isRecording then
    service.speak("Tidak ada rekaman yang sedang berjalan.")
    return
  end

  clearAutoStopTimer()
  state.isRecording = false
  state.isPaused = false
  abandonRecorderAudioFocus()
  triggerVibration(1.3)

  local ok = true
  local err = nil

  if state.agcEffect then
    pcall(function()
      state.agcEffect.setEnabled(false)
      state.agcEffect.release()
    end)
    state.agcEffect = nil
  end

  if state.isWav then
    pcall(function()
      if state.audioRecord then
        state.audioRecord.stop()
        state.audioRecord.release()
      end
    end)

    pcall(function()
      if state.recordThread then
        state.recordThread.join(1000)
      end
    end)

    if state.currentFilePath then
      updateWavHeader(state.currentFilePath, state.pcmTotalBytes or 0, state.pcmSampleRate or 44100, state.pcmChannels or 1)
    end

    state.audioRecord = nil
    state.recordThread = nil
    state.isWav = false
  else
    if state.recorder then
      ok, err = pcall(function()
        state.recorder.stop()
        state.recorder.reset()
        state.recorder.release()
      end)
      state.recorder = nil
    end
  end

  if ok and state.currentFilePath then
    state.lastRecordedPath = state.currentFilePath
    local recordedFile = File(state.currentFilePath)
    service.speak("Rekaman selesai.")
    showRecordedFileActionDialog(recordedFile)
  else
    service.speak("Rekaman dihentikan, terdapat kendala berkas: " .. tostring(err))
  end
end

-- Jeda Rekaman
local function pauseRecording()
  if not state.isRecording then return end
  if state.isPaused then
    showPauseDialog()
    return
  end

  if state.isWav then
    state.isPaused = true
    triggerVibration(1.0)
    service.speak("Rekaman dijeda.")
    showPauseDialog()
    return
  end

  if Build.VERSION.SDK_INT < 24 then
    service.speak("Android versi ini belum mendukung jeda rekaman. Rekaman langsung disimpan.")
    stopRecording()
    return
  end

  local ok, err = pcall(function()
    state.recorder.pause()
  end)

  if ok then
    state.isPaused = true
    triggerVibration(1.0)
    service.speak("Rekaman dijeda.")
    showPauseDialog()
  else
    service.speak("Gagal menjeda rekaman. Menghentikan rekaman.")
    stopRecording()
  end
end

-- Lanjutkan Rekaman
local function resumeRecording()
  if not state.isRecording or not state.isPaused then return end

  if state.isWav then
    state.isPaused = false
    triggerVibration(1.0)
    service.speak("Rekaman dilanjutkan.")
    return
  end

  local ok, err = pcall(function()
    state.recorder.resume()
  end)

  if ok then
    state.isPaused = false
    triggerVibration(1.0)
    service.speak("Rekaman dilanjutkan.")
  else
    service.speak("Gagal melanjutkan rekaman: " .. tostring(err))
  end
end

-- Dialog Rekaman Dijeda
showPauseDialog = function()
  local items = {
    "1. Lanjutkan Perekaman",
    "2. Selesai & Simpan Rekaman",
    "3. Batalkan & Hapus Rekaman"
  }

  local builder = AlertDialog.Builder(service)
    .setTitle("Rekaman Sedang Dijeda")
    .setItems(items, function(dialog, which)
      dialog.dismiss()
      if which == 0 then
        resumeRecording()
      elseif which == 1 then
        stopRecording()
      elseif which == 2 then
        local confirmBuilder = AlertDialog.Builder(service)
          .setTitle("Konfirmasi Pembatalan")
          .setMessage("Batalkan rekaman ini dan hapus berkasnya?")
          .setPositiveButton("Ya, Hapus", function()
            clearAutoStopTimer()
            state.isRecording = false
            state.isPaused = false
            abandonRecorderAudioFocus()
            triggerVibration(1.2)

            if state.agcEffect then
              pcall(function() state.agcEffect.release() end)
              state.agcEffect = nil
            end

            if state.isWav then
              pcall(function()
                if state.audioRecord then
                  state.audioRecord.stop()
                  state.audioRecord.release()
                end
                if state.recordThread then state.recordThread.join(800) end
              end)
              state.audioRecord = nil
              state.recordThread = nil
              state.isWav = false
            else
              pcall(function()
                if state.recorder then
                  state.recorder.stop()
                  state.recorder.reset()
                  state.recorder.release()
                end
              end)
              state.recorder = nil
            end

            if state.currentFilePath then
              File(state.currentFilePath).delete()
              state.currentFilePath = nil
            end
            service.speak("Rekaman dibatalkan dan dihapus.")
          end)
          .setNegativeButton("Kembali", function()
            showPauseDialog()
          end)
        displayOverlayDialog(confirmBuilder)
      end
    end)
    .setNegativeButton("Tutup", nil)

  displayOverlayDialog(builder)
end

-- Mulai Perekaman Suara
startRecording = function()
  if state.isRecording then
    service.speak("Perekaman sudah aktif berjalan.")
    return
  end

  stopPlayback()
  requestRecorderAudioFocus()

  local fmt = getAudioFormat()
  local ext = ".mp3"
  local outputFormat = 2
  local audioEncoder = 3
  local customRate = true
  local customBitrate = true
  local customChannels = true

  if (fmt == "ogg" or fmt == "webm") and Build.VERSION.SDK_INT < 29 then
    service.speak("Format " .. fmt:upper() .. " memerlukan Android 10 ke atas. Dialihkan ke MP3.")
    fmt = "mp3"
  end

  if fmt == "wav" then
    ext = ".wav"
  elseif fmt == "mp3" then
    ext = ".mp3"
    outputFormat = 2
    audioEncoder = 3
  elseif fmt == "m4a" then
    ext = ".m4a"
    outputFormat = 2
    audioEncoder = 3
  elseif fmt == "aac" then
    ext = ".aac"
    outputFormat = 6
    audioEncoder = 3
  elseif fmt == "ogg" then
    ext = ".ogg"
    outputFormat = 11
    audioEncoder = 7
  elseif fmt == "webm" then
    ext = ".webm"
    outputFormat = 9
    audioEncoder = 7
  elseif fmt == "amr_wb" then
    ext = ".amr"
    outputFormat = 4
    audioEncoder = 2
    customRate = false
    customBitrate = false
    customChannels = false
  elseif fmt == "amr_nb" then
    ext = ".amr"
    outputFormat = 3
    audioEncoder = 1
    customRate = false
    customBitrate = false
    customChannels = false
  elseif fmt == "3gp_aac" then
    ext = ".3gp"
    outputFormat = 1
    audioEncoder = 3
  elseif fmt == "3gp_amr" or fmt == "3gp" then
    ext = ".3gp"
    outputFormat = 1
    audioEncoder = 1
    customRate = false
    customBitrate = false
    customChannels = false
  end

  local prefix = getRecordPrefix()
  if prefix == "" then prefix = "REC" end
  local timeStamp = SimpleDateFormat("yyyyMMdd_HHmmss", Locale.getDefault()).format(Date())
  local targetFile = File(getRecordingsDir(), prefix .. "_" .. timeStamp .. ext)
  state.currentFilePath = tostring(targetFile.getAbsolutePath())

  local audioSourceId = MediaRecorder.AudioSource.MIC
  if getNoiseReduction() then
    audioSourceId = MediaRecorder.AudioSource.VOICE_RECOGNITION
  end

  -- Jalur WAV
  if fmt == "wav" then
    local sampleRate = math.floor(getAudioSampleRate())
    local channels = math.floor(getAudioChannels())
    local channelConfig = (channels == 2) and AudioFormat.CHANNEL_IN_STEREO or AudioFormat.CHANNEL_IN_MONO
    local audioEncoding = AudioFormat.ENCODING_PCM_16BIT
    local minBuf = AudioRecord.getMinBufferSize(sampleRate, channelConfig, audioEncoding)
    if minBuf <= 0 then minBuf = 4096 end
    local bufSize = minBuf * 2

    local ok, err = pcall(function()
      state.audioRecord = AudioRecord(audioSourceId, sampleRate, channelConfig, audioEncoding, bufSize)
      if state.audioRecord.getState() ~= AudioRecord.STATE_INITIALIZED then
        error("Inisialisasi AudioRecord gagal.")
      end

      if getGainControl() then
        pcall(function()
          if AutomaticGainControl.isAvailable() then
            state.agcEffect = AutomaticGainControl.create(state.audioRecord.getAudioSessionId())
            if state.agcEffect then state.agcEffect.setEnabled(true) end
          end
        end)
      end

      state.isWav = true
      state.pcmSampleRate = sampleRate
      state.pcmChannels = channels
      state.pcmTotalBytes = 0
      state.audioRecord.startRecording()

      state.recordThread = Thread(Runnable{
        run = function()
          local fos = nil
          pcall(function()
            fos = FileOutputStream(File(state.currentFilePath))
            local headerPlaceholder
            pcall(function() headerPlaceholder = byte[44] end)
            if not headerPlaceholder then
              headerPlaceholder = Array.newInstance(Byte.TYPE, 44)
            end
            fos.write(headerPlaceholder)

            local pcmBuffer
            pcall(function() pcmBuffer = byte[4096] end)
            if not pcmBuffer then
              pcmBuffer = Array.newInstance(Byte.TYPE, 4096)
            end

            local totalBytes = 0
            while state.isRecording and state.isWav do
              if not state.isPaused then
                local readBytes = state.audioRecord.read(pcmBuffer, 0, 4096)
                if readBytes > 0 then
                  fos.write(pcmBuffer, 0, readBytes)
                  totalBytes = totalBytes + readBytes
                  state.pcmTotalBytes = totalBytes
                end
              else
                Thread.sleep(100)
              end
            end
            fos.flush()
            fos.close()
          end)
        end
      })
      state.recordThread.start()
    end)

    if ok then
      state.isRecording = true
      state.isPaused = false
      setupAutoStopTimer()
      triggerVibration(1.1)
      local msg = "Perekaman WAV Lossless dimulai"
      if getRecordTimerSeconds() > 0 then
        msg = msg .. " (Timer " .. math.floor(getRecordTimerSeconds() / 60) .. "m)"
      end
      service.speak(msg)
    else
      abandonRecorderAudioFocus()
      state.audioRecord = nil
      state.recordThread = nil
      state.isWav = false
      state.isRecording = false
      state.isPaused = false
      service.speak("Gagal memulai rekaman WAV: " .. tostring(err))
    end
    return
  end

  -- Jalur MediaRecorder
  local ok, err = pcall(function()
    state.recorder = MediaRecorder()
    state.isWav = false

    state.recorder.setAudioSource(audioSourceId)
    state.recorder.setOutputFormat(outputFormat)
    state.recorder.setAudioEncoder(audioEncoder)

    if not customRate then
      if fmt == "amr_wb" then
        state.recorder.setAudioSamplingRate(16000)
      else
        state.recorder.setAudioSamplingRate(8000)
      end
    else
      pcall(function() state.recorder.setAudioSamplingRate(math.floor(getAudioSampleRate())) end)
    end

    if customBitrate then
      pcall(function() state.recorder.setAudioEncodingBitRate(math.floor(getAudioBitrate())) end)
    end

    if not customChannels then
      pcall(function() state.recorder.setAudioChannels(1) end)
    else
      pcall(function() state.recorder.setAudioChannels(math.floor(getAudioChannels())) end)
    end

    state.recorder.setOutputFile(state.currentFilePath)
    state.recorder.prepare()
    state.recorder.start()
  end)

  if ok then
    state.isRecording = true
    state.isPaused = false
    setupAutoStopTimer()
    triggerVibration(1.1)
    local msg = "Perekaman suara dimulai"
    if getRecordTimerSeconds() > 0 then
      msg = msg .. " (Timer " .. math.floor(getRecordTimerSeconds() / 60) .. "m)"
    end
    service.speak(msg)
  else
    abandonRecorderAudioFocus()
    state.recorder = nil
    state.isRecording = false
    state.isPaused = false
    service.speak("Gagal memulai rekaman: " .. tostring(err))
  end
end

-- Dialog Format Audio
showFormatDialog = function()
  local formats = {
    "1. WAV (Lossless PCM - Kualitas Asli)",
    "2. M4A / AAC (Rekomendasi - Jernih & Standar)",
    "3. MP3 (Format Musik)",
    "4. AAC / ADTS (Raw Audio)",
    "5. OGG / Opus (Android 10+)",
    "6. WebM / Opus (Format Modern)",
    "7. AMR-WB (Vokal HD, 16 kHz)",
    "8. AMR-NB (Telepon Standar, 8 kHz)",
    "9. 3GP / AAC (Kontainer 3GP Kualitas AAC)",
    "10. 3GP / AMR-NB (Ukuran Paling Ringan)"
  }
  local values = {
    "wav", "m4a", "mp3", "aac", "ogg", "webm",
    "amr_wb", "amr_nb", "3gp_aac", "3gp_amr"
  }
  local currentFmt = getAudioFormat()
  local selIndex = 2

  for i, v in ipairs(values) do
    if tostring(v) == tostring(currentFmt) or (v == "3gp_amr" and currentFmt == "3gp") then
      selIndex = i - 1
      break
    end
  end

  local builder = AlertDialog.Builder(service)
    .setTitle("Pilih Format Audio")
    .setSingleChoiceItems(formats, selIndex, function(dialog, which)
      dialog.dismiss()
      setAudioFormat(values[which + 1])
      triggerVibration(1.0)
      service.speak("Format diubah ke " .. formats[which + 1]:gsub("^%d+%.%s*", ""))
      showSettingsDialog()
    end)
    .setNegativeButton("Kembali", function()
      showSettingsDialog()
    end)

  displayOverlayDialog(builder)
end

-- Dialog Bitrate
showBitrateDialog = function()
  local options = {
    "320 kbps (Kualitas Tertinggi)",
    "256 kbps (Sangat Tinggi)",
    "192 kbps (Tinggi)",
    "128 kbps (Standar)",
    "96 kbps (Sedang)",
    "64 kbps (Hemat Ruang)"
  }
  local values = {320000, 256000, 192000, 128000, 96000, 64000}
  local current = getAudioBitrate()
  local selIndex = 3

  for i, v in ipairs(values) do
    if tonumber(v) == tonumber(current) then
      selIndex = i - 1
      break
    end
  end

  local builder = AlertDialog.Builder(service)
    .setTitle("Pilih Bitrate")
    .setSingleChoiceItems(options, selIndex, function(dialog, which)
      dialog.dismiss()
      setAudioBitrate(values[which + 1])
      triggerVibration(1.0)
      service.speak("Bitrate diatur ke " .. options[which + 1])
      showSettingsDialog()
    end)
    .setNegativeButton("Kembali", function()
      showSettingsDialog()
    end)

  displayOverlayDialog(builder)
end

-- Dialog Frekuensi Sampel
showSampleRateDialog = function()
  local options = {
    "48 kHz (Kualitas Studio)",
    "44.1 kHz (Kualitas CD / Standar)",
    "22.05 kHz (Sedang)",
    "16 kHz (Standar Bicara)",
    "8 kHz (Kualitas Telepon)"
  }
  local values = {48000, 44100, 22050, 16000, 8000}
  local current = getAudioSampleRate()
  local selIndex = 1

  for i, v in ipairs(values) do
    if tonumber(v) == tonumber(current) then
      selIndex = i - 1
      break
    end
  end

  local builder = AlertDialog.Builder(service)
    .setTitle("Pilih Frekuensi Sampel (kHz)")
    .setSingleChoiceItems(options, selIndex, function(dialog, which)
      dialog.dismiss()
      setAudioSampleRate(values[which + 1])
      triggerVibration(1.0)
      service.speak("Frekuensi sampel diatur ke " .. options[which + 1])
      showSettingsDialog()
    end)
    .setNegativeButton("Kembali", function()
      showSettingsDialog()
    end)

  displayOverlayDialog(builder)
end

-- Dialog Channels
showChannelsDialog = function()
  local channelOptions = {
    "Mono (1 Channel - Ringan)",
    "Stereo (2 Channel - Kiri/Kanan)"
  }
  local values = {1, 2}
  local current = getAudioChannels()
  local selIndex = (tonumber(current) == 2) and 1 or 0

  local builder = AlertDialog.Builder(service)
    .setTitle("Pilih Saluran Audio")
    .setSingleChoiceItems(channelOptions, selIndex, function(dialog, which)
      dialog.dismiss()
      setAudioChannels(values[which + 1])
      triggerVibration(1.0)
      local selectedName = (values[which + 1] == 2) and "Stereo" or "Mono"
      service.speak("Saluran audio diatur ke " .. selectedName)
      showSettingsDialog()
    end)
    .setNegativeButton("Kembali", function()
      showSettingsDialog()
    end)

  displayOverlayDialog(builder)
end

-- Dialog Prefix
showPrefixDialog = function()
  local prefixes = {"1. REC", "2. Catatan", "3. Wawancara", "4. Kuliah", "5. Suara", "6. Musik"}
  local values = {"REC", "Catatan", "Wawancara", "Kuliah", "Suara", "Musik"}
  local current = getRecordPrefix()
  local selIndex = 0

  for i, v in ipairs(values) do
    if v == current then
      selIndex = i - 1
      break
    end
  end

  local builder = AlertDialog.Builder(service)
    .setTitle("Pilih Awalan Nama Berkas")
    .setSingleChoiceItems(prefixes, selIndex, function(dialog, which)
      dialog.dismiss()
      local chosen = values[which + 1]
      setRecordPrefix(chosen)
      triggerVibration(1.0)
      service.speak("Awalan nama berkas diatur ke " .. chosen)
      showSettingsDialog()
    end)
    .setNegativeButton("Kembali", function()
      showSettingsDialog()
    end)

  displayOverlayDialog(builder)
end

-- Dialog Peredam Bising
showNoiseReductionDialog = function()
  local options = {
    "Aktif (Filter Desis & Fokus Suara)",
    "Nonaktif (Suara Alami)"
  }
  local isEnabled = getNoiseReduction()
  local selIndex = isEnabled and 0 or 1

  local builder = AlertDialog.Builder(service)
    .setTitle("Peredam Bising (Noise Suppression)")
    .setSingleChoiceItems(options, selIndex, function(dialog, which)
      dialog.dismiss()
      local enable = (which == 0)
      setNoiseReduction(enable)
      triggerVibration(1.0)
      service.speak("Peredam bising " .. (enable and "diaktifkan" or "dinonaktifkan"))
      showSettingsDialog()
    end)
    .setNegativeButton("Kembali", function()
      showSettingsDialog()
    end)

  displayOverlayDialog(builder)
end

-- Dialog Gain Control (AGC)
showGainControlDialog = function()
  local options = {
    "Aktif (Automatic Gain Control - Stabilkan Volume Suara)",
    "Nonaktif (Volume Mikrofon Bawaan Pabrik)"
  }
  local isEnabled = getGainControl()
  local selIndex = isEnabled and 0 or 1

  local builder = AlertDialog.Builder(service)
    .setTitle("Gain Control (AGC)")
    .setSingleChoiceItems(options, selIndex, function(dialog, which)
      dialog.dismiss()
      local enable = (which == 0)
      setGainControl(enable)
      triggerVibration(1.0)
      service.speak("Gain control " .. (enable and "diaktifkan" or "dinonaktifkan"))
      showSettingsDialog()
    end)
    .setNegativeButton("Kembali", function()
      showSettingsDialog()
    end)

  displayOverlayDialog(builder)
end

-- Dialog Timer Rekaman Otomatis
showRecordTimerDialog = function()
  local timerOptions = {
    "1. Nonaktif (Rekam Manual Tanpa Batas)",
    "2. 5 Menit",
    "3. 15 Menit",
    "4. 30 Menit",
    "5. 60 Menit (1 Jam)"
  }
  local values = {0, 300, 900, 1800, 3600}
  local currentSec = getRecordTimerSeconds()
  local selIndex = 0

  for i, v in ipairs(values) do
    if tonumber(v) == tonumber(currentSec) then
      selIndex = i - 1
      break
    end
  end

  local builder = AlertDialog.Builder(service)
    .setTitle("Timer Rekaman Otomatis")
    .setSingleChoiceItems(timerOptions, selIndex, function(dialog, which)
      dialog.dismiss()
      local chosenSec = values[which + 1]
      setRecordTimerSeconds(chosenSec)
      triggerVibration(1.0)
      local label = (chosenSec == 0 and "dinonaktifkan") or (math.floor(chosenSec / 60) .. " menit")
      service.speak("Timer rekaman otomatis " .. label)
      showSettingsDialog()
    end)
    .setNegativeButton("Kembali", function()
      showSettingsDialog()
    end)

  displayOverlayDialog(builder)
end

-- Dialog Aksi Penghentian
showStopBehaviorDialog = function()
  local options = {
    "Langsung Berhenti (Simpan & Tampilkan Menu)",
    "Terjeda Dulu (Pause Rekaman Sebelum Disimpan)"
  }
  local values = {"direct", "pause"}
  local current = getStopBehavior()
  local selIndex = (tostring(current) == "pause") and 1 or 0

  local builder = AlertDialog.Builder(service)
    .setTitle("Aksi Penghentian Rekaman")
    .setSingleChoiceItems(options, selIndex, function(dialog, which)
      dialog.dismiss()
      setStopBehavior(values[which + 1])
      triggerVibration(1.0)
      local label = (which == 1) and "Terjeda Dulu" or "Langsung Berhenti"
      service.speak("Aksi penghentian diatur ke " .. label)
      showSettingsDialog()
    end)
    .setNegativeButton("Kembali", function()
      showSettingsDialog()
    end)

  displayOverlayDialog(builder)
end

-- Dialog Efek Getaran
showVibrationDialog = function()
  local options = {
    "1. Rendah (Lembut)",
    "2. Sedang (Standar)",
    "3. Tinggi (Kuat)",
    "4. Nonaktif (Hening)"
  }
  local values = {"low", "medium", "high", "off"}
  local current = getVibrationLevel()
  local selIndex = 0

  for i, v in ipairs(values) do
    if v == current then
      selIndex = i - 1
      break
    end
  end

  local builder = AlertDialog.Builder(service)
    .setTitle("Intensitas Getaran")
    .setSingleChoiceItems(options, selIndex, function(dialog, which)
      dialog.dismiss()
      local chosen = values[which + 1]
      setVibrationLevel(chosen)
      triggerVibration(1.0)
      service.speak("Intensitas getaran diatur ke " .. chosen)
      showSettingsDialog()
    end)
    .setNegativeButton("Kembali", function()
      showSettingsDialog()
    end)

  displayOverlayDialog(builder)
end

-- Dialog Reset
showResetConfirmDialog = function()
  local builder = AlertDialog.Builder(service)
    .setTitle("Reset Pengaturan")
    .setMessage("Kembalikan semua setelan perekam ke setelan default?")
    .setPositiveButton("Ya, Reset", function()
      pcall(function() sp.edit().clear().commit() end)
      pcall(function() if backupConfigFile.exists() then backupConfigFile.delete() end end)
      triggerVibration(1.0)
      service.speak("Semua pengaturan dikembalikan ke awal.")
      showSettingsDialog()
    end)
    .setNegativeButton("Batal", function()
      showSettingsDialog()
    end)

  displayOverlayDialog(builder)
end

-- Menu Pengaturan
showSettingsDialog = function()
  local fmtLabels = {
    wav = "WAV (Lossless PCM)", m4a = "M4A (AAC)", mp3 = "MP3", aac = "AAC (ADTS)",
    ogg = "OGG (Opus)", webm = "WebM (Opus)", amr_wb = "AMR-WB (16k)",
    amr_nb = "AMR-NB (8k)", ["3gp_aac"] = "3GP (AAC)", ["3gp_amr"] = "3GP (AMR)", ["3gp"] = "3GP (AMR)"
  }
  local curFmt = getAudioFormat()
  local fmtName = fmtLabels[curFmt] or curFmt:upper()
  local kbps = (curFmt == "wav") and "Uncompressed (PCM)" or (math.floor(getAudioBitrate() / 1000) .. " kbps")
  local khzVal = getAudioSampleRate() / 1000
  local khz = (khzVal == math.floor(khzVal) and string.format("%d", khzVal) or string.format("%.1f", khzVal)) .. " kHz"
  local chName = (getAudioChannels() == 2) and "Stereo (2 Ch)" or "Mono (1 Ch)"
  local prefixName = getRecordPrefix()

  local noiseLabel = getNoiseReduction() and "Aktif" or "Nonaktif"
  local gainLabel = getGainControl() and "Aktif (AGC)" or "Nonaktif"
  local timerSec = getRecordTimerSeconds()
  local timerLabel = (timerSec == 0 and "Nonaktif") or (math.floor(timerSec / 60) .. " Menit")
  local stopBehaviorLabel = (getStopBehavior() == "pause") and "Terjeda Dulu" or "Langsung Berhenti"
  local vibLevel = getVibrationLevel()

  local settingsItems = {
    "1. Format Berkas (Aktif: " .. fmtName .. ")",
    "2. Laju Bit / Bitrate (Aktif: " .. kbps .. ")",
    "3. Frekuensi Sampel (Aktif: " .. khz .. ")",
    "4. Saluran Audio (Aktif: " .. chName .. ")",
    "5. Awalan Nama Berkas (Aktif: " .. prefixName .. "_)",
    "6. Peredam Bising (Aktif: " .. noiseLabel .. ")",
    "7. Gain Control / AGC (Aktif: " .. gainLabel .. ")",
    "8. Timer Batas Rekam (Aktif: " .. timerLabel .. ")",
    "9. Aksi Penghentian (Aktif: " .. stopBehaviorLabel .. ")",
    "10. Intensitas Getaran (Aktif: " .. vibLevel .. ")",
    "11. Periksa Versi Baru",
    "12. Reset Semua Pengaturan ke Default"
  }

  local builder = AlertDialog.Builder(service)
    .setTitle("Pengaturan Perekam Suara (v" .. SCRIPT_VERSION .. ")")
    .setItems(settingsItems, function(dialog, which)
      dialog.dismiss()
      triggerVibration(1.0)
      if which == 0 then showFormatDialog()
      elseif which == 1 then showBitrateDialog()
      elseif which == 2 then showSampleRateDialog()
      elseif which == 3 then showChannelsDialog()
      elseif which == 4 then showPrefixDialog()
      elseif which == 5 then showNoiseReductionDialog()
      elseif which == 6 then showGainControlDialog()
      elseif which == 7 then showRecordTimerDialog()
      elseif which == 8 then showStopBehaviorDialog()
      elseif which == 9 then showVibrationDialog()
      elseif which == 10 then checkForUpdate()
      elseif which == 11 then showResetConfirmDialog()
      end
    end)
    .setNegativeButton("Tutup", nil)

  displayOverlayDialog(builder)
end

-- ====================================================================
-- ALUR EKSEKUSI
-- ====================================================================
if state.isRecording then
  if state.isPaused then
    showPauseDialog()
  elseif getStopBehavior() == "pause" then
    pauseRecording()
  else
    stopRecording()
  end
else
  startRecording()
end

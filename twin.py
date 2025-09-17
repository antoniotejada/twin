#!/usr/bin/env python
"""
Twin panel file manager

XXX Allow search sourcing from voidtools Everything?

"""

import collections
import datetime
import logging
import os
import Queue
import shutil
import string
import struct
import sys
import time

from PIL import Image, ImageQt, ExifTags

from PyQt5.QtCore import *
from PyQt5.QtGui import *
from PyQt5.QtWidgets import *

FileInfo = collections.namedtuple("FileInfo", ["filename","size", "mtime", "attr"])

# XXX Add system, archive, etc
FILEINFO_ATTR_DIR = 1 << 0
FILEINFO_ATTR_HIDDEN = 1 << 1
FILEINFO_ATTR_WRITABLE = 1 << 2

def fileinfo_is_dir(fileinfo):
    return ((fileinfo.attr & FILEINFO_ATTR_DIR) != 0)

def fileinfo_is_hidden(fileinfo):
    return ((fileinfo.attr & FILEINFO_ATTR_HIDDEN) != 0)

def fileinfo_is_writable(fileinfo):
    return ((fileinfo.attr & FILEINFO_ATTR_WRITABLE) != 0)

def fileinfo_build_attr(is_dir, is_hidden, is_writable):
    return (
        (1 if is_dir else 0) |
        (2 if is_hidden else 0) |
        (4 if is_writable else 0) |
        0
    )

class LineHandler(logging.StreamHandler):
    def __init__(self):
        super(LineHandler, self).__init__()

    def emit(self, record):
        text = record.getMessage()
        messages = text.split('\n')
        indent = ""
        for message in messages:
            r = record
            r.msg = "%s%s" % (indent, message)
            r.args = None
            super(LineHandler, self).emit(r)
            indent = "    " 

def setup_logger(logger):
    """
    Setup the logger with a line break handler
    """
    logging_format = "%(asctime).23s %(levelname)s:%(filename)s(%(lineno)d):[%(thread)d] %(funcName)s: %(message)s"

    logger_handler = LineHandler()
    logger_handler.setFormatter(logging.Formatter(logging_format))
    logger.addHandler(logger_handler) 

    return logger

def os_path_root(path):
    """
    - Return the parent root of the path, ie the topmost path that is not the
      drive or the unc
    - Return None if path has no parent
    """
    # Remove drive and unc, normalize slashes and pick the first component
    path = os.path.splitunc(os.path.splitdrive(path)[1])[1]
    path = os.path.normpath(path)
    components = path.split(os.path.sep)
    root = None if (len(components) == 1) else components[0]

    return root

def os_remove(filepath):
    if (os.path.isdir(filepath)):
        shutil.rmtree(filepath)
    else:
        os.remove(filepath)

def xrange(list_or_int):
    return __builtins__.xrange(list_or_int if isinstance(list_or_int, int) else len(list_or_int))

def index_of(l, item):
    try:
        return l.index(item)

    except Exception:
        return -1

def rindex_of(l, item):
    try:
        return l.rindex(item)

    except Exception:
        return -1

# XXX This needs to use the imagereader/PIL supported extensions
# XXX Should add all files disregarding extensions so full directories can be
#     moved, etc?
IMAGE_EXTENSIONS = ('.bmp','.enc','.gif', '.jpg', '.jpeg', '.jfif', '.png', '.webp')
FILTERED_EXTENSIONS = []

# Size of the thumbnails stored in the model
IMAGE_WIDTH = 256
IMAGE_HEIGHT = 256

# Size of the images displayed on each item of the listview
DISPLAY_WIDTH = 128
DISPLAY_HEIGHT = 128

# XXX Make this dependent in images per viewport and memory consumed
MAX_CACHE_ENTRIES = 92
# Reduce the cache by this number of entries when the cache overflows
MAX_CACHE_ENTRIES_WATERMARK = 10

# Number of PixmapReader threads in charge of reading the image, decoding and
# scaling. On slow sources, this can cause stale reads to block newer ones when
# navigating the directory
READING_THREADS = 10
READING_THREADS = 1

use_image_reader = True
# PIL is able to read exif tags but causes the UI to stutter noticeably
# and consumes a 4x more memory
use_pil = True

# Use a QStyledItemDelegate to draw scalable icons as thumbnails. The other
# option is to have the model return the scaled up icon, but that means all the
# views must have the same icon size
use_delegate = True

# Incremental row loading works, but makes select all/invert selection behave
# unexpectedly (eg select all + fetchmore thew new rows won't be selected),
# scrollbars change scale as new rows are loaded...
# XXX This will be needed for Voidtools Everything integration? Or use some kind
#     of capping there?
use_incremental_row_loading = False

# Use Qt a lot faster (x4?) but more UI blocking diriterator vs. Python os.listdir
use_diriterator = True
# Use win32 FindFirst/FindNext, probably slower than Qt, but a lot faster than
# os.listdir and completely non-blocking
use_findfirst = True

def qFindMainWindow():
    for widget in qApp.topLevelWidgets():
        if (isinstance(widget, QMainWindow)):
            return widget
    return None

def qResizePixmap(pixmap, target_width, target_height):
    """
        Scale the given pixmap to the target size, preserving aspect ratio, and
        centering the image by adding any necessary simmetric padding.
    """
    assert None is logger.debug("Resizing from %dx%d to %dx%d", pixmap.width(), pixmap.height(), target_width, target_height)
    
    # Get the original width and height of the pixmap
    orig_width = pixmap.width()
    orig_height = pixmap.height()

    # Calculate the scaling factor to preserve aspect ratio
    scale_factor_width = float(target_width) / orig_width
    scale_factor_height = float(target_height) / orig_height
    scale_factor = min(scale_factor_width, scale_factor_height)

    # Calculate the new width and height while preserving the aspect ratio
    new_width = int(orig_width * scale_factor)
    new_height = int(orig_height * scale_factor)

    # Scale the image to the new size
    scaled_pixmap = pixmap.scaled(new_width, new_height, Qt.KeepAspectRatio, Qt.SmoothTransformation)
    
    # Create a new pixmap of the target size
    result_pixmap = QPixmap(target_width, target_height)
    result_pixmap.fill(QColor(255, 255, 255))  # Fill with a white background (or any color)

    # Center the scaled image onto the result pixmap
    painter = QPainter(result_pixmap)
    x_offset = (target_width - new_width) // 2
    y_offset = (target_height - new_height) // 2
    painter.drawPixmap(x_offset, y_offset, scaled_pixmap)
    painter.end()

    return result_pixmap
    
def qLaunchWithPreferredApp(filepath):
    logger.info("%r", filepath)
    # pyqt5 on lxde raspbian fails to invoke xdg-open for unknown reasons and
    # falls back to invoking the web browser instead, use xdg-open explicitly on
    # "xcb" platforms (X11) 
    # See https://github.com/qt/qtbase/blob/067b53864112c084587fa9a507eb4bde3d50a6e1/src/gui/platform/unix/qgenericunixservices.cpp#L129
    if (QApplication.platformName() != "xcb"):
        url = QUrl.fromLocalFile(filepath)
        QDesktopServices.openUrl(url)
        
    else:
        # Note there's no splitCommand in this version of Qt5, build the
        # argument list manually
        QProcess.startDetached("xdg-open", [filepath])

def qYesNoCancelMessageBox(parent, title, message, defaultButton=QMessageBox.Cancel):
    return QMessageBox.question(parent, title, message,
        buttons=QMessageBox.Yes | QMessageBox.No | QMessageBox.Cancel,
        # Set it explicitly. Despite what docs say, the default is Yes
        defaultButton=defaultButton)


g_rate_limited_call_timers = {}
def qRateLimitCall(fn, delay_ms):
    """
    Call the function and force a delay to the next invocation. Essentially a
    rate-limited call.

    This is slightly different than the classic deboucne where
    - The first invocation is delayed 
    - Further invications restart the debounce timer

    Note this uses the function reference as debounce identifier, which works
    with regular functions and member functiosn (each instance will have its own
    identifier so they are debounced independently) but can fail with certain
    lambdas or local functions that depend on the context and generate an
    different internal function (which are essentially different functions
    anyway and should debounce separately?)

    XXX Arguably for context-dependent just keep updating the function and
        overwrite the last invocation?
    """
    def call_and_cleanup(fn):
        key = fn
        timer, rate_limited_calls = g_rate_limited_call_timers.pop(key)
        logger.info("Rate limiting timer expired for %r rate_limited_calls %s", fn, rate_limited_calls)
        if (rate_limited_calls > 0):
            fn()
        
    key = fn
    # Allow this call unless less than delay_ms happened since the last call
    timer, rate_limited_calls = g_rate_limited_call_timers.get(key, (None, 0))
    if (timer is None):
        logger.info("Rate limiting timer not found for %s %r", key, fn)
        # First debounce call:
        # - call the function
        # - set a timer flagging not call at expiration
        fn()

        timer = QTimer()
        timer.setSingleShot(True)
        timer.timeout.connect(lambda : call_and_cleanup(fn))
        timer.start(delay_ms)

        g_rate_limited_call_timers[key] = (timer, 0)

    else:
        assert None is logger.debug("Rate limiting timer found for %s %r rate_limited_calls %d", key, fn, rate_limited_calls)
        # Second or later time was called, ignore the call, flag to call at
        # timer expiration

        # XXX This could restart the timer. Have a version that always delays
        #     and restarts?
        g_rate_limited_call_timers[key] = (timer, rate_limited_calls + 1) 

def qEnumToStr(enum_type, enum_value):
    # Note type(enum_value) is QtCore.Type, so enum_type cannot be obtained from
    # enum_value and has to be provided as parameter
    enumTypeToName = {
        getattr(enum_type, name) : name for name in vars(enum_type)
        if isinstance(getattr(enum_type, name), type(enum_value))
    }
    return enumTypeToName.get(enum_value, "0x%x" % enum_value)

def qEnumToStr2(enum_type, enum_value):
    # XXX QMetaEnum.fromType doesn't exist in PyQt5
    meta_enum = QMetaEnum.fromType(enum_type)
    return meta_enum.valueToKey(enum_value)

class EnumString:
    """
    Using the class instead of the function directly, prevents the conversion to
    string when used as logging parameter when logging is disabled, increasing
    performance.

    Examples:

    print EnumString(QEvent, QEvent.KeyPress)
    KeyPress
    print EnumString(QEvent, 6)
    KeyPress
    print EnumString(QEvent, event.type()
    """
    def __init__(self, enum_type, enum_value):
        self.enumType = enum_type
        self.enumValue = enum_value

    def __str__(self):
        return qEnumToStr(self.enumType, self.enumValue)

def qBitToStr(enum_type, bit_type, bit_value):
    # Note type(enum_value) is QtCore.Type, so enum_type cannot be obtained from
    # enum_value and has to be provided as parameter
    enumTypeToName = {
        getattr(enum_type, name) : name for name in vars(enum_type)
        if isinstance(getattr(enum_type, name), bit_type)
    }
    return enumTypeToName.get(bit_value, "0x%x" % bit_value)

def qBitNamesToStr(enum_type, sample_value, bits):
    """
    sample_value is needed because, unlike with regular enums, bits is a
    combination value of type int, so there's no way to get the mask type to
    introspect from.

    XXX This doesn't work for bitmasks that hold multiple types, eg for QFrame
        style, is split between QFrame.Shadow_mask and QFrame.Shape_mask values
        setFrameShadow, setFrameShape and setFrameStyle for the combined values

    QFrame.Shadow values qBitNamesToStr(QFrame, QFrame.Plain, QFrame.Raised)
    ['Raised']

    qBitNamesToStr(QFrame, QFrame.Sunken, QFrame.Sunken) ['Plain', 'Raised']

    QFrame.Shape values qBitNamesToStr(QFrame, QFrame.VLine, QFrame.VLine)
    ['Box', 'HLine']

    but it won't work with the combined style. Make sample_value allow a list of
    values from both enums?

    """
    current_bitmask = 1
    bit_names = []

    while (current_bitmask <= bits):
        bit = bits & current_bitmask
        if (bit != 0):
            bit_name = qBitToStr(enum_type, type(sample_value), bit)
            bit_names.append(bit_name)
        current_bitmask = current_bitmask << 1

    if (len(bit_names) == 0):
        bit_names.append(qBitToStr(enum_type, type(sample_value), 0))
    return str.join(",", bit_names)

class BitmaskString:
    """
    Using the class instead of the function directly, prevents the conversion to
    string when used as logging parameter when logging is disabled, increasing
    performance.

    Examples:

    print BitmaskString(QItemSelectionModel, QItemSelectionModel.NoUpdate,
    QItemSelectionModel.Select) Select print BitmaskString(QItemSelectionModel,
    QItemSelectionModel.NoUpdate, 2) Select print
    BitmaskString(QItemSelectionModel, QItemSelectionModel.NoUpdate, 3)
    Clear,Select

    print BitmaskString(QStyle, QStyle.State_None, QStyle.State_Raised)
    State_Raised print BitmaskString(QStyle, QStyle.State_None, 2) State_Raised

    """
    def __init__(self, enum_type, sample_value, bits):
        self.enumType = enum_type
        self.sampleValue = sample_value
        self.bits = bits

    def __str__(self):
        return qBitNamesToStr(self.enumType, self.sampleValue, self.bits)

class DirectoryReader(QThread):
    direntryRead = pyqtSignal(set, list)
    def __init__(self, dirpath, batch_size = None, recurse=False, parent=None):
        super(DirectoryReader, self).__init__(parent)
        self.dirpath = dirpath
        self.batch_size = batch_size
        self.recurse = recurse
        
    def abort(self):
        logger.info("Requesting abort")
        self.requestInterruption()
        
    def mustAbort(self):
        return self.isInterruptionRequested()

    def run(self):
        logger.info("Starting %r", self.dirpath)
        if (use_findfirst):
            import ctypes

            dir_infos_set = set()
            file_infos = []

            # Define FILETIME structure (64-bit value)
            class FILETIME(ctypes.Structure):
                _fields_ = [
                    ("dwLowDateTime", ctypes.c_uint32),
                    ("dwHighDateTime", ctypes.c_uint32)
                ]

            class WIN32_FIND_DATA(ctypes.Structure):
                _fields_ = [
                    ("dwFileAttributes", ctypes.c_uint32),   # File attributes
                    ("ftCreationTime", FILETIME),            # File creation time
                    ("ftLastAccessTime", FILETIME),          # Last access time
                    ("ftLastWriteTime", FILETIME),           # Last write time
                    ("nFileSizeHigh", ctypes.c_uint32),      # High part of file size
                    ("nFileSizeLow", ctypes.c_uint32),       # Low part of file size
                    ("dwReserved0", ctypes.c_uint32),        # Reserved (set to 0)
                    ("dwReserved1", ctypes.c_uint32),        # Reserved (set to 0)
                    ("cFileName", ctypes.c_wchar * 260),     # File name (path)
                    ("cAlternateFileName", ctypes.c_wchar * 14)  # 8.3 format short name
                ]

            MAX_PATH = 260
            INVALID_HANDLE_VALUE = 2**64-1
            EPOCH_DIFF = 116444736000000000  # Difference between FILETIME epoch and Unix epoch
            TICKS_PER_SECOND = 10**7  # Number of 100-nanosecond intervals per second


            # Constants for file attributes (from Windows API)
            FILE_ATTRIBUTE_READONLY = 0x01
            FILE_ATTRIBUTE_HIDDEN = 0x02
            FILE_ATTRIBUTE_SYSTEM = 0x04
            FILE_ATTRIBUTE_DIRECTORY = 0x10
            FILE_ATTRIBUTE_ARCHIVE = 0x20
            FILE_ATTRIBUTE_NORMAL = 0x80

            # Load kernel32.dll
            kernel32 = ctypes.WinDLL('kernel32', use_last_error=True)

            # Function prototypes for FindFirstFile, FindNextFile, and FindClose
            FindFirstFileW = kernel32.FindFirstFileW
            FindFirstFileW.argtypes = [ctypes.c_wchar_p, ctypes.POINTER(WIN32_FIND_DATA)]
            FindFirstFileW.restype = ctypes.c_void_p  # Returns handle or INVALID_HANDLE_VALUE

            FindNextFileW = kernel32.FindNextFileW
            FindNextFileW.argtypes = [ctypes.c_void_p, ctypes.POINTER(WIN32_FIND_DATA)]
            FindNextFileW.restype = ctypes.c_bool  # Returns True on success, False on failure

            FindClose = kernel32.FindClose
            FindClose.argtypes = [ctypes.c_void_p]
            FindClose.restype = ctypes.c_bool  # Returns True on success

            # Create a WIN32_FIND_DATA object to hold the result
            find_data = WIN32_FIND_DATA()

            # Stack is relative to self.dirpath
            dirpath_stack = [""]
            handle = INVALID_HANDLE_VALUE
            try:
                logger.info("Reading next entries")
                fileinfo_ready = False
                while (not self.mustAbort()):
                    if (not fileinfo_ready):
                        if (handle != INVALID_HANDLE_VALUE):
                            assert None is logger.debug("Closing handle 0x%x", handle)
                            FindClose(handle)
                            handle = INVALID_HANDLE_VALUE
                        if (len(dirpath_stack) == 0):
                            break
                        # Start the search
                        dirpath = dirpath_stack.pop()
                        # Add wildcard, required by FindFirstFile
                        abs_dirpath = os.path.join(self.dirpath, dirpath, "*")
                        assert None is logger.debug("Reading first entry for %r %r %r", dirpath, self.dirpath, abs_dirpath)
                        handle = FindFirstFileW(unicode(abs_dirpath), ctypes.byref(find_data))
                        
                        if (handle == INVALID_HANDLE_VALUE):
                            logger.warn("Unable to open directory or invalid path %r %r %r" % (dirpath, self.dirpath, abs_dirpath))
                            continue

                    # Fetch the filename
                    filename = find_data.cFileName

                    # FindFirst returns both "." and "..", ignore "."
                    if (filename != "."):
                        is_dotdot = (filename == "..")
                        filename = os.path.join(dirpath, find_data.cFileName)
                        
                        is_dir = ((find_data.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) != 0)
                        is_readonly = ((find_data.dwFileAttributes & FILE_ATTRIBUTE_READONLY) != 0)
                        is_hidden = ((find_data.dwFileAttributes & FILE_ATTRIBUTE_HIDDEN) != 0)

                        file_info = FileInfo(
                            filename, 
                            # Symlinks return the size of the target, not the symlink
                            # file, use os.path instead. There's a way to get the size
                            # of the .lnk file, but it's involved having to read the
                            # file, etc
                            # https://stackoverflow.com/questions/53411886/qfileinfo-size-is-returning-shortcut-target-size
                            find_data.nFileSizeHigh * 2**32 + find_data.nFileSizeLow, 
                            # XXX Check if this is also returning the wrong date for .lnk files
                            # XXX Find out if this is UTC, fix UTC elsewhere
                            (((find_data.ftLastWriteTime.dwHighDateTime << 32) | find_data.ftLastWriteTime.dwLowDateTime) - EPOCH_DIFF) / TICKS_PER_SECOND,
                            fileinfo_build_attr(is_dir, is_hidden, not is_readonly)
                        )

                        if (is_dir):
                            dir_infos_set.add(file_info)
                            if ((self.recurse) and not (is_dotdot)):
                                dirpath_stack.append(filename)

                        else:
                            file_infos.append(file_info)
                    
                    # Continue fetching the next file
                    fileinfo_ready = FindNextFileW(handle, ctypes.byref(find_data))
                    #logger.info("FindNext 0x%x %r %r", handle, res, find_data.cFileName)
                        
                    # emit when done with this dir (also done for good if not
                    # recursing) or this batch
                    if ((not fileinfo_ready) or ((self.batch_size is not None) and (len(file_infos) + len(dir_infos_set)) > self.batch_size)):
                        assert None is logger.debug("Sorting %d + %d", len(file_infos), len(dir_infos_set))
                        file_infos = sorted(dir_infos_set, key=lambda a: a.filename.lower()) + sorted(file_infos, key= lambda a: a.filename.lower())
                        
                        assert None is logger.debug("Emitting %d + %d", len(file_infos), len(dir_infos_set))
                        self.direntryRead.emit(dir_infos_set, file_infos)

                        dir_infos_set = set()
                        file_infos = []
            finally:
                if (handle != INVALID_HANDLE_VALUE):
                    logger.info("Closing handle 0x%x", handle)
                    FindClose(handle)
                    handle = INVALID_HANDLE_VALUE

        elif (use_diriterator):
            # Use positional arguments to QDirIterator since keyword arguments
            # seem to fail with "unknown keyword argument"?

            it = QDirIterator(
                unicode(self.dirpath), 
                [("*%s" % ext) for ext in IMAGE_EXTENSIONS] if (len(FILTERED_EXTENSIONS) > 0) else ["*"], 
                QDir.Files | QDir.AllDirs | QDir.NoDot | QDir.Hidden | QDir.System, 
                QDirIterator.Subdirectories if self.recurse else QDirIterator.NoIteratorFlags)

            dir_infos_set = set()
            file_infos = []
            last_sleep_time = time.time()
            logger.info("Reading dir")
            while (it.hasNext() and (not self.mustAbort())):
                #logger.info("Nexting %d", len(file_infos))
                # On slow drives it.next() stalls for ~2s every ~650 entries.
                # Unfortunately that seems to be a blocking stall (Qt or GIL)
                # that prevents the UI thread from doing anything
                it.next()
                
                #logger.info("Filenaming")
                if (self.recurse):
                    # When recursive, return the path relative to the requested
                    # dirpath
                    filename = os.path.relpath(it.filePath(), self.dirpath)
                else:
                    filename = it.fileName()
                #logger.info("isDiring")
                is_dir = it.fileInfo().isDir()

                #logger.info("read entry %r %s", filename, is_dir)

                file_info = FileInfo(
                    filename, 
                    # Symlinks return the size of the target, not the symlink
                    # file, use os.path instead. There's a way to get the size
                    # of the .lnk file, but it's involved having to read the
                    # file, etc
                    # https://stackoverflow.com/questions/53411886/qfileinfo-size-is-returning-shortcut-target-size
                    os.path.getsize(it.fileInfo().filePath()) if it.fileInfo().isSymLink() else it.fileInfo().size(), 
                    # XXX Check if this is also returning the wrong date for .lnk files
                    # XXX Find out if this is UTC, fix UTC elsewhere
                    it.fileInfo().lastModified().toMSecsSinceEpoch() / 1000, 
                    fileinfo_build_attr(is_dir, it.fileInfo().isHidden(), it.fileInfo().isWritable())
                )

                if (is_dir):
                    dir_infos_set.add(file_info)

                else:
                    file_infos.append(file_info)

                if (False):
                    if (((time.time() - last_sleep_time) > 0.01)):
                        logger.info("Sleeping")
                        # Even on slow devices, yieldCurrentThread() is not good
                        # enough for keeping the UI thread responsive, do a
                        # msleep(1) for tradeoff between UI responsiveness and 

                        # XXX Should this be done by number of entries? when entries
                        #     are fast, there's need to sleep, when entries are slow
                        #     there's no need because reading the entry should allow
                        #     other threads to work?
                        time.sleep(0.01)
                        last_sleep_time = time.time()
                
                # XXX The merge delete mode needs all the entries, otherwise
                #     valid entries are deleted
                if ((not it.hasNext()) or ((self.batch_size is not None) and (len(file_infos) + len(dir_infos_set)) > self.batch_size)):
                    logger.info("Sorting")
                    file_infos = sorted(dir_infos_set, key=lambda a: a.filename.lower()) + sorted(file_infos, key= lambda a: a.filename.lower())
                    
                    logger.info("Emitting")
                    self.direntryRead.emit(dir_infos_set, file_infos)

                    dir_infos_set = set()
                    file_infos = []

        else:
            assert not self.recurse, "Recursion not supported yet on the listdir path"
            dir_infos_set = set([FileInfo("..", 0, 0, fileinfo_build_attr(True, False, True))] if (os.path.dirname(self.dirpath) != self.dirpath) else [])
            file_infos = []
            
            # listdir takes ~34s. and processing another ~30s on slow drives. UI
            # is very responsive, none of the two seem to take. This was on a
            # directory with lots of images and 2 subdirs, but also lots of mp4,
            # which explains the slowness in processing (isdir path being hit),
            # once .mp4 are added to the extensions, the processing time is
            # negligible.
            logger.info("listdiring")
            # Force unicode on listdir parameter so results are unicode too
            l = os.listdir(unicode(self.dirpath))
            logger.info("processing")

            # XXX Sort first and emit later in batches at processing time? But
            #     cannot be done until directories are known, which is at
            #     processing time anyway. Sort after the fact?
            for filename in l:
                #if (self.mustAbort()):
                #    break
                filepath = os.path.join(self.dirpath, filename)
                # XXX os.stat/os.path.isdir can be slow on network drives
                st = os.stat(filepath)
                is_dir = os.path.isdir(filepath)
                #is_dir = stat.S_ISDIR(st.st_mode)
                size = 0
                #size = st.st_size
                mtime = 0
                #mtime =  st.st_mtime
                file_info = FileInfo(filename, size, mtime, fileinfo_build_attr(is_dir, False, True))
                if (is_dir):
                    dir_infos_set.add(file_info)

                elif ((len(FILTERED_EXTENSIONS) == 0) or filename.lower().endswith(FILTERED_EXTENSIONS)):
                    file_infos.append(file_info)

                else:
                    logger.info("Ignoring filtered out file %r", filename)

            if (not self.mustAbort()):
                logger.info("sorting")
                # XXX Could sort by date but can be slow on network drives
                file_infos = sorted(dir_infos_set, key=lambda a: a.filename.lower()) + sorted(file_infos, key= lambda a: a.filename.lower())

                logger.info("Emitting")
                self.direntryRead.emit(dir_infos_set, file_infos)

        logger.info("Aborted" if (self.mustAbort()) else "Ended" )
        
        self.quit()

class PixmapReader(QThread):
    """
    Thread in charge of reading an image, possibly from a slow network drive,
    decoding and scaling it, allowing the UI thread to be responsive.

    Care was taken to find the best operations found that release the GIL and
    don't block the UI thread.

    It's important to test fast sources (as opposed to slow sources like network
    drives) to check for UI blocks because on slow sources threads are most of
    the time blocked by reads, which don't block the UI. On fast sources, there
    are lots of image decoding  that may cause UI blocks depending on the method
    used

    The only shared resource with the UI thread this thread modifies is the
    request queue, emitting a signal when done which will be handled in the UI
    thread.
    """
    pixmapRead = pyqtSignal(int, str, QPixmap)
    def __init__(self, request_queue, parent=None):
        super(PixmapReader, self).__init__(parent)
        self.request_queue = request_queue
        
    def run(self):
        request_queue = self.request_queue
        while (True):
            # XXX Arguably this should fetch from the end of the queue which has
            #     the most recent items in case initial items were made stale by
            #     scrolling away? (but the request queue is cleared in
            #     receive_pixmap and new requests issued for visible items, so
            #     most of the time it should only contain non-stale items)
            data = request_queue.get()
            if (data is None):
                break
            row, filepath = data
            logger.info("%d %r", row, filepath)
            try:
                with open(filepath, "rb") as f:
                    # XXX On slow connections visible items can be behind stale
                    #     items. read() could chunk and check for a flag stating
                    #     whether this is a stale item and it should be discarded.
                    #     But note detecting when an item is stale is not trivial.
                    if (use_pil):
                        try:
                            # Note open doesn't load the image need to call .load()
                            # or some other function that causes the load, eg
                            # .thumbnail()
                            
                            # XXX Investigate if the exif information reads the
                            #     whole image or only the header so PIL could be
                            #     used efficiently for exif only and Qt for
                            #     decoding?
                            logger.info("opening")
                            img = Image.open(f)

                            # Reduce size before rotating and, more importantly,
                            # before converting to QPixmap, since that seems to take
                            # a very long time and blocks the UI. This puts the PIL
                            # path in comparable time and memory than the Qt path

                            # XXX Not clear the above is true wrt speed, it was done
                            #     using a slow source which masks UI blocking

                            # XXX Investigate why QPixmap conversion takes a long
                            #     time?
                            # This takes 7s on remote drives
                            logger.info("thumbnailing")
                            img.thumbnail((IMAGE_WIDTH, IMAGE_HEIGHT))

                            logger.info("exifing")
                            # Not all file formats have exif (eg PNG), guard against
                            exif_data = img._getexif() if hasattr(img, "_getexif") else None
                            if (exif_data is not None):
                                for tag, value in exif_data.items():
                                    decoded_tag = ExifTags.TAGS.get(tag, tag)
                                    if (decoded_tag == 'Orientation'):
                                        logger.info("Found exif orientation %r", value)
                                        if (value == 3):
                                            img = img.rotate(180, expand=True)
                                        elif (value == 6):
                                            img = img.rotate(-90, expand=True)
                                        elif (value == 8):
                                            img = img.rotate(90, expand=True)

                            logger.info("toqpixmapping")
                            pixmap = ImageQt.toqpixmap(img)
                            logger.info("closing")
                            img.close()
                            img = None
                        except Exception as e: 
                            # - PIL sometimes errors with broken data stream
                            # IOError: broken data stream when reading image file
                            # - PIL sometimes errors with "unsupported image mode 'CMYK'"
                            # XXX Fall-back to image-reader on failure, at least
                            #     CMYK jpeg is supported there
                            # XXX Merge this with the external exception?
                            logger.error("PIL Error loading %r %s", filepath, e)
                            pixmap = QPixmap()

                    elif (use_image_reader):
                        logger.info("reading")
                        data = f.read()
                        buffer = QBuffer()
                        buffer.setData(data)
                        # XXX Recycle QImageReaders in this thread? Not clear how
                        #     slow it is to create on every request and there are
                        #     known bugs reusing QImageReader
                        reader = QImageReader(buffer)
                        logger.info("readering")
                        image = reader.read()
                        logger.info("fromimaging")
                        pixmap = QPixmap.fromImage(image)
                        # Don't hold on to these while blocking for requests and
                        # garbage collection. With 10 threads and ~3MB jpegs, this
                        # reduces memory consumption from ~500MB to ~70MB
                        reader = None
                        image = None
                        data = None
                        
                    else:
                        data = f.read()
                        pixmap = QPixmap()
                        # This seems to cause more UI blocking, UI is less
                        # responsive, probably there's a single QImageReader?
                        pixmap.loadFromData(data)
                        data = None
            
            except Exception as e:
                # XXX This is normally hit when trying to fetch images for stale
                #     direntries on the non-stale image directory, fix that case
                #     since it fills the thumbs with stale error thumgs, but
                #     still handle exceptions since network could be down, etc
                logger.error("Open Error loading %r %s", filepath, e)
                pixmap = QPixmap()

            if (not pixmap.isNull()):
                # XXX Resizing here is good for multithreading, but may want to
                #     return the full size pixmap, get a size parameter with the
                #     request?
                # XXX Also, storing borders is wasted memory in the cache
                # XXX Skip resizing if it's already the target size
                #pixmap = pixmap.scaled(IMAGE_WIDTH, IMAGE_HEIGHT, Qt.IgnoreAspectRatio, Qt.SmoothTransformation)
                # XXX This is not needed on the PIL path
                pixmap = qResizePixmap(pixmap, IMAGE_WIDTH, IMAGE_HEIGHT)
            logger.info("done with %d %r", row, filepath)

            self.pixmapRead.emit(row, filepath, pixmap)

class DirectoryModel(QAbstractTableModel):
    """
    - incremental loading by returning loaded rows from rowCount and
      canFetchMore/fetchMore
    - LRU caching

    XXX Look into QFileSystemModel
    
    """
    def __init__(self, page_size=10):
        super(DirectoryModel, self).__init__()

        self.page_size = page_size
        self.directoryReader = None

        # Create the bare minimum so things don't crash
        self.file_dir = None
        self.loaded_rows = 0
        self.file_infos = []
        self.dir_infos_set = set()
        
        def receive_pixmap(row, filepath, pixmap):
            """
            Receive a pixmap from the PixmapReader thread. Put it in the cache
            for the given key and trigger datachanged for the given row.

            This is connected to a signal fired by in the PixmapReader and runs
            in the UI thread, so it's safe to modiy the cache, etc.
            """
            logger.info("row %d %r", row, filepath)
            
            key = os.path.basename(filepath)
            self.request_set.remove(key)
            
            if (os.path.dirname(filepath) != self.file_dir):
                # The directory was navigated away and this is a stale image
                # from a previous directory. setDirectory clears the caches
                # (since the key is the filename and not the filepath, so
                # different directories cannot share the cache) so the
                # cacheImage call below will fail . The PixmapReader thread will
                # still send these since it has no knowledge that it's stale.
                # The request queue will be emptied below from all stale
                # requests. The incoming row also refers to the previous grid
                # and, although the new grid may have that row number, it's not
                # valid either, so don't do anything with those invalid data.

                # XXX Make the caches shareable across directories? Would
                #     simplify and help if the old dir is navigated to. The
                #     cache already has bounds anyway?
                logger.info("Ignoring stale image %r", filepath)

            else:
                if (pixmap.isNull()):
                    logger.error("Error receiving %r", filepath)
                    pixmap = self.image_cache[":error"]
                    
                self.cacheImage(key, pixmap)
                # Emit dataChanged for the specific item
                index = self.createIndex(row, 0)
                self.dataChanged.emit(index, index, [Qt.DecorationRole])
            
            # Empty the request queue to discard stale requests from items no
            # longer in view. By emitting a datachanged for each discarded item,
            # the current Qt implementation will ignore the datachanged for
            # items scrolled out and will re-issue data() calls for items in
            # view. This is a simple solution to the hard problem of only
            # servicing requests for items in view, since there's no easy way to
            # do that, and even less from the model.

            # XXX This has two drawbacks, none of them fatal:
            #     - Causes redundant calls to data() for the items in view until
            #       the items in view have been fetched. This is a minor problem.
            #     - Causes items that are displaying the right image to
            #       momentarily show the requesting placeholder. This is
            #       empirically happening, but it's not clear the full reason, in
            #       theory an item can only be here if there's a request for it,
            #       and there should only be a request for it if it has the
            #       requesting placeholder?
            
            # XXX Could use a heuristic that only removes requests "away" from
            #     the last queued request, since that should be the the most
            #     recent data() call

            try:
                while (True):
                    row, filepath = self.request_queue.get_nowait()
                    key = os.path.basename(filepath)
                    logger.debug("purging request row %d %r", row, filepath)
                    assert key in self.request_set
                    assert key not in self.image_cache
                    self.request_set.remove(key)

                    # Trigger new requests, ignore stale requests
                    if (os.path.dirname(filepath) == self.file_dir):
                        index = self.createIndex(row, 0)
                        self.dataChanged.emit(index, index, [Qt.DecorationRole])

                    else:
                        logger.info("Ignoring purged stale request %r vs. %r", filepath, self.file_dir)

            except Queue.Empty:
                pass
            
        self.request_queue = Queue.Queue()
        self.request_set = set()
        self.pixmapReaders = [PixmapReader(self.request_queue) for _ in xrange(READING_THREADS)] 
        for pixmapReader in self.pixmapReaders:
            pixmapReader.pixmapRead.connect(receive_pixmap)
            pixmapReader.start()

    def findFileInfoRow(self, filename):
        return [f.filename for f in self.file_infos].index(filename)

    def getFiles(self, insert_only = False):
        logger.info("reading dir")

        def receive_direntry(dir_infos_set, file_infos):
            self.mergeDirEntries(dir_infos_set, file_infos, insert_only)
            # New files received, there are begin and delete emits that will
            # update the view if they are visible, but if loaded_rows is not the
            # maximum, it could happen that directories are not shown. Call
            # fetchmore to guarantee that at least directories are shown
            if (self.rowCount() < len(self.dir_infos_set)):
                self.fetchMore(QModelIndex())
            
        if ((self.directoryReader is not None) and self.directoryReader.isRunning()):
            # Stop signals from the old thread, they are probably form a
            # previous directory listing and they would to the current grid but
            # fail to load due to the changed path
            logger.info("Disconnecting signal from old DirectoryReader finished %s running %s", self.directoryReader.isFinished(), self.directoryReader.isRunning())
            self.directoryReader.direntryRead.disconnect()
            self.directoryReader.abort()

        # Batch and deletions are incompatible since, it cannot detect deletions
        # vs. a partial list (batch), only batch if insert_only
        
        # XXX This gets blocked behind image load, pause image loading while
        #     entries are being read
        self.directoryReader = DirectoryReader(self.file_dir, 500 if insert_only else None)
        self.directoryReader.direntryRead.connect(receive_direntry)
        self.directoryReader.start()

    def calculateSubdirSizes(self, subdir_index=QModelIndex()):
        """
        - subdir_index is a directory then calculate sizes for that subdir
        - subdir_index is invalid then calculate sizes for all subdirs in the
          table view
        """
        logger.info("reading dir")

        # XXX Allow to queue multiple single directory requests
        subdir_fileinfo = self.file_infos[subdir_index.row()]
        subdir = subdir_fileinfo.filename if subdir_index.isValid() else None

        subdir_sizes = {}

        def set_fileinfo_size(row, size):
            logger.info("row %d, size %d", row, size)
            # XXX Remove dir_infos_set completely? use nameddicts so file_info
            #     can be modified vs. recreated?

            file_info = self.file_infos[row]
            self.dir_infos_set.remove(file_info)
            file_info = file_info._replace(size = size)
            self.dir_infos_set.add(file_info)
            self.file_infos[row] = file_info

            index = self.index(row, 3)
            # XXX This is really slow with 10s of directories, coalesce?
            # self.dataChanged.emit(index, index, [Qt.DisplayRole, Qt.UserRole, Qt.DecorationRole])
            
            return file_info

        current_state = {}
        current_state["subdir_row"] = None
        current_state["subdir"] = None
        # XXX This probably doesn't need a set since directories are sequential
        #     and should be added only once?
        dirty_rows = set()
        def receive_direntry(dir_infos_set, file_infos):
            # DirIterator issues
            # - recurse sends dot even if nodot is set
            # - recurse doesn't send dot or dotdot for a subdir if the directory
            #   is empty
            assert None is logger.debug("Received direntry %s", file_infos)

            # Note because of using named tuples, subdir_fileinfo reference
            # changes on every size modification, refresh it
            # subdir_fileinfo = self.file_infos[subdir_index.row()]
            # Size is negative while it's being calculated
            #size = subdir_fileinfo.size - sum([file_info.size for file_info in file_infos])
            
            # XXX This breaks when calculating for a single subdir and the
            #     subdir has subdirs, fix
            for file_info in file_infos:
                this_subdir = os_path_root(file_info.filename)
                this_subdir = subdir if (subdir is not None) else this_subdir 
                # Note this will store the current dir size in the None entry
                # XXX This could update the model incrementally with a negative
                #     size but this is faster than emitting signals etc and the "?"
                #     indicator is good enough?
                if (this_subdir is not None):
                    if (current_state["subdir"] != this_subdir):
                        # This is the first time this directory is updated,
                        # change icon to being updated and finalize the size for
                        # the subdir previuosly being updated
                        
                        # XXX When calculating sizes of multiple top level
                        #     directories, the order of completion is
                        #     counter-intuitive because it's done in filesystem
                        #     order, not in table order, this should find the
                        #     directories and queue them in table order instead
                        #     of recursing at the top?
                        if (current_state["subdir_row"] is not None):
                            set_fileinfo_size(current_state["subdir_row"], subdir_sizes[current_state["subdir"]])
                            current_state["subdir"] = subdir
                        row = self.findFileInfoRow(this_subdir)
                        current_state["subdir_row"] = row
                        current_state["subdir"] = this_subdir
                        set_fileinfo_size(current_state["subdir_row"], -2)

                        dirty_rows.add(row)

                        if (len(dirty_rows) > 100000):
                            refresh_rows(list(dirty_rows))
                            dirty_rows.clear()

                    subdir_sizes[this_subdir] += file_info.size

        def refresh_rows(rows):
            """
            Given a list of rows, find runs inside it and emit the minimum
            number of dataChanged signals
            """
            # Most of the time this is called for rows of directories, which are
            # consecutive and form a single consecutive run, use min and max
            # instead of run searching. 
            rows = sorted(rows)

            min_row = rows[0]
            max_row = rows[-1]
            if ((max_row - min_row + 1) == len(rows)):
                start_run= min_row
                end_run = max_row
                logger.info("datachanged minmax [%d, %d]", start_run, end_run)
                index_start = self.index(start_run, 3)
                index_end = self.index(end_run, 3)
                self.dataChanged.emit(index_start, index_end, [Qt.DisplayRole, Qt.UserRole, Qt.DecorationRole])
                return
            
            # Set end < start and end != 0 so it starts by recording the start
            # of the initial run
            start_run = 0
            end_run = -1
            for i, row in enumerate(rows):
                # Spill a run when non consecutive row is found or if this is
                # the last row
                if (row != end_run + 1) or (i == (len(rows) - 1)):
                    if (end_run >= start_run):
                        logger.info("datachanged [%d, %d]", start_run, end_run)
                        index_start = self.index(start_run, 3)
                        index_end = self.index(end_run, 3)
                        
                        self.dataChanged.emit(index_start, index_end, [Qt.DisplayRole, Qt.UserRole, Qt.DecorationRole])

                    start_run = row

                end_run = row

        def finish_size_calculation():
            assert None is logger.debug("subdir_sizes %s file_infos %s", subdir_sizes, self.file_infos)
            rows = []
            for key, size in subdir_sizes.iteritems():
                # Ignore the sum for the current directory stored in [None]
                if (key is not None):
                    row = self.findFileInfoRow(key)
                    # XXX This causes an emit that seems to be pretty slow looking
                    #     at the logs, all the directories should be lumped
                    #     together, try to coalesce all the emits?
                    set_fileinfo_size(row, size)
                    rows.append(row)
            # XXX Empty directories won't have an entry in subdir_sizes, need to 
            #     clear them, but why no ".." entry in empty directories?
            refresh_rows(rows)

        if ((self.directoryReader is not None) and self.directoryReader.isRunning()):
            # Stop signals from the old thread, they are probably form a
            # previous directory listing and they would to the current grid but
            # fail to load due to the changed path
            logger.info("Disconnecting signal from old DirectoryReader finished %s running %s", self.directoryReader.isFinished(), self.directoryReader.isRunning())
            self.directoryReader.direntryRead.disconnect()
            self.directoryReader.abort()

        
        for row in xrange(len(self.file_infos)):
            file_info = self.file_infos[row]
            # Clear all directory sizes but for ".." if subdir is None, only
            # subdir otherwise
            if (fileinfo_is_dir(file_info) and (
                (not subdir_index.isValid() and (file_info.filename != "..")) or (file_info.filename == subdir)
                )):
                # Force create entries for all root directories, DirIterator
                # won't create and then they fail to be reset below
                subdir_sizes[file_info.filename] = 0
                # XXX This causes an emit that seems to be pretty slow looking
                #     at the logs, all the directories should be lumped
                #     together, try to coalesce all the emits?
                set_fileinfo_size(row, -1) 

        subdir_sizes[None] = 0

        # XXX This gets blocked behind image load, pause image loading while
        #     entries are being read
        self.directoryReader = DirectoryReader(self.file_dir if subdir is None else os.path.join(self.file_dir, subdir), 100, recurse=True)
        self.directoryReader.direntryRead.connect(receive_direntry)
        self.directoryReader.finished.connect(finish_size_calculation)
        self.directoryReader.start()
        
    def reloadDirectory(self):
        # Reload and merge the new entries to not perturb the UI
        self.getFiles()

    def mergeDirEntries(self, new_dir_infos_set, new_file_infos, insert_only = False):
        # XXX This needs to put ".." the first entry explicitly, just sorting
        #     alphabetically it's possible it's not. Add it manually instead of
        #     getting it from DirectoryReader?

        # XXX Test if blocksignals help with speed
        # self.blockSignals(True)
        logger.info("")
        #logger.info("%s %s", new_dir_infos_set, new_file_infos)
        i_old = 0
        i_new = 0
        while (True):
            f_old = self.file_infos[i_old] if (i_old < len(self.file_infos)) else None
            f_new = new_file_infos[i_new] if (i_new < len(new_file_infos)) else None

            if ((f_old is None) and (f_new is None)):
                break

            is_dir_new = ((f_new is not None) and fileinfo_is_dir(f_new))
            is_dir_old = ((f_old is not None) and fileinfo_is_dir(f_old))
            
            # Traverse in sort order: directories first, alphabetical second
            # XXX Directories are on its own lists, this could do directory
            #     sorting and then file sorting?
            assert None is logger.debug("Comparing old %r vs. new %r", f_old, f_new)
            if ((f_old is not None) and (f_new is not None) and (f_old.filename == f_new.filename)):
                i_old += 1
                i_new += 1

            elif ((f_new is None) or ((f_old is not None) and 
                (
                    # f_old is a directory and f_new is not
                    (is_dir_old and not is_dir_new) or 
                    # f_old and f_new are both files or directories and f_old is
                    # alphabetically first
                    ((is_dir_old == is_dir_new) and (f_old.filename.lower() < f_new.filename.lower()))
                )
                )):
                if (insert_only):
                    i_old += 1

                else:
                    # f_old was deleted
                    assert None is logger.debug("Deleted %r", f_old)
                    # Prevent triggering "Invalid index", only report removal if
                    # row was loaded, but report if all the rows have been loaded
                    is_loaded_row = (i_old < self.loaded_rows)
                    if (is_loaded_row):
                        self.beginRemoveRows(QModelIndex(), i_old, i_old)
                    self.file_infos.pop(i_old)
                    
                    if (is_loaded_row):
                        self.loaded_rows -= 1
                        self.endRemoveRows()

                    if (f_old in self.image_cache):
                        del self.image_cache[f_old]
                        self.lru_image_keys.remove(f_old)
                
            else:
                # f_new was added
                assert None is logger.debug("Inserted %r", f_new)
                
                # Prevent triggering "Invalid index", only report insertion if
                # row was loaded, including after the last loaded row, which
                # takes care of forcing a refresh when file_infos increase
                # (otherwise the view is stale if files are added when
                # loaded_rows == len(file_infos) )
                is_loaded_row = (i_old <= self.loaded_rows)
                if (is_loaded_row):
                    self.beginInsertRows(QModelIndex(), i_old, i_old)
                self.file_infos.insert(i_old, f_new)
                if (is_loaded_row):
                    self.loaded_rows += 1
                    self.endInsertRows()
                i_new += 1
                i_old += 1

        # assert len(self.file_infos) == len(new_file_infos)
        # assert self.file_infos == new_file_infos
        
        if (insert_only):
            self.dir_infos_set |= new_dir_infos_set
        else:
            self.dir_infos_set = new_dir_infos_set

        # self.blockSignals(False)
        # self.layoutChanged.emit()
        logger.info("Done")


    def setDirectory(self, file_dir):
        # XXX This needs to idle the threads
        # XXX Also treat archives (.zip, etc) as directories?
        # XXX Remember selections per directory?

        self.beginResetModel()

        self.file_dir = file_dir
        self.loaded_rows = 0
        self.file_infos = []
        self.dir_infos_set = set()
        
        # XXX getFiles can fail for eg permission errors, don't set file_dir
        #     until getFiles works and return error or raise
        self.getFiles(True)

        # XXX Use QCache, have a multilevel cache:
        #     - full res pixmap
        #     - thumbnail pixmap
        #     - pixmap raw file on memory
        #     - thumbnail raw file on memory
        #     - pixmap mmapped file
        #     - thumbnail mmapped file
        #     - pixmap file on disk
        #     - thumbnail on disk
        #     - disk cache of pixmap file
        #     - disk cache of thumbnail file
        self.image_cache = {}
        self.lru_image_keys = []

        # Note these special images don't have LRU entries, so they will never
        # be deleted
        self.image_cache[":error"] = QPixmap(IMAGE_WIDTH, IMAGE_HEIGHT)
        self.image_cache[":error"].fill(Qt.red)

        self.image_cache[":requesting"] = QPixmap(IMAGE_WIDTH, IMAGE_HEIGHT)
        self.image_cache[":requesting"].fill(Qt.yellow)

        self.image_cache[":requested"] = QPixmap(IMAGE_WIDTH, IMAGE_HEIGHT)
        self.image_cache[":requested"].fill(Qt.blue)

        self.image_cache[":purged"] = QPixmap(IMAGE_WIDTH, IMAGE_HEIGHT)
        self.image_cache[":purged"].fill(Qt.blue)

        dir_icon = qApp.style().standardIcon(QStyle.SP_DirIcon)
        self.image_cache[":directory_icon"] = dir_icon
        pixmap = qResizePixmap(dir_icon.pixmap(256, 256), IMAGE_WIDTH, IMAGE_WIDTH)
        self.image_cache[":directory"] = pixmap

        dir_icon = qApp.style().standardIcon(QStyle.SP_FileDialogNewFolder)
        dir_icon = qApp.style().standardIcon(QStyle.SP_BrowserReload)
        self.image_cache[":directory_sizing_icon"] = dir_icon

        dir_icon = qApp.style().standardIcon(QStyle.SP_MessageBoxCritical)
        self.image_cache[":file_system_icon"] = dir_icon

        dir_icon = qApp.style().standardIcon(QStyle.SP_MessageBoxWarning)
        self.image_cache[":file_hidden_icon"] = dir_icon

        dir_icon = qApp.style().standardIcon(QStyle.SP_DialogOkButton)
        self.image_cache[":directory_up_icon"] = dir_icon
        pixmap = qResizePixmap(dir_icon.pixmap(256, 256), IMAGE_WIDTH, IMAGE_WIDTH)
        self.image_cache[":directory_up"] = pixmap

        dir_icon = qApp.style().standardIcon(QStyle.SP_FileIcon)
        self.image_cache[":file_icon"] = dir_icon
        pixmap = qResizePixmap(dir_icon.pixmap(256, 256), IMAGE_WIDTH, IMAGE_WIDTH)
        self.image_cache[":file"] = pixmap

        self.endResetModel()

    def cacheImage(self, key, pixmap):
        """
        Put the image with the given key in the cache, possibliy evicting older
        images.
        """
        # XXX This guards against stale images when changing directories and
        #     self.file_infos is empty which raises in .index below, remove for
        #     perf?
        logger.info("key %s, index %d/%d cached %d %d loaded %d", 
            key, self.findFileInfoRow(key) if key in self.file_infos else -1, len(self.file_infos),
            len(self.image_cache), len(self.lru_image_keys), 
            self.loaded_rows
        )
        if (len(self.image_cache) > MAX_CACHE_ENTRIES):
            logger.info("purging cache %s", [self.findFileInfoRow(purge_key) for purge_key in self.lru_image_keys[:MAX_CACHE_ENTRIES_WATERMARK]])
            for purge_key in self.lru_image_keys[:MAX_CACHE_ENTRIES_WATERMARK]:
                #self.image_cache[purge_key].fill(Qt.blue)
                del self.image_cache[purge_key]
            self.lru_image_keys[:] = self.lru_image_keys[MAX_CACHE_ENTRIES_WATERMARK:]

        self.lru_image_keys.append(key)
        self.image_cache[key] = pixmap

    def headerData(self, section, orientation, role=Qt.DisplayRole):
        logger.debug("section %d orientation %d role %d", section, orientation, role)
        if (role == Qt.DisplayRole):
            sections = [ "Fullname", "Name", "Ext", "Size", "Date", "Attr" ]
            if (orientation == Qt.Vertical):
                return "Row %d" % section
            elif (orientation == Qt.Horizontal):
                return sections[section]

        return None
    
    def data(self, index, role):
        """ Lazy load the image data only when requested """
        if (not index.isValid() or (index.row() >= self.rowCount())):
            return None

        file_info = self.file_infos[index.row()]

        if (index.column() > 1):
            if (role == Qt.DecorationRole):
                return None

        if (role == Qt.TextAlignmentRole):
            if (index.column() == 3):
                return Qt.AlignRight
            if (index.column() == 2):
                return Qt.AlignRight
            

        if (role == Qt.EditRole):
            return file_info.filename

        if (role == Qt.DisplayRole):
            t = file_info.filename
            is_dir = fileinfo_is_dir(file_info)
            if (is_dir):
                t = "[%s]" % t
                
            if (index.column() == 0):
                pass

            elif (index.column() == 1):
                if (not is_dir):
                    t = os.path.splitext(t)[0]
            
            elif (index.column() == 2):
                if (is_dir):
                    # Directory sizes span the extension and size columns and
                    # the data is associated to the extension
                    if (file_info.size < 0):
                        # Size is being calculated in the background
                        # XXX Find a magic number to show when this calculation
                        #     is active vs. queued behind another calculation
                        
                        # XXX Directories don't have extension, allow the the
                        #     size should be allowed to expand the extension column
                        t = "?"

                    elif (file_info.size == 0):
                        t = "<DIR>"
                    else: 
                        t = QLocale().toString(file_info.size)
                    # t = "12345678901234567890"

                else:
                    t = os.path.splitext(t)[1]

            elif (index.column() == 3):
                if (is_dir):
                    # XXX Looks like this is taking some space in the spanned column, investigate?
                    # XXX Make sure this doesn't break code that relies on size being 3
                    return None
                else:
                    size = file_info.size
                    t = QLocale().toString(size)

            elif (index.column() == 4):
                # XXX Fix UTC?
                t = datetime.datetime.fromtimestamp(file_info.mtime)
                # XXX Get this from locale
                t = t.strftime("%Y-%m-%d %H:%M:%S")
                
            elif (index.column() == 5):
                t = "-%s-%s"  % ("r" if (not fileinfo_is_writable(file_info)) else "-", "h" if fileinfo_is_hidden(file_info) else "-")
            
            # Cap the length so they are guaranteed to have uniform sizes
            # Note that itemdelegate adds 2*QStyle::PM_FocusFrameHMargin to the width of the text
            # t = qApp.fontMetrics().elidedText(t, Qt.ElideMiddle, DISPLAY_WIDTH - 2 * qApp.style().pixelMetric(QStyle.PM_FocusFrameHMargin))
            # Getting this wrong over DISPLAY_WITH causes layout issues when
            # enabling uniformsizes
            if (not use_delegate):
                main_window = qFindMainWindow()
                # t = main_window.list_view.fontMetrics().elidedText(t, Qt.ElideMiddle, DISPLAY_WIDTH - 50)
                t = main_window.list_view.fontMetrics().elidedText(t, Qt.ElideMiddle, DISPLAY_WIDTH - 2 * qApp.style().pixelMetric(QStyle.PM_FocusFrameHMargin))
                # t = str(index.row())

            return t

        elif (role == Qt.UserRole):
            return file_info
        
        elif role == Qt.DecorationRole:
            file_name = file_info.filename
            is_dir = fileinfo_is_dir(file_info)

            if (index.column() == 1):
                # Use the small icons so they fit and get transparency, don't
                # use pixmaps, which are opaque. Don't bother using thumbnails
                # since they are too small
                if (is_dir):
                    if (file_name == ".."):
                        return self.image_cache[":directory_up_icon"]
                        
                    else:
                        if (file_info.size == -2):
                            # Size being calculated
                            return self.image_cache[":directory_sizing_icon"]

                        else:
                            return self.image_cache[":directory_icon"]
                else:
                    if (fileinfo_is_hidden(file_info)):
                        return self.image_cache[":file_hidden_icon"]

                    elif (not fileinfo_is_writable(file_info)):
                        return self.image_cache[":file_system_icon"]
                    else:

                        return self.image_cache[":file_icon"]

            if (is_dir):
                if (file_name == ".."):
                    pixmap = self.image_cache[":directory_up"]
                else:
                    pixmap = self.image_cache[":directory"]

            elif (not file_name.lower().endswith(IMAGE_EXTENSIONS)):
                pixmap = self.image_cache[":file"]

            else:
                # pixmap = self.image_cache[":requesting"]
                pixmap = self.image_cache.get(file_name, None)

            # Only load the image if it is not cached
            if (pixmap is None):
                if (True) and False:
                    pixmap = QPixmap(os.path.join(self.file_dir, file_name))
                    if (pixmap.isNull()):
                        pixmap = self.image_cache[":error"]
                        
                    else:
                        pixmap = pixmap.scaled(IMAGE_WIDTH, IMAGE_HEIGHT, Qt.IgnoreAspectRatio, Qt.SmoothTransformation)
                        
                    self.cacheImage(file_name, pixmap)
                else:
                    
                    if (file_name not in self.request_set):
                        pixmap = self.image_cache[":requesting"]
                        logger.debug("requesting index %d %r ", index.row(), file_name)
                        self.request_set.add(file_name)
                        self.request_queue.put((index.row(), os.path.join(self.file_dir, file_name)))
                    
                    else:
                        #pixmap = self.image_cache[":requested"]
                        pixmap = self.image_cache[":requesting"]
                        logger.info("ignoring already requested index %d %r", index.row(), file_name)
                
            if (index.column() == 0):
                if (DISPLAY_HEIGHT != pixmap.height()) and False:
                    pixmap = qResizePixmap(pixmap, DISPLAY_WIDTH, DISPLAY_HEIGHT)
            else:
                # XXX Thumbnails are not that useful in this mode, just show
                #     directory vs. file (maybe app icon) and don't preload
                #     thumbnails?
                pixmap = qResizePixmap(pixmap, 32, 32)

            return pixmap
        return None

    def flags(self, index):
        return Qt.ItemIsSelectable | Qt.ItemIsEnabled | Qt.ItemIsEditable

    def rowCount(self, parent=None):
        # Return the number of rows we have currently available for display
        # Network drive sneed fetchmore or take forever to show a responsive UI
        return self.loaded_rows
        
    def columnCount(self, parent=QModelIndex()):
        logger.debug("")
        # Fullname, Name, ext, size, date, attr
        return 6
    
    def canFetchMore(self, index):
        """ Return True if there are more rows to load """
        logger.info("loaded_rows %d file_infos %d dir_infos_set %d page_size %d", self.loaded_rows, len(self.file_infos), len(self.dir_infos_set), self.page_size)
        return (self.rowCount() < len(self.file_infos))

    def fetchMore(self, index):
        """ Load more rows when the user scrolls to the end """
        logger.info("loaded_rows before %d total %d", self.loaded_rows, len(self.file_infos))
        if (self.canFetchMore(QModelIndex())):
            if (use_incremental_row_loading):
                # XXX There's a Qt bug for which if the number of loaded rows is not
                #     a multiple of the items per row, scrolling down via cursor
                #     gets "stuck" in all the items but for the two leftmost items.
                #     To workaround that, always make loaded_rows a multiple of the
                #     items per row, so Qt always find an available item below the
                #     rightmost items.
            
                # Always load the directories
            
                next_loaded_rows = min(max(self.loaded_rows, len(self.dir_infos_set)) + self.page_size - (self.loaded_rows % self.page_size), len(self.file_infos))
            else:
                next_loaded_rows = len(self.file_infos)

            self.beginInsertRows(index, self.loaded_rows, next_loaded_rows - 1)
            self.loaded_rows = next_loaded_rows
            self.endInsertRows()
            logger.info("loaded_rows after %d", self.loaded_rows)
        
class FixedWidthStyle(QCommonStyle):
    def __init__(self):
        super(FixedWidthStyle, self).__init__()
        self.size = None

    def setWidth(self, width):
        logger.info("%d", width)
        self.size = QSize(width, width)

    def sizeFromContents(self, ct, opt, sz, widget):
        logger.info("%r %r %r %r", ct, opt, sz, widget)
        return super(FixedWidthStyle, self).sizeFromContents(ct, opt, sz, widget)

    def viewItemSize(self, option, role):
        """
        Not called by listview in icon mode rendering
        """
        logger.info("%r 0x%x", option, role)
        return super(FixedWidthStyle, self).viewItemSize(option, role)

    def subElementRect(self, element, option, widget=None):
        """
        Called by listview in icon mode rendering
        """
        logger.info("")
        
        rect = super(FixedWidthStyle, self).subElementRect(element, option, widget)

        if (element == QStyle.SE_ItemViewItemDecoration):
            logger.info("Rect %r icon %r", rect, option.icon)
            
            target_width, target_height = self.size.width(), self.size.height()
            width_diff = target_width - rect.width()
            height_diff = target_height - rect.height()

            # Calculate the amount to grow the rectangle in both directions equally
            growth = min(width_diff, height_diff)

            # Adjust the rect using the growth value, expanding equally
            rect.adjust(-growth // 2, -growth // 2, growth // 2, growth // 2)
            
            option.icon = QIcon(qResizePixmap(option.icon.pixmap(target_width, target_height), target_width, target_height))
            # option.icon = QIcon(option.icon.pixmap(target_width, target_height))

        return rect

    def itemPixmapRect(self, rect, flags, pixmap):
        """
        Not called by listview in icon mode rendering
        """
        logger.info("pixmap size %dx%d", pixmap.width(), pixmap.height())
        # Set a fixed width for the pixmap (for example, 64 pixels wide)
        fixed_width = 64
        # Maintain aspect ratio of the pixmap for the height
        aspect_ratio = pixmap.height() / pixmap.width()
        height = int(fixed_width * aspect_ratio)

        # Create a rectangle with fixed width and computed height
        rect = rect
        rect.setWidth(fixed_width)
        rect.setHeight(height)

        # Center the pixmap within the item rect
        rect.moveCenter(option.rect.center())

        return rect

    def drawItemPixmap(self, painter, rectangle, aligment, pixmap):
        """
        Not called by listview in icon mode
        """
        logger.info("")

class ScaledIconDelegate(QStyledItemDelegate):
    """
    Delegate that scales the pixmap returned by DecorationRole to the requested
    width x width
    """
    def __init__(self, *args, **kwargs):
        super(ScaledIconDelegate, self).__init__(*args, **kwargs)
        # Requested width
        self.width = None
        # Cached size
        self.size = None
        
    def paint(self, painter, option, index):
        # See https://github.com/qt/qtbase/blob/5.3/src/widgets/itemviews/qstyleditemdelegate.cpp#L440
        assert None is logger.debug("%r size %r decorationSize %r", option, self.size, option.decorationSize)
        #if (self.size is not None):
        #    option.decorationSize = self.size

        # QStyleOptionViewItem opt = option;    
        opt = QStyleOptionViewItem(option)
        # initStyleOption(&opt, index);
        self.initStyleOption(opt, index)

        # Override the calculated option icon and decorationSize with the scaled
        # one
        pixmap = index.data(Qt.DecorationRole)
        opt.icon = QIcon(qResizePixmap(pixmap, self.size.width(), self.size.height()))
        opt.decorationSize = QSize(self.width, self.width)
        
        #const QWidget *widget = QStyledItemDelegatePrivate::widget(option);
        #QStyle *style = widget ? widget->style() : QApplication::style();
        widget = option.widget
        style = qApp.style() if widget is None else widget.style()
        #style->drawControl(QStyle::CE_ItemViewItem, &opt, painter, widget);
        style.drawControl(QStyle.CE_ItemViewItem, opt, painter, widget)

    def setWidth(self, width):
        """
        Sets the width for the icon and schedules a relayout since the
        column/row sizes have changed
        """
        logger.info("%d", width)
        # Set the new requested width
        self.width = width
        # Invalidate the cached size
        self.size = None

        # Schedule a relayout on this view. model.layoutChanged.emit() is known
        # to work too, but that is model-wide and scheduleDelayedItemsLayout is
        # what the view does in response to that signal, see 
        # https://github.com/qt/qtbase/blob/5.3/src/widgets/itemviews/qabstractitemview.cpp#L3498
        self.parent().scheduleDelayedItemsLayout()
        
    def sizeHint(self, option, index):
        # See https://github.com/qt/qtbase/blob/5.3/src/widgets/itemviews/qstyleditemdelegate.cpp#L463
        logger.debug("decorationSize %r", option.decorationSize)
        # This is a very hot path, needs to cache or precalculate, otherwise
        # the inherited sizeHint takes seconds in the profiler
        if (self.size is None):
            # Width has changed, recalculate size
            # This assumes the size is fixed no matter index and options, which
            # is by design of this delegate
        
            #QStyleOptionViewItem opt = option;
            opt = QStyleOptionViewItem(option)
            #initStyleOption(&opt, index);
            self.initStyleOption(opt, index)
            #const QWidget *widget = QStyledItemDelegatePrivate::widget(option);
            widget = option.widget
            #QStyle *style = widget ? widget->style() : QApplication::style();
            style = qApp.style() if widget is None else widget.style()

            # Override the decorationSize with the requested size
            opt.decorationSize = QSize(self.width, self.width)

            #return style->sizeFromContents(QStyle::CT_ItemViewItem, &opt, QSize(), widget);
            size = style.sizeFromContents(QStyle.CT_ItemViewItem, opt, QSize(), widget)

            logger.info("self.width %r decorationSize %r sizeFromContents %r", self.width, opt.decorationSize, size)

            self.size = size
            
        return self.size


class CurrentRowHighlightDelegate(QStyledItemDelegate):
    """
    Qt supports QTableView full row selecting but not full row focusing. In
    order to do full row focusing two things are needed:
    1. Invalidate the cells that are in the current row
    2. Highlight all the cells in the focused row

    Ideally 2. would be done efficiently via palette or stylesheets, but there's
    no way to set a style or palette entry that affects the siblings of the
    focused cell.

    The only way of doing 2. is by a delegate that checks if the given index is
    in the focused row and sets the palette or brush appropriately.
    Unfortunately that can be innefficient when done from Python, specifically
    initOptions and drawControl appear as big hotspots in the profiler.

    As an added bonus, this also 
    - sets the selected row text, which could also be done by stylesheet via 
        FileTableView::item:focus { 
            background-color: #cceeff;
        }
        FileTableView::item:focus:selected { 
            background-color: #cceeff;
        }
        FileTableView::item:selected { 
            color: red;
            background-color: white;
        }
        See https://doc.qt.io/qt-6/stylesheet-reference.html
    - removes the per cell focus rectangle

    XXX Check when eg initOptions can be cached
    """
    def __init__(self, selection_model, *args, **kwargs):
        super(CurrentRowHighlightDelegate, self).__init__(*args, **kwargs)
        
        def currentChanged(current, previous):
            logger.info("")
            
            # Force redraw of the table
            self.parent().scheduleDelayedItemsLayout()

        # Qt by default only highlights the current cell, in order to extend the
        # highlight to the whole row, it's necessary to invalidate all the cells
        # in the new current row and in the old current row whenever the current
        # row changes. 
        #
        # This is done by hooking on the selectionModel's currentChanged, and
        # then doing scheduleDelayedItemsLayout. This is overkill in that the
        # whole view is invalidated instead of just the intervening rows, but
        # there's no way of invalidating only those rows of the view
        #
        # Other options like invalidating the cells (eg emit dataChanged) work
        # at model level, instead of at view level, which means that all the
        # views connected to that model would get unnecessarily invalidated.

        # Note this also triggers when the view loses/gains focus, which is
        # necessary to remove the highlight at that time
        selection_model.currentChanged.connect(currentChanged)
        
    def paint(self, painter, option, index):
        # See https://github.com/qt/qtbase/blob/5.3/src/widgets/itemviews/qstyleditemdelegate.cpp#L440
        
        view = option.widget
        if (
            ((index.row() != view.currentIndex().row()) and 
            # Would like to use the fast path for selected items too, but
            # setting a selected item style (focused or not) in the stylesheet
            # causes the backgroundbrush and palette brush below to be
            # overridden, investigate?
            ((option.state & QStyle.State_Selected) == 0)) or 
            # XXX This could skip the non focused view but needs to set a style
            #     or palette is set to paint selected red on white
            #(not view.hasFocus())
            False
            ):
            # This is a hotpath, use the fast native path whenever possible
            super(CurrentRowHighlightDelegate, self).paint(painter, option, index)
            return
        
        assert None is logger.debug("")
        # QStyleOptionViewItem opt = option;    
        opt = QStyleOptionViewItem(option)
        # initStyleOption(&opt, index);
        self.initStyleOption(opt, index)

        # Override the calculated option background brush, remove focus rectangle
        
        # Note there's no need to check if the widget is focused for the
        # selected color since the selected color doesn't change when focus is
        # lost
        if (index.row() == view.currentIndex().row()) and (view.hasFocus()):
            # drawControl QStyle.CE_ItenViewITem sometimes uses backgroundBrush
            # and sometimes the palette brush, set both
            # XXX This could use Q_PROPERTY defined in the stylesheet?
            opt.backgroundBrush = QBrush(QColor("#cceeff"))
            opt.palette.setBrush(QPalette.Highlight, QColor("#cceeff"))
            # Remove State_HasFocus so the focus rectangle is not drawn
            opt.state = opt.state & ~QStyle.State_HasFocus

        else:
            opt.palette.setBrush(QPalette.Highlight, Qt.white)

        opt.palette.setColor(QPalette.HighlightedText, Qt.red)
        
        #const QWidget *widget = QStyledItemDelegatePrivate::widget(option);
        #QStyle *style = widget ? widget->style() : QApplication::style();
        widget = option.widget
        style = qApp.style() if widget is None else widget.style()
        #style->drawControl(QStyle::CE_ItemViewItem, &opt, painter, widget);
        style.drawControl(QStyle.CE_ItemViewItem, opt, painter, widget)

class FileTableView(QTableView):
    def __init__(self, parent=None):
        super(FileTableView, self).__init__(parent)
        
    def focusInEvent(self, event):
        logger.info("")
        super(FileTableView, self).focusInEvent(event)
        # XXX Uncomment to also enable tableheader accent on focus, note this is
        #     not useful in icon view since there are no headers in that view
        # self.horizontalHeader().setStyleSheet("QHeaderView::section { background-color: #cceeff; }")
        
    def focusOutEvent(self, event):
        logger.info("")
        super(FileTableView, self).focusOutEvent(event)
        # XXX Uncomment to also enable tableheader accent on focus, note this is
        #     not useful in icon view since there are no headers in that view
        # self.horizontalHeader().setStyleSheet("")
        
    def keyPressEvent(self, event):
        logger.info("%r", event)
        if (event.key() in [Qt.Key_Left, Qt.Key_Right]):
            event.ignore()

        else:
            super(QTableView, self).keyPressEvent(event)

    def mousePressEvent(self, event):
        logger.info("%r", event)

        # Prevent selecting on left button, select on right button
        if (event.button() == Qt.LeftButton):
            # Don't select, but still want to set the element current
            index = self.indexAt(event.pos())
            if (index.isValid()):
                index = index.sibling(index.row(), 1)
                # XXX This is replicated in FilePane, refactor
                self.selectionModel().setCurrentIndex(index, QItemSelectionModel.NoUpdate | QItemSelectionModel.Rows)

            event.ignore()
                
        elif (event.button() == Qt.RightButton):
            # XXX This is not perfect, it doesn't do multiple select toggle on
            #     dragging like the default left click does
            # Select on right click
            index = self.indexAt(event.pos())
            if (index.isValid()):
                self.selectRow(index.row())
            event.accept()

        else:
            super(FileTableView, self).mousePressEvent(event)

class FilePane(QWidget):
    def __init__(self, *args, **kwargs):
        logger.info("")
        super(FilePane, self).__init__(*args, **kwargs)

        self.dir_history = []
        self.current_dir_history = -1

        self.search_string = ""
        self.search_string_display_ms = 2000
        self.search_string_timer = QTimer()
        self.search_string_timer.setSingleShot(True)
        self.search_string_timer.timeout.connect(self.resetSearchString)

        self.DISPLAY_WIDTH = DISPLAY_WIDTH

        self.setupActions()

        self.file_dir = None

        # XXX Set a sorting model so manual sorting is not necessary, with the
        #     default being directories first, files last, both alphabetically.
        #     Check that it doesn't break incremental loading
        model = DirectoryModel()
        
        # Create views
        self.list_view = QListView()
        self.table_view = FileTableView()
        # XXX These are created beforehand because setModels calls setupModels,
        #     which need to update these, think about the right way of structuring
        #     this
        self.disk_info_label = QLabel("C:\ 0000 k of 00000 k free")
        self.summary_label = QLabel("0k / 0k in 0 / 0 files, 0 / 0 dirs")
        self.header_label = QLabel(self.file_dir)

        self.setModels(model)

        # Cofigure the listview
        self.list_view.setViewMode(QListView.IconMode)
        self.list_view_style = FixedWidthStyle()
        #self.list_view.setStyle(self.list_view_style)
        #self.list_view.setGridSize(QSize(DISPLAY_WIDTH, DISPLAY_HEIGHT+20))
        # setUniformItemSizes is important so past items are note data() which
        # kills the LRU cache. ListViewPrivate::itemSize uses it to prevent
        # calling the delegate. Unforunately this requires doing elision in the 
        # Using a delegate avoids having to do elision in the model's data() 
        if (use_delegate):
            delegate = ScaledIconDelegate(self.list_view)
            delegate.setWidth(self.DISPLAY_WIDTH)
            self.list_view_style.setWidth(self.DISPLAY_WIDTH)
            self.list_view.setItemDelegate(delegate)
            self.list_view.setSpacing(10)
            self.list_view.setTextElideMode(Qt.ElideMiddle)
        else:
            # UniformItemSizes requires text to be either wrapped or elided, so
            # the size remains constant no matter the text length, but wrapping
            # doesn't work since adds height when wrapping into several lines
            # and elision doesn't always work because it doesn't look at the
            # icon size to set the width. The only solution other than using an
            # Item delegate is to do elision in data(), but that requires
            # accessing the view's font, which breaks encapsulation (and there
            # could be multiple views connected to a model)
            # self.list_view.setIconSize(QSize(DISPLAY_WIDTH, DISPLAY_HEIGHT))
            self.list_view.setUniformItemSizes(True)
        # self.list_view.setWordWrap(False)

        # No need to disable setTabKeyNavigation since the listview doesn't
        # consume tab key by default

        # Don't focus just on mouse wheel
        self.list_view.setFocusPolicy(Qt.StrongFocus)

        self.list_view.setEditTriggers(QAbstractItemView.NoEditTriggers)
        
        # Note the selection mode is independent of the selection mode*l*, need
        # to configure even if the listview and the tableview share the
        # selection mode*l*
        self.list_view.setSelectionMode(QAbstractItemView.MultiSelection)
        # Also needs to set the row so when an index is selected on the listview,
        # it's also reflected in all the columns in the tableview 
        self.list_view.setSelectionBehavior(QAbstractItemView.SelectRows)
        
        # These allow tuning the behavior, not clear it's useful
        #self.list_view.setFlow(QListView.LeftToRight)
        #self.list_view.setWrapping(True)
        # This causes relayout on resize, the other option is to
        # self.model.layoutChanged.emit() from the app's resizeEvent
        self.list_view.setResizeMode(QListView.Adjust)
        self.list_view.activated.connect(self.itemActivated)

        # Don't bold headers when there are rows selected
        self.table_view.horizontalHeader().setHighlightSections(False)
        # Make the Name column take all remaining horizontal space, the others
        # to be as small as possible
        # XXX This needs to be done on very load because the current contents of
        #     the table are the headers, which are too small for some fields
        self.table_view.horizontalHeader().setSectionResizeMode(1, QHeaderView.Stretch)
        for i in xrange(4):
            self.table_view.horizontalHeader().setSectionResizeMode(i + 2, QHeaderView.ResizeToContents)
        # Don't display row numbers
        self.table_view.verticalHeader().setVisible(False)
        # Shrink the row height to roughly font height
        self.table_view.verticalHeader().setDefaultSectionSize(self.table_view.fontMetrics().height() + 6)
        # Don't display the big thumbnail column
        self.table_view.hideColumn(0)
        self.table_view.setIconSize(QSize(16, 16))
        self.table_view.setShowGrid(False)
        self.table_view.activated.connect(self.itemActivated)
        
        # Disable tab navigation so it can be trapped by the app to switch
        # panes, another option is to use Qt.ApplicationShortcut in the app
        # shortcut. 
        self.table_view.setTabKeyNavigation(False)
        # Don't focus just on mouse wheel
        self.table_view.setFocusPolicy(Qt.StrongFocus)
        
        # XXX Decide how to handle item editing (file renaming), right now it's
        #     done via a FilePane-level dialog box and reloadDirectory. The
        #     default Qt in place cell edit behavior is to modify the model,
        #     which then needs a hook to modify the filesystem but needs to end
        #     at the view level to check for existing filename or rename
        #     failures.
        #
        #     In addition, there's also file moving to the other panel, which 
        #     should also allow a rename edit box to double as single file 
        #     renaming
        # self.table_view.setEditTriggers(QAbstractItemView.EditKeyPressed)
        self.table_view.setEditTriggers(QAbstractItemView.NoEditTriggers)

        # The best configuration for the default table to behave like a typical
        # file panel is 
        # - MultiSelection (so multiple files can be selected) and 
        # - Select rows so the full row is selected instead of individual cells.
        
        # XXX This still has issues:
        #     - Multiselection causes that calls to setCurrentIndex focus *and*
        #       select the row, this is prevented by calling setCurrentIndex
        #       on the selection model instead of in the main model, see 
        #       setCurrentIndex docs
        #     - Multiselection causes search by typing letters to toggle the
        #       selection of the item found on every leter pressed. Not fixed yet
        #     - Multiselection causes clicking with the left mouse button to
        #       focus *and* select. This is fixed by mousePressEvent special 
        #       handling left clicks
        #     - The movement is still at cell level, left and right are still
        #       enabled and the focus rectangle drawn on the individual cell.
        #       This is fixed by eventFiltering left/right movement.
        #     - The focus rectangle is still on a single cell, not on the full
        #       row. This is fixed by using a delegate that removes the focus
        #       flag, which removes the focus rect altogether and triggering view
        #       updates on currentIndex changes
        self.table_view.setSelectionMode(QAbstractItemView.MultiSelection)
        self.table_view.setSelectionBehavior(QAbstractItemView.SelectRows)
        
        def headerChooser(pos):
            logger.info("Header chooser for %s", pos)
            table = self.table_view
            model = table.model()
            
            menu = QMenu()
            for col in xrange(model.columnCount()):
                header = model.headerData(col, Qt.Horizontal)
                action = menu.addAction(header)
                action.setData(col)
                action.setCheckable(True)
                action.setChecked(not table.isColumnHidden(col))
            
            action = menu.exec_(table.viewport().mapToGlobal(pos))
            if (action is not None):
                col = action.data()
                if (table.isColumnHidden(col)):
                    table.showColumn(col)
                else:
                    table.hideColumn(col)
                table.resizeColumnsToContents()
                    
        # Note the column order and visibility already get automatically
        # restored with the headerview save and restoreState and saveState
        # functions
        headers = self.table_view.horizontalHeader()
        headers.setSectionsMovable(True)
        headers.setContextMenuPolicy(Qt.CustomContextMenu)
        headers.customContextMenuRequested.connect(headerChooser)      


        layout = QVBoxLayout()
        # layout.addWidget(QTextEdit())

        # Layout to hold the views
        self.view_layout = QVBoxLayout()
        self.view_layout.addWidget(self.list_view)
        
        # XXX If the table_view is initially shown and the list_view is
        #     initially hidden, the icons are cropped vertically, investigate.
        #     Gets fixed by ctrl +/-
        #     Doesn't always happen?

        self.list_view.setVisible(False)
        #self.table_view.setVisible(False)
        self.view_layout.addWidget(self.table_view)

        #self.header_label = QPushButton(self.file_dir)
        #self.header_label.setStyleSheet("text-align: left")
        self.disk_info_label.setAlignment(Qt.AlignVCenter | Qt.AlignLeft)
        layout.addWidget(self.disk_info_label)

        self.header_label.setFrameStyle(QFrame.Panel | QFrame.Sunken)
        self.header_label.setAlignment(Qt.AlignVCenter | Qt.AlignLeft)

        layout.addWidget(self.header_label)
        layout.setSpacing(0)
        layout.addLayout(self.view_layout)
        
        layout.addWidget(self.summary_label)

        # Install eventfilters on children views to trap focusin/out and change
        # header button color
        self.header_label.installEventFilter(self)
        self.list_view.installEventFilter(self)
        self.table_view.installEventFilter(self)

        # Label font is too small, increase
        font = QFont(self.disk_info_label.font().family(), self.disk_info_label.font().pointSize()+2)
        self.disk_info_label.setFont(font)
        self.header_label.setFont(font)
        self.summary_label.setFont(font)

        self.setLayout(layout)

        logger.info("ListView font %s pointSize %d height %d", self.list_view.font().family(), 
            self.list_view.font().pointSize(), self.list_view.fontMetrics().height())

    def setupModels(self):
        logger.info("")

        # XXX Doing this seems to undo something done at views' setModel time,
        #     but probably needs to be done, do it elsewhere before?

        #self.model.disconnect()
        #self.selection_model.disconnect()

        # Call setspan on rowsinserted/deleted to make directory sizes span
        # extension and size columns
        # Rate-limit since it ignores the parameters for simplicity
        self.model.rowsInserted.connect(self.rateLimitedMergeDirSizeExt)
        self.model.rowsMoved.connect(self.rateLimitedMergeDirSizeExt)
        self.model.rowsRemoved.connect(self.rateLimitedMergeDirSizeExt)
        self.model.modelReset.connect(self.rateLimitedMergeDirSizeExt)

        # Updating the summary is expensive and can be called frequently when
        # inserting/removing rows or calculating directory sizes, rate-limit the
        # update
        self.selection_model.selectionChanged.connect(self.rateLimitedUpdateSummary)
        self.model.rowsInserted.connect(self.rateLimitedUpdateSummary)
        self.model.rowsRemoved.connect(self.rateLimitedUpdateSummary)
        self.model.dataChanged.connect(self.rateLimitedUpdateSummary)
        self.model.modelReset.connect(self.rateLimitedUpdateSummary)

        self.model.modelReset.connect(lambda : self.header_label.setText(self.model.file_dir))

        # Set an item delegate to do proper row-aware focus 
        self.table_view.setItemDelegate(CurrentRowHighlightDelegate(self.selection_model, self.table_view))

    def mergeDirSizeExt(self):
        model = self.table_view.model()
        self.table_view.clearSpans()
        for row in xrange(model.rowCount()):
            file_info = model.index(row, 0).data(Qt.UserRole)
            if (fileinfo_is_dir(file_info)):
                logger.info("Merging %d", row)
                self.table_view.setSpan(row, 2, 1, 2)
            else:
                # This assumes directories go first and there are no spans in
                # files
                break
                
    def rateLimitedMergeDirSizeExt(self):
        # Don't rate limit this call too much, otherwise the UI takes time to
        # enlarge the <DIR> columns and the UX is bad
        qRateLimitCall(self.mergeDirSizeExt, 10)

    def setModels(self, model, selection_model=None):
        """
        XXX The whole point of this function is so panel contents can be swapped
            without reloading the directory in swapPaneContents, but it has
            multiple corner cases: 
            - sharing with initialization to avoid duplication, but guaranteeing 
              that init has initialized enough and in the right order
            - calling signal handlers that don't get called because setModel 
              doesn't trigger them
            - and switching views can be
            done a lot simpler by loadDirectory, rethink?
        """
        logger.info("")
        
        self.model = model
        self.file_dir = self.model.file_dir
        
        self.list_view.setModel(self.model)
        
        enable_sorting = False
        if (enable_sorting):
            # XXX This works but silently crashes when switching views and back
            #     in setCurrentIndex. Probably needs to be careful when using
            #     model() vs. sourceModel(). 
            # XXX updatePageSize also crashes or returns negative values,
            #     probably related to createRootIndex, but making
            #     createRootIndex use the active view's model() crashes the app
            #     at startup
            # XXX It also needs to subclass and override lessThan or to set a
            #     sortRole that puts directories first and does case-insensitive
            # XXX Also, check behavior with background loading, should work but 
            #     will perturb UI surrounding the focused row?
            proxyModel = QSortFilterProxyModel(self)
            proxyModel.setSourceModel(self.model)
            proxyModel.sort(1, Qt.AscendingOrder)
            self.table_view.setModel(proxyModel)
            self.table_view.setSortingEnabled(True)
            self.table_view.sortByColumn(1, Qt.AscendingOrder)
            self.proxyModel = proxyModel
            # This shows the sorting indicator and allows sorting by clicking on
            # headers
            # XXX Although sorting seems to be disabled
            self.table_view.horizontalHeader().setSectionsClickable(True)

        else:
            self.table_view.setModel(self.model)

        if (selection_model is None):
            selection_model = self.table_view.selectionModel()

        # Share the selectionmodel between listview and tableview so selection
        # is preserved across view switching. Note this needs to be done after
        # the main models are set, since setting the main model resets the
        # selection model
        self.selection_model = selection_model
        self.table_view.setSelectionModel(self.selection_model)
        self.list_view.setSelectionModel(self.selection_model)

        # There's no signal being sent for the setModel above, need to reset the
        # size/ext column spans explicitly, summary and header label
        # XXX Trigger a resetModel signal instead?
        #self.mergeDirSizeExt()
        #self.updateSummary()
        #self.header_label.setText(self.file_dir)

        self.setupModels()

        # XXX Emitting a signal instead of calling the size/ext column spans,
        #     summary and header label redraw prevents having to create the
        #     widgets beforehand at __init__ time and replicating the calls the
        #     signal handlers make, but has a UI delay when updating that is bad
        #     UX?
        self.model.modelReset.emit()

    def updateSummary(self):
        logger.info("Starting")

        # Ignore until a model has been loaded after app startup
        if (self.file_dir is None):
            return

        locale = QLocale()

        # XXX There's no QStorageInfo until 5.4 and and no shutil.disk_usage in
        #     python 2.7
        if (False):
            info = QStorageInfo(self.file_dir)
            self.disk_info_label.setText("%s %s k of %s k free" % (
                info.displayName(),
                locale.toString(info.bytesAvailable() / 2**10), 
                locale.toString(info.bytesTotal() / 2**10))
            )
        else:
            total_bytes = 0
            free_bytes = 0
            drive = os.path.splitdrive(self.file_dir)[0]
            unc = os.path.splitunc(self.file_dir)[0]
            drive = unc if (drive == "") else (drive + "\\")
            try:
                import ctypes
                GetDiskFreeSpaceExW = ctypes.windll.kernel32.GetDiskFreeSpaceExW

                root_path = ctypes.c_wchar_p(drive)
                free_bytes_available = ctypes.c_ulonglong(0)
                total_number_of_bytes = ctypes.c_ulonglong(0)
                total_number_of_free_bytes = ctypes.c_ulonglong(0)

                # Call GetDiskFreeSpaceExW to get the disk space details
                result = GetDiskFreeSpaceExW(
                    root_path, 
                    ctypes.byref(free_bytes_available),
                    ctypes.byref(total_number_of_bytes),
                    ctypes.byref(total_number_of_free_bytes)
                )
                total_bytes = total_number_of_bytes.value
                free_bytes = free_bytes_available.value
            except Exception as e:
                logger.error("Error %s", e)
                                            
            self.disk_info_label.setText("%s %s k of %s k free" % (
                drive,
                locale.toString(free_bytes / 2**10),
                locale.toString(total_bytes / 2**10)
            ))

        selected_size = 0
        selected_files = 0
        selected_dirs = 0
        total_size = 0
        total_files = 0 
        total_dirs = 0 
        
        for row in xrange(self.model.rowCount()):
            index = self.model.index(row, 3)
            file_info = index.data(Qt.UserRole)
            size = file_info.size
            is_selected = self.getActiveView().selectionModel().isSelected(index)
            if (fileinfo_is_dir(file_info)):
                selected_dirs += 1 if is_selected else 0
                total_dirs += 1

            else:
                selected_files += 1 if is_selected else 0
                total_files += 1
            total_size += size
            selected_size += size if is_selected else 0
            
        self.summary_label.setText("%s k / %s k in %s / %s files, %s / %s dirs" % (
            locale.toString(selected_size / 2**10),
            locale.toString(total_size / 2**10),
            locale.toString(selected_files),
            locale.toString(total_files),
            locale.toString(selected_dirs),
            locale.toString(total_dirs)
        ))
        logger.info("Done")

    def rateLimitedUpdateSummary(self):
        qRateLimitCall(self.updateSummary, 500)

    def resetSearchString(self):
        QToolTip.hideText()
        self.search_string = ""
        self.search_string_timer.stop()

    def setSearchString(self, search_string):
        self.search_string = search_string
        if (self.search_string == ""):
            self.resetSearchString()
            
        else:
            # Setting a new search string, refresh the thumbnail timer, and the
            # string in case it changed. Use an "infinite" display time and
            # manual hiding timer since there's no way to restart the default
            # QToolTip timer without hiding and showing the QTooltip which does
            # bad UX flash
            QToolTip.showText(
                self.getActiveView().parentWidget().mapToGlobal(self.getActiveView().geometry().topLeft()), 
                self.search_string, 
                self, 
                QRect(),
                sys.maxint
            )
            self.search_string_timer.start(self.search_string_display_ms)

    def setupActions(self):
        # Override the default tableview copy action which only copies the
        # filename, with one that copies the full filepath
        self.copyFilepathsAct = QAction('Copy Filepaths', self, shortcut="ctrl+shift+c", triggered=self.copySelectedFilepaths, shortcutContext=Qt.WidgetWithChildrenShortcut)

        self.copyFilesAct = QAction('Copy to Clipboard', self, shortcut="ctrl+c", triggered=self.copySelectedFiles, shortcutContext=Qt.WidgetWithChildrenShortcut)
        self.cutFilesAct = QAction('Cut to Clipboard', self, shortcut="ctrl+x", triggered=self.cutSelectedFiles, shortcutContext=Qt.WidgetWithChildrenShortcut)
        # XXX Have an option to ove to trash, shift+del vs. del?
        self.deleteFilesAct = QAction('Delete', self, shortcut="del", triggered=self.deleteSelectedFiles, shortcutContext=Qt.WidgetWithChildrenShortcut)

        self.pasteFilesAct = QAction('Paste from Clipboard', self, shortcut="ctrl+v", triggered=self.pasteClipboardFiles, shortcutContext=Qt.WidgetWithChildrenShortcut)

        self.changeDirAct = QAction('Change Directory', self, shortcut="ctrl+d", triggered=self.changeDirectory, shortcutContext=Qt.WidgetWithChildrenShortcut)
        self.reloadDirAct = QAction('Reload Directory', self, shortcut="ctrl+r", triggered=self.reloadDirectory, shortcutContext=Qt.WidgetWithChildrenShortcut)
        self.parentDirAct = QAction('Parent Directory', self, triggered=self.gotoParentDirectory, shortcutContext=Qt.WidgetWithChildrenShortcut)
        self.parentDirAct.setShortcuts(["backspace", "ctrl+PgUp"])
        self.childDirAct = QAction('Child Directory', self, shortcut="ctrl+PgDown", triggered=self.gotoChildDirectory, shortcutContext=Qt.WidgetWithChildrenShortcut)
        # XXX Missing PgDown to enter current directory
        self.prevDirectoryAct = QAction('Previous Directory', self, shortcut="alt+left", triggered=lambda : self.gotoHistoryDirectory(-1), shortcutContext=Qt.WidgetWithChildrenShortcut)
        self.nextDirectoryAct = QAction('Next Directory', self, shortcut="alt+right", triggered=lambda : self.gotoHistoryDirectory(1), shortcutContext=Qt.WidgetWithChildrenShortcut)
        # XXX Don't do if the activewview is not the table, ie do select only on the listview?
        self.calculateSubdirSizesAct = QAction('Calculate Subdirectory Sizes', self, shortcut="space", triggered=lambda : self.calculateSubdirSizes(self.getActiveView().currentIndex()), shortcutContext=Qt.WidgetWithChildrenShortcut)
        self.calculateAllSubdirsSizesAct = QAction('Calculate All Subdirectory Sizes', self, shortcut="alt+shift+return", triggered=lambda : self.calculateSubdirSizes(), shortcutContext=Qt.WidgetWithChildrenShortcut)

        self.createDirAct = QAction('Create Directory', self, shortcut="F7", triggered=self.createDirectory, shortcutContext=Qt.WidgetWithChildrenShortcut)
        self.createDirAct.setShortcuts(["ctrl+n", "F7"])

        # XXX Make this work with F6, right now F6 is at the app level to move
        #     to the next pane directory, but F6 should work for both and this
        #     should be shift+F6 in place editing?
        self.renameFileAct = QAction('Rename File', self, shortcut="F2", triggered=self.renameFile, shortcutContext=Qt.WidgetWithChildrenShortcut)

        self.increaseIconSizeAct = QAction('Increase Icon Size', self, shortcut="ctrl++", triggered=lambda : self.resizeIcons(16), shortcutContext=Qt.WidgetWithChildrenShortcut)
        self.decreaseIconSizeAct = QAction('Decrease Icon Size', self, shortcut="ctrl+-", triggered=lambda : self.resizeIcons(-16), shortcutContext=Qt.WidgetWithChildrenShortcut)
        
        self.switchViewAct = QAction("Switch View", self, shortcut="ctrl+t", triggered=self.switchView, shortcutContext=Qt.WidgetWithChildrenShortcut)

        self.selectAndAdvanceAct = QAction("Select and Advance", self, shortcut="insert", triggered=self.selectAndAdvance, shortcutContext=Qt.WidgetWithChildrenShortcut)
        self.invertSelectionAct = QAction("Invert Selection", self, shortcut="ctrl+b", triggered=self.invertSelection, shortcutContext=Qt.WidgetWithChildrenShortcut)
        self.selectAllOrClearAct = QAction("Select all/None", self, shortcut="ctrl+a", triggered=self.selectAllOrClear, shortcutContext=Qt.WidgetWithChildrenShortcut)

        self.openInExternalViewerAct = QAction("Open in External Viewer", self, shortcut="F3", triggered=self.openInExternalViewer, shortcutContext=Qt.WidgetWithChildrenShortcut)

        # XXX LineEdit with directory name, bookmarks/favorites/history combobox
        # XXX Allow filtering files by typing name
        # XXX Allow searching files by typing name
        
        self.addAction(self.copyFilepathsAct)
        self.addAction(self.copyFilesAct)
        self.addAction(self.cutFilesAct)
        self.addAction(self.deleteFilesAct)
        self.addAction(self.pasteFilesAct)
        self.addAction(self.changeDirAct)
        self.addAction(self.reloadDirAct)
        self.addAction(self.parentDirAct)
        self.addAction(self.childDirAct)
        self.addAction(self.prevDirectoryAct)
        self.addAction(self.nextDirectoryAct)
        self.addAction(self.calculateSubdirSizesAct)
        self.addAction(self.calculateAllSubdirsSizesAct)
        self.addAction(self.createDirAct)
        self.addAction(self.renameFileAct)
        self.addAction(self.increaseIconSizeAct)
        self.addAction(self.decreaseIconSizeAct)
        self.addAction(self.switchViewAct)
        self.addAction(self.selectAndAdvanceAct)
        self.addAction(self.invertSelectionAct)
        self.addAction(self.selectAllOrClearAct)
        self.addAction(self.openInExternalViewerAct)

    def setCurrentIndex(self, index):
        logger.info("%d,%d", index.row(), index.column())
        # The normal setCurrentIndex both sets the focus AND selects, wich is
        # undesirable. As per QAbstractItemView::setCurrentIndex documentation,
        # set the current in the selection model, not in the model, so the item
        # is only focused, not selected
        self.getActiveView().selectionModel().setCurrentIndex(index, QItemSelectionModel.NoUpdate)

    def scrollTo(self, index):
        logger.info("%d, %d", index.row(), index.column())
        self.getActiveView().scrollTo(index)

    def selectAllOrClear(self):
        logger.info("")
        # Clear the selection if more than half are selected, otherwise select
        # all (use more than half as a heuristic)
        # XXX How does this interact with incremental loading? What if not all
        #     the rows are loaded?
        if (len(self.getActiveView().selectionModel().selectedRows()) >= (self.model.rowCount() / 2)):
            self.getActiveView().clearSelection()
        else:
            self.getActiveView().selectAll()
        
    def invertSelection(self):
        logger.info("")

        model = self.model
        selection_model = self.getActiveView().selectionModel()

        # XXX How does this interact with incremental loading? What if not all
        #     the rows are loaded?
        
        # This can be slow with many files due to the individual signals, use a
        # selection instead of going index by index
        # Table model has full row selection, so only go through rows
        selection = QItemSelection(model.index(0,0), model.index(model.rowCount()-1, 0))
        selection_model.select(selection, QItemSelectionModel.Toggle | QItemSelectionModel.Rows)
    
    def selectAndAdvance(self):
        logger.info("")
        view = self.getActiveView()
        index = view.currentIndex()
        view.selectionModel().select(index, QItemSelectionModel.Toggle | QItemSelectionModel.Rows)
        # Note this advancing works on both listview and tableview, since
        # listviews only have rows
        index = self.createRootIndex(index.row() + 1)
        if (index.isValid()):
            self.setCurrentIndex(index)

    def openInExternalViewer(self):
        logger.info("")
        filename = self.getActiveView().currentIndex().data(Qt.UserRole).filename
        filepath = os.path.join(self.file_dir, filename)
        editor_filepath = R"C:\Program Files\totalcmd\TOTALCMD64.EXE"
        arguments = ["/S=L", filepath]
        QProcess().startDetached(editor_filepath, arguments)

    def resizeIcons(self, delta):
        logger.info("%d + %d", self.DISPLAY_WIDTH, delta)
        new_width = max(64, self.DISPLAY_WIDTH + delta)
        if (new_width != self.DISPLAY_WIDTH):
            if (use_delegate):
                self.DISPLAY_WIDTH, self.DISPLAY_HEIGHT = new_width, new_width
                self.list_view.itemDelegate().setWidth(self.DISPLAY_WIDTH)
                self.list_view_style.setWidth(self.DISPLAY_WIDTH)
                
            else:
                # XXX Make this app or even listview local (or use the iconSize
                #     straight), but data(Qt.DisplayRole) needs this too?
                global DISPLAY_WIDTH
                global DISPLAY_HEIGHT
                DISPLAY_WIDTH, DISPLAY_HEIGHT = new_width, new_width
                # XXX setIconSize is not necessary when setting QPixmaps instead
                #     of QIcons
                # XXX Looks like layoutChanged is already sent by setIconSize?
                # self.list_view.setIconSize(QSize(DISPLAY_WIDTH, DISPLAY_HEIGHT))
                
                self.model.layoutChanged.emit()
                
            # update the page size and call canFetchmore to update loaded_rows
            # and workaround Qt keyboard navigation flag
            self.updatePageSize()
            if (self.model.canFetchMore(QModelIndex())):
               self.model.fetchMore(QModelIndex())

    def createDirectory(self):
        logger.info("")
        default_name = ""
        index = self.getActiveView().currentIndex()
        if (index.isValid()):
            default_name = index.data(Qt.UserRole).filename
        text, ok = QInputDialog.getText(
            self, "Create Directory", "Directory name:", QLineEdit.Normal, 
            default_name
        )
        logger.info("%r", text)
        if ((not ok) or (text == "")):
            return

        try:
            os.mkdir(os.path.join(self.file_dir, text))
            
            # XXX Needs to offer to wait for the directory so the setCurrent
            #     below works
            self.reloadDirectory()

            index = self.model.index(self.model.findFileInfoRow(text), 0)
            self.setCurrentIndex(index)
            self.scrollTo(index)

        except Exception as e:
            QMessageBox.warning(
                self, "Create Directory", "Unable to create directory '%r', error '%r'" % (text, e),
                buttons=QMessageBox.Ok,
                # Set it explicitly. Despite what docs say, the default is Yes
                defaultButton=QMessageBox.Ok
            )

    def renameFile(self):
        logger.info("")
        default_name = ""
        # XXX Do something special with multiple selection?
        index = self.getActiveView().currentIndex()
        
        if (index.isValid()):
            default_name = index.data(Qt.UserRole).filename
            text, ok = QInputDialog.getText(
                self, "Rename File",  "File name:", QLineEdit.Normal, default_name
            )
            logger.info("%r", text)
            if ((not ok) or (text == "") or (text == default_name)):
                return

            # XXX Trap renaming to existing file and offer overwrite/keep
            #     both/cancel
            old_filepath = os.path.join(self.file_dir, default_name)
            new_filepath = os.path.join(self.file_dir, text)
            try:
                if (os.path.exists(new_filepath)):
                    # XXX Offer rename again?
                    res = qYesNoCancelMessageBox(self, "Rename File", "'%r' already exists, overwrite?" % text)
                    if (res != QMessageBox.Yes):
                        return
                    os_remove(new_filepath)

                os.rename(old_filepath, new_filepath)
                # XXX Needs to offer to wait for the directory so the setCurrent
                #     below works
                
                # XXX A better way is to change the model and emit datachanged
                #     for this index, but what about re-sorting that should
                #     happen
                self.reloadDirectory()
            
                index = self.model.index(self.model.findFileInfoRow(text), 0)
                self.setCurrentIndex(index)
                self.scrollTo(index)

            except Exception as e:
                QMessageBox.warning(
                    self, "Rename File", "Unable to rename file '%r' to '%r', error '%r'" % (default_name, text, e),
                    buttons=QMessageBox.Ok,
                    defaultButton=QMessageBox.Ok
                )

    def gotoHistoryDirectory(self, delta):
        logger.info("%d %s", self.current_dir_history, self.dir_history)
        next_dir_history = self.current_dir_history + delta
        if (0 <= next_dir_history < len(self.dir_history)):
            self.current_dir_history = next_dir_history
            self.setDirectory(self.dir_history[self.current_dir_history], False)

    def gotoChildDirectory(self):
        logger.info("")
        file_info = self.getActiveView().currentIndex().data(Qt.UserRole)
        if ((file_info is not None) and (fileinfo_is_dir(file_info))):
            logger.info("Navigating to child %r", file_info.filename)
            # Use normpath, translate .. into parent
            self.setDirectory(os.path.normpath(os.path.join(self.file_dir, file_info.filename)))

    def gotoParentDirectory(self):
        parent_path = os.path.dirname(self.file_dir)
        logger.info("%r", parent_path)
        if (parent_path != self.file_dir):
            self.setDirectory(parent_path)

    def createRootIndex(self, row=0):
        col = 0 if (self.getActiveView() is self.list_view) else 1
        
        if (self.model.hasIndex(row, col)):
            index = self.model.index(row, col)
        else:
            index = QModelIndex()

        return index

    def calculateSubdirSizes(self, index=QModelIndex()):
        logger.info("")
        # This is called in several cases:
        # - When pressing space on the list_view (index is a file or a dir),
        #   toggle
        # - When pressing space on a file, toggle (index is a file)
        # - When pressing space on a non-selected dir, calculate space for this
        #   dir (index is a non-selected dir)
        # - When pressing space on a selected dir, toggle (index a selected dir)
        # - When pressing alt+shift+enter, calculate space for all dirs (index
        #   is invalid)

        view = self.getActiveView()
        if ((view == self.table_view) and (not view.selectionModel().isSelected(index))):
            self.model.calculateSubdirSizes(index)

        # If the index points to a valid file/dir on any view, toggle
        if (index.isValid()):
            view.selectionModel().select(index, QItemSelectionModel.Toggle | QItemSelectionModel.Rows)

    def setDirectory(self, file_dir, add_to_history = True):
        logger.info("%r", file_dir)
        old_file_dir = self.file_dir

        self.file_dir = file_dir
        # XXX This should use a signal instead of hijacking the main window
        qFindMainWindow().updateWindowTitle()
        self.header_label.setText(self.file_dir)

        if (add_to_history):
            self.current_dir_history += 1
            # Clamp history/append entry as necessary
            self.dir_history = self.dir_history[:self.current_dir_history] + [file_dir]

        # Display a dialog box that can cancel the directory listing, use NoIcon
        # so it doesn't make a sound when showing the dialog box
        msg_box = QMessageBox(QMessageBox.NoIcon, "Reading Directory", "Reading directory %r" % self.file_dir, QMessageBox.Ok | QMessageBox.Cancel, self)
        msg_box.button(QMessageBox.Ok).setText("Background")
        msg_box.setDefaultButton(msg_box.button(QMessageBox.Ok))
        self.model.setDirectory(self.file_dir)
        
        # XXX This should elide the entry so the messagebox doesn't change sizes
        #     with each entry
        #self.model.directoryReader.direntryRead.connect(lambda d, f: msg_box.setText("Reading directory %r\nEntry: %s" % (self.file_dir, f[0])))
        self.model.directoryReader.finished.connect(lambda : msg_box.close())
        #self.model.directoryReader.finished.connect(lambda : self.table_view.resizeColumnsToContents())
        # Sleep a bit and then processEvents, this is a simple way of not
        # flashing the messagebox if listing the directory takes little time
        # XXX Find a better way
        time.sleep(0.10)
        if (self.model.directoryReader.isRunning()):
            # Docs say exec result is opaque, even if it seems to match .result()
            res = msg_box.exec_()
            logger.info("QMessageBox returned 0x%x result is 0x%x", res, msg_box.result())
            if (self.model.directoryReader.isRunning() and (msg_box.result() == QMessageBox.Cancel)):
                self.model.directoryReader.abort()
        else:
            # The connect above may not hit if already finished and because
            # msgbox didn't exec, the UI thread hasn't had a chance to process the
            # direntryRead signals in charge of filling the model in this
            # thread, do it now so the code below doesn't find the model empty
            logger.info("DirectoryReader finished early, processing signals")
            qApp.processEvents()

        # XXX This could be done at startup time instead on every load if the
        #     headers are larger than the content, but they are currently not
        # Data has changed, autoresize the necessary columns
        # XXX This should probably go through signals?
        self.table_view.horizontalHeader().setSectionResizeMode(1, QHeaderView.Stretch)
        for i in xrange(4):
            self.table_view.horizontalHeader().setSectionResizeMode(i + 2, QHeaderView.ResizeToContents)
        
        # QTimer.singleShot(0, lambda : self.table_view.resizeColumnsToContents())
            
        # XXX Note even setting 0,0 can fail when using async DirectoryReader
        #     because the list may be still empty at this point, so 0,0 is
        #     invalid, specifically it may not even have the ".." entry yet,
        #     which is filled in by DirectoryReader too
        
        # XXX Asynchronous incremental directory loading is nice in theory but
        #     it breaks in practice:
        #     - focusing on the incoming dir needs to wait for that item to be in the
        #       model
        #     - focusing on the first dir also needs to wait for all items to be
        #       loaded, because the first dir may be the last entry listed,
        #       which happens to be the first one after sorting
        #     - even when waiting for the item to be in the model, scrolling to 
        #       that item may be useless because new items can be added after 
        #       the scroll (either in front or behind the item, since they need 
        #       to be propertly sorted). Qt won't keep the view of that item
        #       constant when items are added/removed.
        #     What is useful:
        #     - Doing async loading, just not incremental
        #     - Keeping the UI responsive, displaing some directory loading
        #       animation or such
        #     - Being able to abort directory loading, either showing the
        #       previous directory or even displaying whatever entries were
        #       collected until then
        
        # Create an index to the proper column depending on the active view (if
        # using column 0 the table_view will appear to not have keyboard focus
        # until cursor right key is pressed, which makes sense because right
        # will move from the hidden 0 column to the visible 1 column)

        index = self.createRootIndex()
        # If going up to the parent directory, focus on the children just left
        # (guard against old_file_dir which will be none at app startup)
        if ((old_file_dir is not None) and (os.path.dirname(old_file_dir) == self.file_dir)):
            # Focus on the incoming dir, could fail if didn't sleep enough time
            # to list this directory, or if it didn't sleep enough to increase
            # loaded_rows 

            # XXX Focusing on the incoming dir cannot be done with async dir
            #     listing, schedule a task to do it after a second? Do sync dir
            #     unless it takes more than this many seconds? Ideally would like to
            #     do something like sync dir listing for a second and if not
            #     completed then switch to async? Pump messages for a few secs so
            #     the signal is received and then try?
            for _ in xrange(1):
                logger.info("Sleeping before processEvents")
                time.sleep(0.01)
                qApp.processEvents()
                logger.info("Woke up after processEvents")
                # .index will fail if there wasn't enough time to fetch the
                # given entry
                try:
                    
                    row = self.model.findFileInfoRow(os.path.basename(old_file_dir))
                    index = self.createRootIndex(row)
                    logger.info("Created index %r row %d vs. row %d", index.data(Qt.DisplayRole), index.row(), row)
                    # XXX This is failing to focus even if hasIndex is True, but
                    #     if sleep for longer then it works. In both cases the
                    #     reported number of iterations is 0. The index with
                    #     shorter sleep is lower and the list smaller, probably
                    #     because the list is partially loaded, but it's not
                    #     clear why it would fail since all is done in the same
                    #     thread so it cannot be that the list is loaded behind
                    #     calculating the index and setting it as current and
                    #     scrolling to below
                    logger.info("valid %s has %s row %d rowcount %d", index.isValid(), self.model.hasIndex(index.row(), index.column()), index.row(), self.model.rowCount())
                    if (self.model.hasIndex(index.row(), index.column())):
                        logger.info("Focusing on incoming dir after %d iterations", _)
                        break
                except ValueError:
                    # .index() failed, not yet in list or it's deeper in
                    # hierarchy
                    pass
            
        if (self.model.hasIndex(index.row(), index.column())):
            logger.info("Setting index %r", index.data(Qt.DisplayRole))
            self.setCurrentIndex(index)
            def scrollToIndex(index, old_file_dir):
                try:
                    logger.info("Old scrollto is %r row %d", index.data(Qt.DisplayRole), index.row())
                    row = self.model.findFileInfoRow(os.path.basename(old_file_dir))
                    index = self.createRootIndex(row)
                    logger.info("New scrollto is %r row %d", index.data(Qt.DisplayRole), index.row())
                    self.scrollTo(index)
            
                except ValueError:
                    logger.info("Can't scrollTo")
            if (old_file_dir is not None):
                QTimer.singleShot(0, lambda : scrollToIndex(index, old_file_dir))

    def itemActivated(self, index):
        if (self.search_string_timer.isActive()):
            logger.info("Resetting search_string")
            self.search_string_timer.stop()
            self.search_string_timer.timeout.emit()
            
        file_info = index.data(Qt.UserRole)
        filename = file_info.filename
        logger.info("%d %r", index.row(), file_info)
        if (fileinfo_is_dir(file_info)):
            dirpath = os.path.normpath(os.path.join(self.file_dir, filename))
            self.setDirectory(dirpath)

        else:
            # XXX Unicode chars fail
            qLaunchWithPreferredApp(os.path.join(self.file_dir, filename))

    def getActiveView(self):
        if (self.list_view.isVisible()):
            return self.list_view
        else:
            return self.table_view
    
    def switchView(self):
        """ Switch between ListView and TableView """
        # XXX Do selected items need transferring too?
        logger.info("")
        if (self.getActiveView() is self.list_view):
            index = self.list_view.currentIndex()
            index = self.table_view.model().index(index.row(), 1)
            
            self.list_view.setVisible(False)

            self.table_view.resizeColumnsToContents()
            self.table_view.setVisible(True)
            self.table_view.setFocus()

            self.setCurrentIndex(index)
            self.scrollTo(index)

        else:
            index = self.table_view.currentIndex()
            index = self.list_view.model().index(index.row(), 0)

            self.table_view.setVisible(False)

            self.list_view.setVisible(True)
            self.list_view.setFocus()

            self.setCurrentIndex(index)
            self.scrollTo(index)
        
        self.updatePageSize()

    def updatePageSize(self):
        """
        There's a Qt bug for which keyboard cursor down doesn't fetch new rows
        when the current item is "one of the rightmost" items. The cursor
        movement can be unblocked by moving down from "one of the leftmost"
        items. This seems to be because there are no fetched items directly
        underneath the "rightmost" items, depending on the value of loaded_rows.

        The workaround is twofold:
        - Calculate page_size to be a multiple of items per row
        - In fetchMore, always make loaded_rows be a multiple of page_size

        This needs to be applied whenever the items per row changes, ie window
        resizing and icon resizing

        XXX Centralize the bugfix here and call fetchMore to update? The
            important part is the value of loaded_rows, more than the value of
            page_size, so the bugfix just needs to clamp loaded_rows to a
            multiple of items_per_row whenever loaded_rows is updated?
        """
        logger.info("")

        # This can be called without elements yet, ignore
        if (self.model.rowCount() == 0):
            return

        # Update the page size to match a multiple of 
        # XXX set the page size to items_per_row * items_per_column for naming consistency?
        # XXX Does the scrollbar have this page size already?
        # XXX This calculation seems 100% accurate, but a more fail proof way
        #     would be to use indexAt() from 0 to the item that jumps to the next
        #     row?

        index = self.createRootIndex()
        if (self.getActiveView() is self.list_view):
            item_size = self.list_view.sizeHintForIndex(index)

            # The spacing is between elements and between the first element and
            # border and between the last element and border
            items_per_row = (self.list_view.viewport().width() - self.list_view.spacing() - self.list_view.horizontalOffset()) * 1.0 / (item_size.width() + self.list_view.spacing())
            logger.info("listview width %d viewport width %d item width %d items per row %3.3f spacing %d page step %s", 
                self.list_view.width(), self.list_view.viewport().width(), item_size.width(), items_per_row, self.list_view.spacing(), 
                self.list_view.verticalScrollBar().pageStep())
            
            page_size = int(items_per_row)

        else:
            # XXX Always load all rows in table mode? But they are in the model
            #     and needs to restore them when switching to list mode
            item_size = self.table_view.sizeHintForIndex(index)
            page_size = self.table_view.viewport().height() / item_size.height()
            logger.info("tableview height %d viewport height %d item height %d items per col %3.3f", 
                self.table_view.height(),
                self.table_view.viewport().height(),
                item_size.height(), page_size)
            page_size = int(page_size)
            
        # XXX Using sorting causes page_size to be negative, guard for now.
        #     Investigate
        # updatePageSize: tableview height 1311 viewport height 1279 item height -1 items per col -1279.000
        self.model.page_size = max(page_size, 2)

    def eventFilter(self, source, event):
        logger.info("%r %s", source, EnumString(QEvent, event.type()))
        # Note focusIn / focusOut is not sent to the FilePane when the
        # FileTableView is focused, trap it with eventFilter
        # XXX Probably due to focuspolicy? Is there a FilePane focus policy that
        #     would work?
        if (event.type() == QEvent.FocusOut):
            self.header_label.setStyleSheet("text-align: left;")

        elif (event.type() == QEvent.FocusIn):
            color = QColor()
            color.setNamedColor("#cceeff")
            color = color.darker(125)
            self.header_label.setStyleSheet("text-align: left; background-color: %s" % color.name()) 
            # XXX This should use a signal instead of hijacking the main window
            qFindMainWindow().updateWindowTitle()
        
        elif ((source is self.header_label) and (event.type() == QEvent.MouseButtonRelease)):
            self.changeDirectory()

        elif ((event.type() == QEvent.KeyPress) and (self.search_string != "") and 
              (event.key() in [Qt.Key_Backspace, Qt.Key_Up, Qt.Key_Down])):
            # Allow minimal editing of the search string, navigation of hits up
            # and down
            
            # XXX Navigating the matches with up and down is intuitive but far
            #     from the home row, another option is to use Enter/shift-Enter,
            #     but that may cause erroneous directory switches if pressed
            #     when the timer just expired

            # Edit the string
            search_string = self.search_string
            if (event.key() == Qt.Key_Backspace):
                # XXX Delete one word if ctrl is pressed
                if (event.modifiers() & Qt.ControlModifier):
                    i = rindex_of(search_string, " ")
                    if (i == -1):
                        search_string = ""
                    else:
                        search_string = search_string[:i]

                else:
                    search_string = search_string[:-1]

                # Removing chars doesn't change the match, so no need to
                # rematch

            elif (event.key() in [Qt.Key_Up, Qt.Key_Down]):
                # Navigate the matches,  go to the next occurrence or wrap around
                index = self.getActiveView().currentIndex()
                delta = -1 if (event.key() == Qt.Key_Up) else 1
                start_row = index.row() 
                
                rowCount = self.model.rowCount()
                row = start_row + delta
                while ( start_row - rowCount < row < start_row + rowCount):
                    # Set the current index to the matching cell
                    
                    index = self.createRootIndex(row % rowCount)
                    filename = index.data(Qt.UserRole).filename
                    
                    # Check if the cell contains the typed substring (case insensitive)
                    if (search_string in filename.lower()):
                        self.setCurrentIndex(index)
                        break
                    row += delta
                    
            self.setSearchString(search_string)

            return True

        elif ((event.type() == QEvent.ShortcutOverride) and 
              (event.key() in [Qt.Key_Space, Qt.Key_Backspace, Qt.Key_Up, Qt.Key_Down]) and 
              self.search_string_timer.isActive()):
            # Prevent a few shortcuts to be used when editing the search_string
            # and accept the override, this will re-send they key event to the
            # child, which will be uses below for the search_string
            event.accept()
            
        elif ((event.type() == QEvent.KeyPress) and 
              # event.text() returns empty for cursor, etc which triggers the
              # "in" clause, ignore
              ((event.text() != "") and (event.text() in (string.digits + string.letters + string.punctuation + " ")))
            ):
            # The default behavior performs prefix search and selects the item,
            # perform substring search, don't select, display search string
            # on tooltip, allow backspace editing and navigating matches
            logger.info("Key %d text %r", event.key(), event.text())
            key = event.text().lower()

            search_string = self.search_string + key

            # Now search for a cell containing the typed string as a substring
            for row in xrange(self.model.rowCount()):
                # Set the current index to the matching cell
                
                index = self.createRootIndex(row)
                filename = index.data(Qt.UserRole).filename
                
                # Check if the cell contains the typed substring (case insensitive)
                # XXX Go to the next if this is already current?
                # XXX Clear typed text on non alpha key (eg after pressing return)?
                if (search_string in filename.lower()):
                    self.setCurrentIndex(index)
                    self.setSearchString(search_string)
                    break
            
            # Stop further handling in the pane views
            return True

        elif ((event.type() == QEvent.KeyPress) and (event.key() == Qt.Key_Escape)):
            # XXX Should this be a shorcut here or in the table view?
            if ((source is self.table_view) and (self.model.directoryReader is not None) and self.model.directoryReader.isRunning()):
                logger.info("Aborting directory readers")
                # Stop signals from the old thread, they are probably form a
                # previous directory listing and they would to the current grid but
                # fail to load due to the changed path
                logger.info("Disconnecting signal from old DirectoryReader finished %s running %s", self.model.directoryReader.isFinished(), self.model.directoryReader.isRunning())
                self.model.directoryReader.direntryRead.disconnect()
                self.model.directoryReader.abort()

            logger.info("Aborting filering")
            self.search_string_timer.stop()
            QToolTip.hideText()
        
        return super(FilePane, self).eventFilter(source, event)
    
    def resizeEvent(self, event):
        super(FilePane, self).resizeEvent(event)
        # adjustlayout flag already takes care of triggering layoutchanged on
        # resize, but need to update the page size to workaround Qt keyboard
        # navigation flag
        self.updatePageSize()

        # XXX There's no adjustLayout on TableView, need to call fetchMore if
        #     loaded_rows don't fill the screen, otherwise keyboard navigation
        #     doesn't fetch more rows (but mouse wheel does)
        if (self.getActiveView() is self.table_view):
            self.model.layoutChanged.emit()
            # XXX This shouldn't be necessary, the layoutChanged above should be
            #     enough?
            if (self.model.canFetchMore(QModelIndex())):
               self.model.fetchMore(QModelIndex())
        
    def changeDirectory(self):
        logger.info("Requesting new directory default is %r", self.file_dir)
        file_dir = QFileDialog.getExistingDirectory(None, "Select Image Folder", self.file_dir)
        if (file_dir != ""):
            self.setDirectory(file_dir)

    def reloadDirectory(self):
        # XXX This doesn't update the view sometimes, eg move a file into an
        #     empty directory and the directory will still show emtpy. Investigate
        self.model.reloadDirectory()

    def pasteClipboardFiles(self):
        """
        Retrieves files from the system clipboard and pastes them into the current directory,
        handling both copy and cut operations.
        """
        logger.info("%s", qApp.clipboard().mimeData())
        
        clipboard = qApp.clipboard()
        mime_data = clipboard.mimeData()

        if mime_data.hasUrls():
            urls = mime_data.urls()
            current_directory = self.file_dir

            # Determine if it's a cut (move) operation
            is_cut_operation = False
            if (mime_data.hasFormat("Preferred DropEffect")):
                data = mime_data.data("Preferred DropEffect")
                # 2 is WinForms.DragDropEffects.Move
                is_cut_operation = (data == struct.pack("<I", 2))

            reply = None
            for url in urls:
                if url.isLocalFile():
                    source_path = url.toLocalFile()
                    destination_path = os.path.join(current_directory, os.path.basename(source_path))

                    if (os.path.exists(destination_path)):
                        if (reply != QMessageBox.YesAll):
                            reply = QMessageBox.question(
                                self,
                                "Paste File",
                                "'%s' already exists, overwrite?" % os.path.basename(destination_path),
                                QMessageBox.Yes | QMessageBox.YesAll | QMessageBox.No | QMessageBox.Cancel,
                                QMessageBox.Cancel
                            )
                            if (reply not in [QMessageBox.Yes, QMessageBox.YesAll]):
                                continue
                        
                    try:
                        if is_cut_operation:
                            shutil.move(source_path, destination_path)
                            logger.info("Moved: %r to %r", source_path, destination_path)

                        else:
                            shutil.copy2(source_path, destination_path)
                            logger.info("Copied: %r to %r", source_path, destination_path)
                    except Exception as e:
                        logger.error("Error processing %r %s", source_path, e)
            
            self.reloadDirectory()

        else:
            logger.info("No files found in the clipboard.")


    def getSelectedFilepaths(self):
        logger.info("")
        selected_filepaths = [os.path.join(self.file_dir, index.data(Qt.UserRole).filename) for index in self.getActiveView().selectionModel().selectedRows()]
        if (len(selected_filepaths) == 0):
            selected_filepaths = [os.path.join(self.file_dir, self.getActiveView().currentIndex().data(Qt.UserRole).filename)]

        return selected_filepaths

    def copySelectedFilepaths(self):
        # XXX Another way of copying filepaths that some apps understand (eg
        #     Total Commander, Everything) is to set the filename, with metadata
        #     "49158 (FileName)". For multiple files this requires metadata 
        #     "49322 (Shell IDList Array)"
        
        # XXX In fact, Total Commander and Everything already use the file paths
        #     in text contexts, so for those apps having a way to copy the
        #     filepath is redundant with copying file contents. Everything even
        #     understands multiple files copied (Total Commander only pastes the
        #     filepath of the first one)

        filepaths = self.getSelectedFilepaths()
        logger.info("Copying filepaths %r", filepaths)
        clipboard = qApp.clipboard()
        clipboard.setText(string.join(filepaths, "\n"))

    def cutCopySelectedFiles(self, cut = False):
        # XXX Do something to gray out if cutting? (note the file doesn't really
        #     get cut until copied elsewhere so there's no point in refreshing
        #     the database here).
        
        # XXX Set the Qt::Itemflags to IsEnabled to False and hope the default
        #     delegate observes the flag?
        filepaths = self.getSelectedFilepaths()
        
        logger.info("%s files %r", "Cutting" if cut else "Copying", filepaths)
        urls = [QUrl.fromLocalFile(filepath) for filepath in filepaths]

        mimeData = QMimeData()
        mimeData.setUrls(urls)

        if (cut):
            # XXX Set translucency on the icon

            # Copy is supported transparently by setUrls, but cut needs
            # different support on Windows, KDE and Gnome
            # Eg see https://github.com/lxqt/libfm-qt/blob/master/src/utilities.cpp#L128
            
            # Windows
            # 2 is WinForms.DragDropEffects.Move
            mimeData.setData("Preferred DropEffect", struct.pack("<I", 2))
            # KDE
            # XXX Untested
            mimeData.setData("application/x-kde-cutselection", struct.pack("<I", 1))
            # Gnome, LXDE, and XFCE
            # Note url.toString() returns unicode but QByteArray won't take
            # unicode, convert to utf-8
            u = u"cut\n" + str.join("\n", [url.toString() for url in urls]) + "\n"
            mimeData.setData("x-special/gnome-copied-files", QByteArray(u.encode("utf-8")))

        qApp.clipboard().setMimeData(mimeData)

    def copySelectedFiles(self):
        self.cutCopySelectedFiles()

    def cutSelectedFiles(self):
        self.cutCopySelectedFiles(True)
    
    def deleteSelectedFiles(self):
        logger.info("")
        # XXX Have an option to send to recycle bin?
        filepaths = self.getSelectedFilepaths()
        reply = None
        for filepath in filepaths:
            if (reply != QMessageBox.YesAll):
                reply = QMessageBox.question(
                    self,
                    'Delete File',
                    'Are you sure you want to delete %r?' % filepath,
                    QMessageBox.Yes | QMessageBox.YesAll | QMessageBox.No | QMessageBox.Cancel,
                    QMessageBox.Cancel
                )

            if (reply in [QMessageBox.Yes, QMessageBox.YesAll]):
                logger.info("Deleting file %r", filepath)
                try:
                    # XXX Check if directory empty and warn again if not?
                    os_remove(filepath)
                        
                except Exception as e:
                    logger.error("Unable to delete file %r %r", filepath, e)

            elif (reply == QMessageBox.Cancel):
                break
        
        self.reloadDirectory()


class TwinWindow(QMainWindow):
    def __init__(self, left_file_dir, right_file_dir):
        super(TwinWindow, self).__init__()
        self.resize(1280, 1080)

        self.setupActions()

        self.profiling = False
        
        splitter = QSplitter(Qt.Horizontal)
        self.splitter = splitter
        
        self.file_panes = []
        for i in xrange(2):
            file_pane = FilePane()

            self.file_panes.append(file_pane)
            splitter.addWidget(file_pane)

        central_widget = splitter
        self.setCentralWidget(central_widget)

        self.updateWindowTitle()

        self.show()

        # Set the directories after showing the app so the FilePane loading
        # directory dialog boxes show on top of the app window and not in
        # isolation
        file_dirs = [left_file_dir, right_file_dir]
        for file_pane, file_dir in zip(self.file_panes, file_dirs):
            file_pane.setDirectory(file_dir)
        
        logger.info("App font %s pointSize %d height %d", qApp.font().family(), qApp.font().pointSize(), qApp.fontMetrics().height())

    def updateWindowTitle(self):
        self.setWindowTitle("%s - Twin" % self.getActivePane().file_dir)
        
    def setupActions(self):
        
        self.nextPaneAct = QAction("Next Pane", self, shortcut="tab", triggered=self.nextPane)

        self.leftToRightAct = QAction("Left to Right", self, shortcut="ctrl+right", triggered= lambda : self.leftToRight())
        self.rightToLeftAct = QAction("Right to Left", self, shortcut="ctrl+left", triggered= lambda: self.leftToRight(True))

        self.copySelectedFilesAct = QAction("Copy Files", self, shortcut="F5", triggered=self.copySelectedFiles, shortcutContext=Qt.ApplicationShortcut)
        self.moveSelectedFilesAct = QAction("Move Files", self, shortcut="F6", triggered=self.moveSelectedFiles, shortcutContext=Qt.ApplicationShortcut)

        self.diffDirsAct = QAction("Diff directories", self, shortcut="ctrl+m", triggered=self.diffDirectories, shortcutContext=Qt.ApplicationShortcut)

        self.swapPaneContentsAct = QAction("Switch Panes", self, shortcut="ctrl+u", triggered=self.swapPaneContents, shortcutContext=Qt.ApplicationShortcut)

        self.profileAct = QAction("Profile", self, shortcut="ctrl+p", triggered=self.profile, shortcutContext=Qt.ApplicationShortcut)

        # XXX LineEdit with directory name, bookmarks/favorites/history combobox
        # XXX Allow filtering files by typing name
        
        self.addAction(self.nextPaneAct)
        self.addAction(self.leftToRightAct)
        self.addAction(self.rightToLeftAct)
        self.addAction(self.copySelectedFilesAct)
        self.addAction(self.moveSelectedFilesAct)
        self.addAction(self.diffDirsAct)
        self.addAction(self.swapPaneContentsAct)
        self.addAction(self.profileAct)

    def leftToRight(self, reverse=False):
        logger.info("")

        source_pane = self.getRightPane() if reverse else self.getLeftPane()
        target_pane = self.getLeftPane() if reverse else self.getRightPane()
        
        # - if the cursor is on the target pane, use the source pane's dirpath
        # - If the cursor is on the source pane and over a non  ".." directory,
        #   use that directory as dirpath
        dirpath = source_pane.file_dir
        if (source_pane is self.getActivePane()):
            file_info = source_pane.getActiveView().currentIndex().data(Qt.UserRole)
            if (fileinfo_is_dir(file_info) and (file_info.filename != "..")):
                dirpath = os.path.join(dirpath, file_info.filename)

        target_pane.setDirectory(dirpath)

    def moveSelectedFiles(self):
        logger.info("")
        self.copyOrMoveSelectedFiles(True)

    def copySelectedFiles(self):
        logger.info("")
        self.copyOrMoveSelectedFiles(False)

    def copyOrMoveSelectedFiles(self, move):
        logger.info("move %s", move)

        filepaths = self.getSourcePane().getSelectedFilepaths()

        target_dir = self.getTargetPane().file_dir

        if (len(filepaths) > 0):
            action = "Move" if move else "Copy"
            # XXX Missing Yes All, No All buttons
            if (qYesNoCancelMessageBox(
                self, 
                "%s files" % action, 
                "%s %d file%s to\n%s" % (action, len(filepaths), "s" if len(filepaths) > 0 else "", target_dir),
                QMessageBox.Yes
                ) == QMessageBox.Yes):
                
                # XXX Needs to check that the selected file is not ..
                # XXX Show progress, cancel, queue/background, etc
                for filepath in filepaths:
                    try:
                        # XXX if destination exists, offer skip, rename,
                        #     overwrite all, yes all, no all standard buttons, etc
                        if (move):
                            logger.info("Moving %r to %r", filepath, target_dir)
                            shutil.move(filepath, target_dir)
                            logger.info("Moved: %r to %r", filepath, target_dir)

                        else:
                            logger.info("Copying %r to %r", filepath, target_dir)

                            shutil.copy2(filepath, target_dir)
                            logger.info("Copied: %r to %r", filepath, target_dir)

                    except Exception as e:
                        # XXX Display errors, offer ignore all, cancel, etc
                        logger.error("Error processing %r %s", filepath, e)

                # XXX Update the model and emit data change instead of forcing a
                #     reload? Do the reload only on corner cases? (eg files were
                #     overwritten)
                self.getSourcePane().reloadDirectory()
                self.getTargetPane().reloadDirectory()

    def swapPaneContents(self):
        logger.info("")
        
        # XXX Right now this only swaps the contents, should also swap the
        #     panes preserving selection, history, etc?
        left_view = self.getLeftPane().getActiveView()
        right_view = self.getRightPane().getActiveView()
        m_left = left_view.model()
        m_right = right_view.model()
        m_selection_left = left_view.selectionModel()
        m_selection_right = right_view.selectionModel()

        self.getLeftPane().setModels(m_right, m_selection_right)
        self.getRightPane().setModels(m_left, m_selection_left)

    def diffDirectories(self):
        logger.info("Start")
        # Sort both directories, mark newer or unique files
        
        # Selecting files can be slow when signals are fired individually,
        # create a selection and select that one
        
        r_left = 0
        r_right = 0
        m_left = self.getLeftPane().getActiveView().model()
        m_right = self.getRightPane().getActiveView().model()
        i_left = m_left.index(r_left,0)
        i_right = m_right.index(r_right,0)

        # Skip directories
        # XXX Use the right flag once fileinfos are integrated
        size_col = 3
        while (i_left.isValid() and (i_left.sibling(r_left, size_col).data(Qt.DisplayRole) == "<DIR>")):
            logger.info("Skipping dir %r", i_left.data(Qt.DisplayRole))
            r_left += 1
            i_left = m_left.index(r_left, 0)

        while (i_right.isValid() and (i_right.sibling(r_right, size_col).data(Qt.DisplayRole) == "<DIR>")):
            logger.info("Skipping dir %r", i_right.data(Qt.DisplayRole))
            r_right += 1
            i_right = m_right.index(r_right, 0)

        s_left = QItemSelection()
        s_right = QItemSelection()
        while (True):

            i_left = m_left.index(r_left, 0)
            i_right = m_right.index(r_right, 0)

            if (not(i_left.isValid() or i_right.isValid())):
                break

            # This assumes the models are similarly sorted
            c = 1 if (not i_left.isValid()) else (-1 if (not i_right.isValid()) else cmp(i_left.data(Qt.UserRole).filename, i_right.data(Qt.UserRole).filename))

            if (c == 0):
                assert None is logger.debug("Matching files %r vs. %r", i_left.data(Qt.DisplayRole), i_right.data(Qt.DisplayRole))
                # Advance both, add newest
                # display dates are lexycographically comparable
                # XXX Compare the right thing once all the fileinfo data is
                #     integrated
                date_col = 4
                # Note reversed comparison so newer files are selected
                c = cmp(i_right.sibling(r_right, date_col).data(Qt.DisplayRole), i_left.sibling(r_left, date_col).data(Qt.DisplayRole))

                # Undo the advance done below
                r_left += 0 if (c == -1) else 1
                r_right += 0 if (c == 1) else 1

                # Fall-through

            if (c == -1):
                assert None is logger.debug("Selecting left file %r", i_left.data(Qt.DisplayRole))
                # Add left, advance left
                s_left.select(i_left, i_left)
                r_left += 1

            elif (c == 1):
                assert None is logger.debug("Selecting right file %r", i_right.data(Qt.DisplayRole))
                # Add right, advance right
                s_right.select(i_right, i_right)
                r_right += 1

        self.getLeftPane().getActiveView().selectionModel().select(s_left, QItemSelectionModel.Select | QItemSelectionModel.Rows)
        self.getRightPane().getActiveView().selectionModel().select(s_right, QItemSelectionModel.Select | QItemSelectionModel.Rows)

        logger.info("Done")
        
    def getLeftPane(self):
        return self.file_panes[0]
    
    def getRightPane(self):
        return self.file_panes[1]

    def getSourcePane(self):
        if (self.focusWidget() is self.file_panes[0].getActiveView()):
            return self.file_panes[0]
        else:
            return self.file_panes[1]

    def getTargetPane(self):
        if (self.focusWidget() is self.file_panes[0].getActiveView()):
            return self.file_panes[1]
        else:
            return self.file_panes[0]

    def getActivePane(self):
        if (self.focusWidget() is self.file_panes[0].getActiveView()):
            return self.file_panes[0]
        else:
            return self.file_panes[1]

    def nextPane(self):
        logger.info("")
        if (self.focusWidget() is self.file_panes[0].getActiveView()):
            self.file_panes[1].getActiveView().setFocus()
        else:
            self.file_panes[0].getActiveView().setFocus()

        # XXX This doesn't update when directory changes on the pane, needs a
        #     filepane directory changed signal propagated to the app
        self.setWindowTitle("%s - Twin" % self.getActivePane().file_dir)

    def closeEvent(self, event):
        logger.info("closeEvent")
        # XXX Ignore cleanup at closeEvent time since it blocks unnecessarily
        #     at exit time when there are pending prefetches
        # self.cleanup()

        return super(TwinWindow, self).closeEvent(event)

    def profile(self):
        import cProfile
        if (self.profiling):
            self.pr.disable()
            self.pr.dump_stats(os.path.join("_out", "profile.prof"))
            logger.warn("Ended profiling")
            #self.showMessage("Ended profiling")

        else:
            #self.showMessage("Profiling...", 0)
            logger.warn("Profiling")
            self.pr = cProfile.Profile()
            self.pr.enable()
            
        self.profiling = not self.profiling
        
logger = logging.getLogger(__name__)
setup_logger(logger)
logger.setLevel(logging.WARNING)
logger.setLevel(logging.INFO)

if __name__ == '__main__':
    app = QApplication(sys.argv)
    
    default_file_dir = R"C:\Users\Public\Pictures"
    file_dirs = [default_file_dir, default_file_dir]

    if (len(sys.argv) > 1):
        file_dirs[0] = sys.argv[1]
        file_dirs[1] = sys.argv[min(2, len(sys.argv)-1)]

    for i, file_dir in enumerate(file_dirs):
        if (not os.path.exists(file_dir)):
            file_dir = QFileDialog.getExistingDirectory(None, "Select Image Folder", os.getcwd())
            if (file_dir == ""):
                file_dir = default_file_dir
            file_dirs[i] = file_dir

    window = TwinWindow(file_dirs[0], file_dirs[1])
    window.show()
    sys.exit(app.exec_())

#!/usr/bin/env python
"""
Twin panel file manager

## References

### Voidtools Everything api

Freely available sdk from https://www.voidtools.com/Everything-SDK.zip

See https://www.voidtools.com/support/everything/sdk/ See
https://www.voidtools.com/support/everything/sdk/python/

The DLL is just a layer on top of the WM_COPYDATA IPC, so that could also be
used directly without the need for the DLL

### Total Commander plugins (filessytem, packer)

https://www.ghisler.com/plugins.htm
https://plugins.ghisler.com/fsplugins/sampleplugin.zip
https://plugins.ghisler.com/fsplugins/fspluginhelp2.1se_chm.zip

https://github.com/ghisler/WFX-SDK
https://ghisler.github.io/WFX-SDK/contents.htm

https://github.com/ghisler/WCX-SDK
https://ghisler.github.io/WCX-SDK/table_of_contents.htm

Double commander includes WCX and WFX plugins with sources, see

https://doublecmd.github.io/doc/en/plugins.html
https://github.com/doublecmd/doublecmd

but they seem to use extra functions outside the standard API, may be
incompatible/require additional support


### Localsend

See https://github.com/meowrain/localsend-go/blob/main/internal/handlers/send.go
See https://github.com/localsend/protocol

## Qt Notes

### Model/View Incremental Row Loading

Essentially incremental row loading from Qt's point of view is a model where the
model reports that there are new rows available as rows are scrolled in, instead
of reporting all the rows from the start with a fixed rowCount()

In the model
- Return loaded_rows < total_rows in canFetchRow
- Increment loaded_rows in fetchMore rows, call beginInsertRows/endInsertRows to
  notify the views
- When updating total_rows and inserting new rows, send a single dummy
  beginInsertRow if rows are inserted at the end. Sending one per inserted row
  defeats the incremental loading, since it would make loaded_rows = total_rows

In the view
- Connect rowsInserted to code that calls fetchMore as long as there's room in
  the this works around a Qt limitation for which 
- Workaround the Qt bug for which loaded_rows for listviews in icon mode need to
  be a multiple of the items per row (otherwise keyboard down scrolling on the
  rightmost items gets stuck and doesn't advance).
- Return the size in the delegate 

Advantages
- Qt normally fetches all data for all the rows reported in rowCount, whether
  they are visible or not. By reporting less in rowCount, less data is fetched

Limitations/disadvantages
- Sorting is not possible, since not all the elements are available.
- Positioning on the upstream directory entry also breaks, since that entry may
  not be loaded yet
- Selecting all elements will only select the loaded elements.
- Comparing directories will give wrong results if not all the items are loaded.
- Scrollbar settings change as new rows are inserted
- It's not a virtual list, all rowCount() elements are kept in memory, other
  manual strategies are needed to lessen (evict images, emit dataChanged to
  force a reload)



### Full row QTableViews

Needs delegate to:
- Remove focus rect
- Highlight the whole row instead of just the focused cell

Needs filter events to:
- Ignore left/right navigation
  ...


### Image item delay loading / caching / evicting

- Schedule loading of the image when the Qt.DecorationRole is requested in
  data(), return a placeholder
- Whenever some image is received, emit dataChanged for that item.
- Whenever some image is evicted from the cache, emit dataChanged for the item
  using that image, otherwise Qt may not call data() to request the
  Qt.DecorationRole. If the item is still visible, Qt will call data() on that
  item and the image will be cached in. Relies on the fact that Qt ignores
  dataChanged for invisible items and doesn't call data() again until they are
  visible, ortherwise it would infinite loop.
- To prevent more recent image requests being queued behind older requests for
  items that may not even be visible anymore (items that have been scrolled away
  without waiting for the image), on every image received clear the request
  queues and emit dataChanged for all those items. This will cause Qt to call
  data(Qt.DecorationRole), which will issue new requests for the visible items'
  iamges. This again relies on the fact that Qt will ignore dataChanged for
  items that are not visible.


## Program Feature Requirements 

- Change to new directory
    - Needs cancellable
    - Needs backgroundable
    - Needs marging if cancelled

- Reload current directory
    - Needs merging

- Cancel background tasks

- Everything search

- Recursive string search

- Select and calculate directory size

- Calculate all directory sizes



"""

import __builtin__
import collections
import ctypes
import datetime
import errno
import json
import logging
import os
import platform
import Queue
import re
import shutil
import stat
import string
import struct
import sys
import time
import zipfile

# datetime.datetime.stptime when using ThreadPool threads sometimes fails on
# Python 2.7 with
#     AttributeError: 'module' object has no attribute '_strptime'
# Fix it by importing _strptime outside of the multithreaded code
# See https://stackoverflow.com/questions/32245560/module-object-has-no-attribute-strptime-with-several-threads-python
# See https://marc.info/?l=python-list&m=144408313516472&w=2
import _strptime

from PIL import Image, ImageQt, ExifTags

from PyQt5.QtCore import *
from PyQt5.QtGui import *
from PyQt5.QtWidgets import *

# - filename can be relative (to the class that generated the FileInfo, eg
#   FileInfoIterator.file_dir) or absolute. This allows holding regular directory listings
#   efficiently (relative to the pane's directory), everything search results
#   (absolute), or regular search results (absolute)
# - size is size in bytes
# - mtime is last modification UTC epoch in seconds
# - attr is FILEINFO_ATTR mask combination
FileInfo = collections.namedtuple("FileInfo", ["filename","size", "mtime", "attr"])

# Attributte masks for FileInfo.attr
# XXX Add system, archive, etc
FILEINFO_ATTR_DIR = 1 << 0
FILEINFO_ATTR_HIDDEN = 1 << 1
FILEINFO_ATTR_WRITABLE = 1 << 2
FILEINFO_ATTR_LINK = 1 << 3

# Information for shares / WFX plugins
WFXInfo = collections.namedtuple("WFXInfo", ["root", "dllpath"])

# Loaded WFX plugin state information
WFXState = collections.namedtuple("WFXState", ["procs", "c"])


def fileinfo_is_link(fileinfo):
    return ((fileinfo.attr & FILEINFO_ATTR_LINK) != 0)

def fileinfo_is_dir(fileinfo):
    return ((fileinfo.attr & FILEINFO_ATTR_DIR) != 0)

def fileinfo_is_packed(fileinfo):
    """
    Return if this is an archive (packed file format). Note this is a heuristic
    and not an exhaustive test
    """
    ext = os.path.splitext(fileinfo.filename)[1].lower()
    return (ext in PACKER_EXTENSIONS)

def fileinfo_is_hidden(fileinfo):
    return ((fileinfo.attr & FILEINFO_ATTR_HIDDEN) != 0)

def fileinfo_is_writable(fileinfo):
    return ((fileinfo.attr & FILEINFO_ATTR_WRITABLE) != 0)

def fileinfo_build_attr(is_dir, is_hidden, is_writable, is_link):
    return (
        (FILEINFO_ATTR_DIR if is_dir else 0) |
        (FILEINFO_ATTR_HIDDEN if is_hidden else 0) |
        (FILEINFO_ATTR_WRITABLE if is_writable else 0) |
        (FILEINFO_ATTR_LINK if is_link else 0) |
        0
    )

def fileinfo_cmp(a, b, field=0, reverse=False):
    """
    Compare FileInfos by the given field, name by default: ".." first, then
    directories sorted alphabetically, then files sorted alphabetically
    """
    a_is_dir = fileinfo_is_dir(a) 
    b_is_dir = fileinfo_is_dir(b) 

    assert field < len(a), "wrong field index %d" % field

    if (a == ".."):
        if (b == ".."):
            res = 0
        else:
            res = -1
    
    elif (b == ".."):
        res = 1

    elif (a_is_dir == b_is_dir):
        # Always compare dirs by name
        if ((field == 0) or a_is_dir):
            res = cmp(a.filename.lower(), b.filename.lower())
        else:
            res = cmp(a[field], b[field])

        # Don't reverse directory ordering, only files
        res = -res if (reverse and not a_is_dir) else res

    elif (a_is_dir):
        res = -1
        
    else:
        assert b_is_dir
        res = 1
        
    return res

def sort_fileinfos(file_infos, sort_field, sort_order):
    """
    Sort in place
    """
    logger.info("Sorting %d file_infos sort_field %d sort_order %d", len(file_infos), sort_field, sort_order)
    file_infos.sort(
        cmp=lambda a, b: fileinfo_cmp(a, b, sort_field, sort_order == Qt.DescendingOrder),
    )

    logger.info("Sorted")


def class_name(o):
    return o.__class__.__name__

class LineHandler(logging.StreamHandler):
    """
    Split lines in multiple records, fill in %(className)s
    """
    def __init__(self):
        super(LineHandler, self).__init__()

    def emit(self, record):
        # Find out class name, _getframe is supposed to be faster than inspect,
        # but less portable
        # caller_locals = inspect.stack()[6][0].f_locals
        caller_locals = sys._getframe(6).f_locals
        clsname = ""
        zelf = caller_locals.get("self", None)
        if (zelf is not None):
            clsname = class_name(zelf) + "."
            zelf = None
        caller_locals = None
        
        # Indent all lines but the first one
        indent = ""
        text = record.getMessage()
        messages = text.split('\n')
        for message in messages:
            r = record
            r.msg = "%s%s" % (indent, message)
            r.className = clsname
            r.args = None
            super(LineHandler, self).emit(r)
            indent = "    " 

def setup_logger(logger):
    """
    Setup the logger with a line break handler
    """
    logging_format = "%(asctime).23s %(levelname)s:%(filename)s(%(lineno)d):[%(thread)d] %(className)s%(funcName)s: %(message)s"

    logger_handler = LineHandler()
    logger_handler.setFormatter(logging.Formatter(logging_format))
    logger.addHandler(logger_handler) 

    return logger

def platform_is_32bit():
    """
    Return true if platform is 32bit
    """
    return (platform.architecture()[0] == "32bit")

def os_path_physpath(path):
    """
    - Return the physical path, ie the deepest path that is a file, as opposed
      to a "virtual" path inside a packed file, eg physdir1\myzip.zip\virtdir1\virtdir2
    - Return None if the path is invalid (no ancestor path exists)
    """
    # XXX Should this abspath before or should the caller do it?
    while (not os.path.exists(path)):
        # XXX Support files in temporary unpack directories by checking if the
        #     hash exists?
        prev_path = path
        path = os.path.dirname(path)
        if (path == prev_path):
            path = None
            break

    return path

def os_path_root(path):
    """
    - Return the parent root of the path, ie the topmost path that is not the
      drive or the unc
    - Return None if path has no parent
    """
    # Remove drive and unc, normalize slashes and pick the first component
    path = os.path.splitunc(os.path.splitdrive(path)[1])[1]
    path = os.path.normpath(path)
    # Note path will start with backward slash if the incoming path was
    # absolute, without for relative
    if (path.startswith(os.path.sep)):
        path = path[1:]
    components = path.split(os.path.sep)
    root = None if (len(components) == 1) else components[0]

    return root

def os_path_contained_extension_index(path, ext):
    """
    - case sensitive, lower or upper path and ext to make case insensitive
    - ext must contain the dot
    - returns -1 if not contained in the path
    """
    if (not path.endswith("\\")):
        path = path + "\\"
    i = index_of(path, ext + "\\")
    return i
    
def os_path_contains_extension(path, ext):
    """
    - case sensitive, lower or upper path and ext to make case insensitive
    - ext must contain the dot
    """
    return (os_path_contained_extension_index(path, ext) != -1)

def os_path_contains(parent, child, strict=False):
    """
    Check if parent path contains or is child path

    XXX This would be simpler if all directory paths are guaranteed to have
        terminating slash, make it so
    """
    # Can't use relpath because relpath raises if one is UNC and the other is
    # not and this function may be used to check those
    return (((child == parent) and not strict) or 
             (child.startswith(parent if parent.endswith(os.sep) else (parent + os.sep))))

def os_remove(filepath):
    if (os.path.isdir(filepath)):
        shutil.rmtree(filepath)
    else:
        os.remove(filepath)

def os_makedirs(dirpath):
    """
    Non-raising version of os.makedir (os.makedir doesn't raise if non-leaf
    directories exist, but it raises if the leaf exists)
    """
    try:
        os.makedirs(dirpath)
    except OSError as e:
        if (e.errno != errno.EEXIST):
            raise

def os_copy(filepath, target_dir):
    """
    Copy filepath (file or directory) inside target_dir
    """
    logger.info("%r to %r", filepath, target_dir)
    
    if (os.path.isdir(filepath)):
        if (os.path.abspath(target_dir).startswith(os.path.abspath(filepath))):
            logger.warn("Ignoring, targetdir %r is inside sourcedir %r", target_dir, filepath)
            return
        # shutil copytree raises if any file or directory exists, do it manually
        # shutil.copytree(filepath, os.path.join(target_dir, os.path.basename(filepath)))
        target_dir = os.path.join(target_dir, os.path.basename(filepath))
        os_makedirs(target_dir)
        for filename in os.listdir(filepath):
            os_copy(os.path.join(filepath, filename), os.path.join(target_dir, filename))
        shutil.copystat(filepath, target_dir)
        
    else:
        shutil.copy2(filepath, target_dir)

def xrange(list_or_int_start_stop, list_or_int_stop=None, step=None):
    def len_or_int(l):
        return l if isinstance(l, int) else len(l)

    if (list_or_int_stop is None):
        return __builtin__.xrange(len_or_int(list_or_int_start_stop))

    else:
        return __builtin__.xrange(len_or_int(list_or_int_start_stop), len_or_int(list_or_int_stop), step)

def index_of(l, item):
    try:
        return l.index(item)

    except ValueError:
        return -1

def rindex_of(l, item):
    try:
        return l.rindex(item)

    except ValueError:
        return -1

# ctypes equivalent of standard C types. The C parser and the C generator will
# strictly use types from this dict (plus pointers and aggregates)
ctypes_default_type_mapping = {
    "char": ctypes.c_char,
    "wchar": ctypes.c_wchar,
    "short" : ctypes.c_short,
    "int": ctypes.c_int,
    "long" : ctypes.c_long,

    "int16" : ctypes.c_int16,
    "int32" : ctypes.c_int32,
    
    "uint16" : ctypes.c_uint16,
    "uint32" : ctypes.c_uint32,

    "long long" : ctypes.c_longlong,
    "unsigned long long" : ctypes.c_ulonglong,

    "unsigned char" : ctypes.c_ubyte,
    "unsigned wchar" : ctypes.c_ushort,
    "unsigned short" : ctypes.c_ushort,
    "unsigned int" : ctypes.c_uint,
    "unsigned long" : ctypes.c_ulong,
    
    "unsigned" : "unsigned int",
    
    "float": ctypes.c_float,
    "double": ctypes.c_double,

    "void" : None,
    "uint32_t" : ctypes.c_uint32,
    "intptr_t" : ctypes.c_ssize_t,
    "uintptr_t" : ctypes.c_size_t,

    # These are here for print_types, since they are not specified in terms of
    # _POINTER but their own type
    "charptr_t" : ctypes.c_char_p,
    "wcharptr_t" : ctypes.c_wchar_p,
    "voidptr_t" : ctypes.c_void_p,
}

def ctypes_to_ccode(ctypes_type, ctypes_name=None):
    """
    Return a string containing C code for the given ctypes type
    """
    def get_type_name(ctypes_type):
        ctypes_type_name = ctypes_type.__name__
        if (ctypes_type in ctypes_default_type_mapping.values()):
            ctypes_type_name = ctypes_default_type_mapping.keys()[ctypes_default_type_mapping.values().index(ctypes_type)]
        return ctypes_type_name

    def format_type(ctypes_type, ctypes_name):
        
        if (isinstance(ctypes_type, (str, unicode))):
            # The name of a type, use that one directly
            return "%s %s" % (ctypes_type, ctypes_name)

        elif (ctypes_type in ctypes_default_type_mapping.values()):
            # Simple type, reverse search in the default mapping (lossless, may
            # return another type than declared)
            ctypes_type_name = get_type_name(ctypes_type)
            return "%s %s" % (ctypes_type_name, ctypes_name)
        
        elif (issubclass(ctypes_type, ctypes.Array)):
            # No need for recursive calls to arrays of pointers, etc, since it's
            # probably more desirable to use the type defined in the include
            # file rather than resolving it to a basic type
            item_type = ctypes_type._type_
            ctypes_type_name = get_type_name(item_type)
            array_length = ctypes_type._length_
            ctypes_name = "%s[%s]" % (ctypes_name, array_length)

            return "%s %s" % (ctypes_type_name, ctypes_name)
        
        elif (issubclass(ctypes_type, ctypes._Pointer)):
            # XXX Will this resolve "too much"? will it use a more natural type
            #     if not resolved?
            while (issubclass(ctypes_type, ctypes._Pointer)):
                ctypes_type = ctypes_type._type_
                ctypes_name = "*%s" % ctypes_name
            ctypes_type_name = get_type_name(ctypes_type)
            return "%s %s" % (ctypes_type_name, ctypes_name)
        
        else:
            return "%s %s" % (get_type_name(ctypes_type), ctypes_name)


    # Note issubclass checks class vs. class, while isinstance checks instance
    # vs. class. issubclass only supports checking classes and strings may come
    # through here for types with a name, so check that it's a type before
    # checking the subclass
    if (isinstance(ctypes_type, type) and issubclass(ctypes_type, ctypes.Structure)):
        # Convert ctypes structure to Python code (C struct equivalent)

        # Use the incoming name since multiple struct names are aliased to a
        # single type so it would only show one
        struct_code = "struct %s {\n" % ctypes_type.__name__ 
        for field_name, field_type in ctypes_type._fields_:
            formatted_type = format_type(field_type, field_name)
            
            struct_code += (" " * 4) + "%s;\n" % formatted_type
        struct_code += "}%s;" % ((" %s" % ctypes_name) if (ctypes_type.__name__  == ctypes_name) else "")
        return struct_code

    elif (isinstance(ctypes_type, type) and issubclass(ctypes_type, ctypes._CFuncPtr)):
        # XXX This needs to use something similar to format_type above on the
        #     result type and the arguments to properly resolve multiple
        #     pointers, arrays, etc
        arg_type_names = []
        for arg_type in ctypes_type._argtypes_:
            if (arg_type is None):
                arg_type_name = "void"
            
            elif (issubclass(arg_type, ctypes._Pointer)):
                base_type = arg_type._type_
                arg_type_name = "%s*" % get_type_name(base_type)

            else:
                arg_type_name = get_type_name(arg_type)

            arg_type_names.append(arg_type_name)
        return "%s %s(%s);" % ("void" if (ctypes_type._restype_ is None) else get_type_name(ctypes_type._restype_), ctypes_name, string.join(arg_type_names, ","))
        
    else:
        formatted_type = format_type(ctypes_type, ctypes_name)
        return "typedef %s;" % formatted_type

def ctypes_preprocess(s):
    """
    Remove most preprocessor directives and all the comments.

    XXX Note this doesn't ignore comments inside double quotation marks, etc

    XXX This should really take constant_mapping do the preprocess instead of just removing
        preprocessor directives

    See
    https://stackoverflow.com/questions/25735506/python-regex-reading-in-c-style-comments
    """
    if (False):
        # XXX This properly considers comments inside comments, but doesn't
        # consider preprocessor directives
        ss = ""
        i_start = 0
        i_end = 0 
        multi_start = -1
        single_start = -1
        while (True):
            # Refresh multi_sart and single_start, note it's necessary to
            # refresh both in case the start of one comment was inside the other
            # comment
            if (i_end > multi_start):
                multi_start = s.find("/*", i_end)
                multi_start = len(s) if (multi_start == -1) else multi_start

            if (i_end > single_start):
                single_start = s.find("//", i_end)
                single_start = len(s) if (single_start == -1) else single_start

            i_start = min(multi_start, single_start)

            ss += s[i_end:i_start]
            if (i_start == len(s)):
                break
            
            if (i_start == multi_start):
                # Find matching multiline comment end
                i_end = s.find("*/", i_start) + 2

            else:
                # Find end of line, note it's important to preserve end of lines
                # for fnding #define boundaries
                i_end = s.find("\n", i_start) + 1

        s = ss
    
    # XXX This doesn't ignore start of multiline inside of single line comment, 
    #     start of comment inside literal strings, etc
    # XXX extern "C" { } removal is brittle, relies on a brace in a line by
    #     itself, improve by counting open braces and closed braces
    # XXX This doesn't consider multiline preprocessor directives
    s = re.sub(r"""
        # Remove preprocesor/extern/single line comment from preprocessor until end of line
        (?:(?:\#ifdef|\#else|\#endif|\#ifndef|\#include|extern|//)[^\n]*|[}]\n)|
        # Remove multline comments
        (?:/[*].*?[*])/
    """, "", s, flags=re.VERBOSE|re.DOTALL)

    return s

def ctypes_map_type(type_mapping, base_type):
    # XXX Unify all ctypes_map_type callers to go through ctypes_parse_fields
    #     that does proper qualifier parsing and remove this const replacement
    base_type = base_type.replace("const", "")
    # XXX This shouldn't need a loop since all the types are resolved when
    #     created? Looks like this happens somewhat with types aliases entered
    #     by hand that resolve to another alias like "unsigned" -> "unsigned
    #     int", fix?
    while (base_type in type_mapping):
        logger.info("resolving %r", base_type)
        base_type = type_mapping[base_type]
        logger.info("resolved to %r", base_type)

    return base_type

def ctypes_get_or_create_type(type_mapping, constant_mapping, qualifiers, base_type_name, num_stars, array_size):
    """
    Creates a derived (pointer) type following qualifiers, num_stars and
    array_size or returns the same type if those are trivial
    - num_stars is the number of pointer operator (stars), 0 for none
    - qualifiers will be "" if no qualifiers
    - array_size will be None if no array
    - base_type_name is the s
    """
    # Only care about signed and unsigned qualifiers
    if ("unsigned" in qualifiers):
        base_type_name = "unsigned " + base_type_name
    
    if (base_type_name in type_mapping):
        ctypes_ftype = ctypes_map_type(type_mapping, base_type_name)

    else:
        raise ValueError("Unsupported type %r found in field." % base_type_name)

    if (num_stars > 0):
        # Special case pointer to c_char, ctypes treats c_char_p as null
        # terminated string and will automatically convert from/to Python
        # string, whie POINTER(c_char) is an array. This is noticeable on the
        # tProgressProc callbacks.
        if (ctypes_ftype is ctypes.c_char):
            ctypes_ftype = ctypes.c_char_p

        elif (ctypes_ftype is ctypes.c_wchar):
            ctypes_ftype = ctypes.c_wchar_p

        else:
            ctypes_ftype = ctypes.c_void_p if (ctypes_ftype is None) else ctypes.POINTER(ctypes_ftype)

        for _ in xrange(num_stars-1):
            ctypes_ftype = ctypes.POINTER(ctypes_ftype)

    if (array_size is not None):
        array_size = constant_mapping[array_size] if (array_size in constant_mapping) else int(array_size)
        # Create a ctypes array of the specified size
        ctypes_ftype = ctypes_ftype * array_size
        
    return ctypes_ftype

def ctypes_parse_fields(s, type_mapping, constant_mapping, field_separator):
    """
    Parse separated list of elements (pass comma for function arguments, semi colon
    for struct fields or simple typedefs)

    - where each element is
        - type name
        - const|signed|unsigned|volatile type name 
        - type name[number_or_constant_name]
        - type *name
        - type* name
        - type ***name
        - type*** name
        - type1 type2 name
    
    - or combinations of the above, eg
        - unsigned int a;
        - const signed char** path, int count
        - long long a;
        - unsigned long long b;

    return 
        - non empty array
        - None, failed to match
    """
    # Regular expression to match fields of form "type name" or "type name[size]" 
    # or "type *name"
    field_pattern = r"""
        \s* # consume any whitespace
        
        (?P<qualifiers> # qualifiers
            # XXX Remove CONST and support it properly as a define that gets 
            #     replaced
            ((const|signed|unsigned|volatile|CONST)\s+)*
        )
        (?P<type> # type, parse any stars later in the identifier as per C standard
            # allow stars after the type or before the name below, consume them 
            # here. Allow multiple whitespace-separated type names for eg 
            # "long long"
            # XXX Although looks like the multiple type names are restricted to 
            #     only a few so it should hard code them?
            (\w+(\s+\w+)*) # 1 or more type names
        )
        (?P<name> # list of stars/spaces plus one identifier
            ([*]|\s+)+\w+  # stars/spaces plus one identifier
            (\s*,\s*([*]|\s+)*\w+)* # list of star/paces plus one identifier
        ) 
        \s* # consume any whitespace
        # XXX The array should be moved up to the comma separated list of identifiers, 
        #     as it is only the last idenfiier can be an array
        (\[\s* # Optional array size
            (?P<arraysize> #optional arraysize as number or identifier
                \d+|\w+
            )
        \s*\])?
        \s*$ # consume any whitespace and force full string matching
    """

    fields = s.split(field_separator)

    # Prepare the fields list for ctypes.Structure
    ctypes_fields = []
    for field in fields:
        logger.info("field %s", field)
        field = field.strip()
        # Field can be empty because separator is sometimes terminator (eg
        # structs)
        if (field == ""):
            break
        m = re.match(field_pattern, field, re.VERBOSE)
        if (m is None):
            raise ValueError("Unsupported field %r found in fields %r." % (field, fields))
        qualifiers, field_type, field_name, array_size = m.group("qualifiers", "type", "name", "arraysize")
        # Ignore const, volatile
        field_type = field_type.strip()
        field_names = field_name.strip().split(",")
        base_type = field_type
        
        array_size if array_size is None else array_size.strip()
        for field_name in field_names:
            num_stars = field_name.count("*")
            field_name = field_name.replace("*", "").strip()
            field_type = ctypes_get_or_create_type(
                type_mapping, constant_mapping, 
                qualifiers,
                base_type, 
                num_stars,
                # XXX Remove once the array size is per identifier, for now
                #     assign to the last element which is the only one that can have
                #     array per regexp construction
                array_size if (field_name is field_names[-1]) else None
            )
            ctypes_fields.append((field_name, field_type))

    return ctypes_fields

def ctypes_parse_typedef(s, type_mapping, constant_mapping):
    """
    Parse a single simple typedef in the string s and add the type to type_mapping
    - Return None if the string doesn't contain a single typedef.

    typedef uintptr_t LPARAM;
    typedef intptr WPARAM;
    typedef void* LPVOID;
    typedef void *HANDLE;
    typedef char* extpath[1024];
    typedef char* path[MAX_PATH];
    """
    # Use a strict enough regexp so this doesn't catch struct definitions or
    # function declarations (no braces, no parens)
    m = re.match(r"\s*typedef\s+([^\(\{;]*;)\s*", s)

    if (m is None):
        return None

    tdef = m.group(1).strip()
    ctypes_fields = ctypes_parse_fields(tdef, type_mapping, constant_mapping, ";")

    for tdef_name, tdef_type in ctypes_fields:
        type_mapping[tdef_name] = tdef_type

    return m

def ctypes_parse_function(s, type_mapping, constant_mapping, proto_mapping):
    """
    Parse a single function prototype or a single function typedef.
    - Return None if it doesn't contain a single typedef

    Supported examples:

    typedef void (DCPCALL tExtensionInitializeProc)(tExtensionStartupInfo* StartupInfo);
    typedef void (DCPCALL tExtensionFinalizeProc)(void* Reserved);
    
    typedef int (__stdcall *tProgressProc)(int PluginNr,TCHAR* SourceName, TCHAR* TargetName,int PercentDone);

    int __stdcall FsInit(int PluginNr,tProgressProc pProgressProc, tLogProc pLogProc,tRequestProc pRequestProc);
    """
    
    # typedef style
    m = re.match(r"\s*typedef\s+(?P<rtype>[^(]*)\((?P<fname>[^)]*)\)\s*\((?P<fargs>[^)]*)\)\s*;\s*", s)
    is_stdcall = True
    is_proto = False
    if (m is None):
        # non-typedef style
        m = re.match(r"\s*(?P<rtype>[*]?\s*(\w+\s+)+)(?P<fname>\w+)\s*\((?P<fargs>[^)]*)\);\s*", s)

        if (m is None):
            return None
        rtype = m.group("rtype")
        # XXX Missing call convention type, this needs to map whatever type (eg
        #     WINAPI, DCPCALL) to see if it ends in __stdcall
        rtype = rtype.replace("__stdcall", "").strip()
        is_proto = True

    else:
        rtype = m.group("rtype")

    logger.info("groupdict %s", m.groupdict())
    
    fname = m.group("fname").strip()
    fargs = m.group("fargs").strip()

    # XXX Missing call convention type
    fname = fname.split()[-1]
    fname = fname.replace("*", "")
    
    num_stars = rtype.count("*")
    rtype = rtype.replace("*", "").strip()
    # XXX Missing splitting the qualifiers
    qualifiers = ""
    ctypes_rtype = ctypes_get_or_create_type(type_mapping, constant_mapping, qualifiers, rtype, num_stars, None)

    ctypes_fields = [] if (fargs == "void") else ctypes_parse_fields(fargs, type_mapping, constant_mapping, ",")
    
    fn = ctypes.WINFUNCTYPE(ctypes_rtype, *[field_type for field_name, field_type in ctypes_fields])
    # Wrap the unnamed function type into a named type, this is not necessary
    # and only needed for introspection purposes so ctypes_to_ccode can have
    # access to the type name, which otherwise is just "WinFunctionType"
    fn = type(fname, (fn,), dict(fn.__dict__))

    if (is_proto):
        proto_mapping[fname] = fn

    else:
        type_mapping[fname] = fn

    logger.info("fname %s restype %r argtypes %r", fname, fn._restype_, fn._argtypes_)

    return m

def ctypes_parse_struct(s, type_mapping, constant_mapping, pack=None):
    """
    Parse the single C struct in the string s. 
    - Return None if s doesn't contain a single struct.
    - Use pack struct packing if provided

    Supported examples

    typedef struct MyStruct { 
        int myField; 
        int field1, field2;
    };
    struct MyStruct { 
        int myField; 
        int field1, field2;
    } *PMyStruct, **PPMyStruct;

    See ctypes_parse_fields for more field examples
    """
    # parse the struct header
    m = re.match(r"\s*(typedef\s+struct|struct)(\s+(?P<sname>\w+))?\s*\{(?P<sbody>[^\}]*)\}\s*(?P<tnames>[^;]+)?;\s*", s)
    if (m is None):
        return None

    logger.info("groupdict %s", m.groupdict())
    
    # Split the struct type names by comma, add the struct name as another
    # struct type name
    struct_type_names = m.groupdict().get("tnames", "").split(",")
    struct_name = m.groupdict().get("sname", None)
    if (struct_name is not None):
        struct_type_names.append(struct_name)
    
    logger.info("struct_type_names %s", struct_type_names)

    # Parse the struct body 

    # Parse the fields in the struct string
    sbody = m.group("sbody")
    ctypes_fields = ctypes_parse_fields(sbody, type_mapping, constant_mapping, ";")

    # Dynamically create the ctypes Structure class with the passed class name
    d = {"_fields_": ctypes_fields}
    if (pack is not None):
        # Note that _pack_ must be set before fields when the Struct is created.
        # In this case the struct information is prestored on a dict and then
        # created, so it satisfies that.
        d.update({ "_pack_" : pack })

    # Parse the names of the struct type and add them to the type_mapping. Sort
    # them in reverse order so a non-pointer is created first and all the
    # pointers can refer to a non-pointer name (otherwise a name will be made
    # up)
    base_type = None
    base_type_name = ""
    # "*" is before any other identifier valid leading char (_A-Za-z) so a
    # regular reverse (higher first) sort guarantees that non pointer names will
    # appear first 
    # XXX Technically given the regular expression 
    for struct_name in sorted(struct_type_names, reverse=True):
        num_stars = struct_name.count("*")
        struct_name = struct_name.replace("*", "").strip()

        # XXX Call ctypes_create_type here?

        if (base_type is None):
            if (num_stars == 0):
                base_type_name = struct_name
            else:
                # There no non-pointer types, need to create a name the pointer
                # can refer to. Note this won't have an entry in type_mapping,
                # as any pointers or other aliases refer to it via the ctype,
                # not the name
                base_type_name = "Struct_%s" % struct_name
            
            base_type = type(base_type_name, (ctypes.Structure,), d)
        struct_type = base_type
        for _ in xrange(num_stars):
            struct_type = ctypes.POINTER(struct_type)
        
        type_mapping[struct_name] = struct_type

        logger.info("created struct type %s %s", struct_name, struct_type)

    assert None is logger.info("created struct type %s\n%s", base_type_name, ctypes_to_ccode(base_type, base_type_name))
    
    return m
    
def ctypes_parse_define(s, type_mapping, constant_mapping):
    """
    Parse simple preprocessor #defines. If the value refers to a previous define
    it will be resolved to the other define's value


    Eg

    #define FS_FILE_OK -1 

    #define FS_FILE_YES FS_FILE_OK

    
    XXX Support simple math operations like prevconstant+1?

    XXX Do something about #defines to a function name? eg but most of the time
        that needs #ifdef support, eg

    #ifdef UNICODE

    #define Everything_GetRunCountFromFileName Everything_GetRunCountFromFileNameW
    """
    m = re.match(r"\s*#\s*define\s+(\w+)\s+([^\n]*)", s)

    if (m is None):
        return None

    dname, dvalue = m.groups()
    dvalue = dvalue.strip()

    try:
        # Base 0 means get the base from the string prefix (0x, etc)
        dvalue = int(dvalue, 0)
    except ValueError:
        try:
            dvalue = float(dvalue)
        except ValueError:
            logger.info("direct dvalue is not numeric %r", dvalue)

    # Values can refer to other values, undo the redirection (note a single
    # redirection lookup is enough since all redirections are undone at creation
    # time)
    dvalue = constant_mapping.get(dvalue, dvalue)
    constant_mapping[dname] = dvalue
    
    return m

def ctypes_parse_definitions(s, type_mapping, constant_mapping, proto_mapping, struct_pack=None):
    """
    Parse multiple function declarations, defines, and struct definitions from a
    single string.

    See https://cs.wmich.edu/~gupta/teaching/cs4850/sumII06/The%20syntax%20of%20C%20in%20Backus-Naur%20form.htm
    See https://github.com/katef/kgt/blob/main/examples/c99-grammar.iso-ebnf
    """

    s = ctypes_preprocess(s)

    while (True):
        # Parse typedefs before structs and functions, parse structs before
        # functions, this is an easy way of preventing ctypes_parse_function
        # confusing a struct with a typedef function called struct
        
        # XXX For the struct vs. function case, trap it in parse_function by
        #     looking at fname? struct is a reserved word anyway
        # XXX For the simple typedef vs. function or struct case, the lack of
        #     braces or parenthesis are probably enough to be discarded there

        # XXX All these return the match, but only the end position is used,
        #     should just return that or return the string or use a file
        #     abstraction over a string? But note the success/error is needed so
        #     the loop is restarted because trying each type in order is
        #     necessary (see above)
        m = ctypes_parse_typedef(s, type_mapping, constant_mapping)
        if (m is not None):
            s = s[m.end():]
            continue
        m = ctypes_parse_struct(s, type_mapping, constant_mapping, struct_pack)
        if (m is not None):
            s = s[m.end():]
            continue
        m = ctypes_parse_define(s, type_mapping, constant_mapping)
        if (m is not None):
            s = s[m.end():]
            continue
        m = ctypes_parse_function(s, type_mapping, constant_mapping, proto_mapping)
        if (m is None):
            break
        s = s[m.end():]

    assert s.strip() == "", "Not the whole string was parsed %r" % s

def ctypes_hook_dll(type_mapping, constant_mapping, proto_mapping, dlls):
    """
    Create ctype constants, types, and functions with the proper argument and
    result typing for all the function prototypes present in the DLLs
    """
    c = {}
    if (not isinstance(dlls, list)):
        dlls = [dlls]

    # Hook constants and types. Note some type names (eg unsigned short) are not
    # valid identifiers, ignore. Also, namedtuple doesn't accept leading
    # underscores, ignore
    # XXX See the source code of named tuple for a more complete check
    for name, ctype in type_mapping.iteritems():
        if ((" " not in name) and (not name.startswith("_"))):
            c[name] = ctype

    for name, ctype in constant_mapping.iteritems():
        if ((" " not in name) and (not name.startswith("_"))):
            c[name] = ctype

    # Hook prototypes of functions present in the dlls
    for name, ctype in proto_mapping.iteritems():
        # Don't check for invalid id, let it fail since functions are important
        # enough that they should cause errors (unlike types, where they just
        # don't get exposed by name but can still be used by reference by
        # arguments, etc)
        for dll in dlls:
            if (hasattr(dll, name)):
                fn = getattr(dll, name)
                fn.argtypes = ctype._argtypes_
                fn.restype = ctype._restype_
                c[name] = fn
                break

    # XXX Using namedtuples prevents from easily adding more fields which is
    #     desirable in some cases (eg add function aliases), use modifiable
    #     named tuples?
    # XXX Using namedtuples also prevents from using leading underscore in the
    #     fields which some C definitions use
    C = collections.namedtuple("C", c.keys()) 
    c = C(**c)

    return c

class CTypesHelper(object):
    """
    Helper to parse include files and hook the dll functions in those include
    files

    Usage:
        c_helper = CTypesHelper("include.h", "dll.dll")
        ...
        c = c_helper()

        find_data = c.WIN32_FIND_DATAW()
        handle = c.FindFirst("c:\\*.*", find_data)
        ...

    XXX Have a hook function so parsing can be done independently from hooking? 
        (eg for WCX/WFX plugins, the parsing is global but the hooking is per DLL)
        In that case, the DLL parameter can be empty or None?
    """
    def __init__(self, includes, dlls):
        """
        - dlls one of
            - string or list of strings with filepaths to dlls to load
            - dll or list of dlls loaded with ctypes.WinDLL
        - inlcudes one of
            - string or list of strings with definitions
            - string or list of strings with filepaths to include files

        The parsing and DLL loading is done on the first invocation of __call__

        XXX Does it really make sense to have multiple dlls? what if they have 
            colliding functions?
        """
        self.c = None

        # Convert from single item to string
        self.dlls = dlls if (isinstance(dlls, (tuple, list))) else [dlls]
        self.includes = includes if (isinstance(includes, (tuple, list))) else [includes]

    def update(self, d):
        """
        Update/add fields

        This should be done after loading. Note the reference returned by c()
        has changed so the caller should refresh any c() cached copies
        """
        c_dict = self.c._asdict()
        c_dict.update(d)
        C = collections.namedtuple("C", c_dict.keys())
        self.c = C(**c_dict)

        return self()

    def __call__(self):
        if (self.c is None):
            types, consts, protos = dict(ctypes_default_type_mapping), {}, {}

            for include in self.includes:
                if (os.path.exists(os.path.join(INCLUDE_DIR, include))):
                    include = open(os.path.join(INCLUDE_DIR, include), "r").read()
                ctypes_parse_definitions(include, types, consts, protos)

            dlls = []
            for dll in self.dlls:
                # The dll may be given by the short name if in the path, don't
                # check the filename, check the type
                if (not isinstance(dll, ctypes.WinDLL)):
                    # XXX Ignore failures in case caller want's to pass win32
                    #     and win64 dlls?
                    dll = ctypes.WinDLL(dll)
                
                dlls.append(dll)

                self.c = ctypes_hook_dll(types, consts, protos, dll)

            # Keep a reference to prevent garbage collection
            self.dlls = dlls

        return self.c

def ctypes_parse_test():
    windows_type_mapping = {
        'CHAR': "char",
        'WCHAR': "wchar",
        'TCHAR': "WCHAR",

        'WORD': "uint16",
        'DWORD': "uint32",
        'LONG': "int32",

        "BOOL" : "int32",
        "WPARAM" : "uintptr_t",
        "LPARAM" : "intptr_t",

        'HANDLE': "voidptr_t",
        'HICON': "HANDLE",
        'HBITMAP': "HANDLE",
        'HWND': "HANDLE",
    }

    def print_types(type_mapping):
        for ctype_name in type_mapping:
            # Note this doesn't preserve the declaration order, so the usage may
            # appear before the definition
            if (ctype_name not in ctypes_default_type_mapping):
                logger.info(ctypes_to_ccode(type_mapping[ctype_name], ctype_name))

    def test_defines():
        type_mapping = dict(ctypes_default_type_mapping)
        constant_mapping = {  }

        s = "#define MAX_PATH 265"
        ctypes_parse_define(s, type_mapping, constant_mapping)

        s = "#define EXT_MAX_PATH MAX_PATH"
        ctypes_parse_define(s, type_mapping, constant_mapping)

        s = "typedef char PATH[EXT_MAX_PATH];"
        ctypes_parse_typedef(s, type_mapping, constant_mapping)

        print_types(type_mapping)

    def test_typedefs():
        typedefs = """
            typedef CONST char *LPCSTR,*PCSTR;
            typedef long long LONGLONG;
            typedef unsigned long long ULONGLONG;
            typedef uintptr_t LPARAM;
            typedef void* LPVOID;
            typedef void *HANDLE;
            typedef char* path[MAX_PATH];
            typedef char* path[1024];
            typedef char** path[1024];
        """
        type_mapping = dict(ctypes_default_type_mapping)
        for l in typedefs.splitlines():
            if (l.strip() == ""):
                continue
            m = ctypes_parse_typedef(l, type_mapping, { "MAX_PATH" : 265 })
            assert m is not None, "None parsing %r" % l

        print_types(type_mapping)
        
    def test_structs():
        type_mapping = dict(ctypes_default_type_mapping)
        type_mapping.update(windows_type_mapping)
        constant_mapping = { "MAX_PATH": 260 }

        ctypes_parse_struct("""
            typedef struct _FILETIME {
                DWORD dwLowDateTime;
                DWORD dwHighDateTime;
            } FILETIME,*PFILETIME,*LPFILETIME;
        """, type_mapping, constant_mapping)

        ctypes_parse_struct("""
            typedef struct {
                DWORD SizeLow,SizeHigh;
                DWORD SizeLow1,SizeHigh1[100];
                DWORD* *SizeLow2,*SizeHigh2;
                FILETIME LastWriteTime;
                int Attr;
            } RemoteInfoStruct;
        """, type_mapping, constant_mapping)
    
        s = """
            typedef struct _WIN32_FIND_DATAA {
                DWORD    dwFileAttributes;
                FILETIME ftCreationTime;
                FILETIME ftLastAccessTime;
                FILETIME ftLastWriteTime; /* Comment */
                DWORD    nFileSizeHigh;
                DWORD    nFileSizeLow;
                DWORD    dwReserved0;
                DWORD    dwReserved1;
                CHAR     cFileName[MAX_PATH];
                CHAR     cAlternateFileName[14];
                DWORD    dwFileType; // Obsolete. Do not use.
                DWORD    dwCreatorType; // Obsolete. Do not use
                WORD     wFinderFlags; // Obsolete. Do not use
            } WIN32_FIND_DATAA, *PWIN32_FIND_DATAA, *LPWIN32_FIND_DATAA;
        """ 
        s = ctypes_preprocess(s)
        ctypes_parse_struct(s, type_mapping, constant_mapping)

        print_types(type_mapping)

    def test_functions():
        type_mapping = dict(ctypes_default_type_mapping)
        type_mapping.update(windows_type_mapping)
        constant_mapping = { "MAX_PATH": 260 }
        proto_mapping = {}

        s = "void void_function(void);"
        ctypes_parse_function(s, type_mapping, constant_mapping, proto_mapping)

        s = "HANDLE __stdcall FsFindFirst(TCHAR* Path, WIN32_FIND_DATA *FindData);"
        ctypes_parse_typedef("typedef unsigned long WIN32_FIND_DATA;", type_mapping, constant_mapping)
        ctypes_parse_function(s, type_mapping, constant_mapping, proto_mapping)

        s = "typedef void (DCPCALL tExtensionInitializeProc)(tExtensionStartupInfo* StartupInfo);"
        ctypes_parse_typedef("typedef unsigned long tExtensionStartupInfo;", type_mapping, constant_mapping)
        ctypes_parse_function(s, type_mapping, constant_mapping, proto_mapping)

        s = "typedef int (__stdcall *tProgressProc)(int PluginNr,TCHAR* SourceName, TCHAR* TargetName,int PercentDone);"
        ctypes_parse_function(s, type_mapping, constant_mapping, proto_mapping)

        s = "int __stdcall FsInit(int PluginNr, tProgressProc pProgressProc);"
        ctypes_parse_function(s, type_mapping, constant_mapping, proto_mapping)

        type_mapping.update(proto_mapping)
        print_types(type_mapping)

    test_defines()
    test_typedefs()
    test_structs()
    test_functions()

POSIX_EPOCH_DATETIME = datetime.datetime.utcfromtimestamp(0)
def datetime_to_utctimestamp(d):
    return (d - POSIX_EPOCH_DATETIME).total_seconds()

WINDOWS_EPOCH_DATETIME = datetime.datetime.strptime('1601-01-01 00:00:00', '%Y-%m-%d %H:%M:%S')
WINDOWS_TICKS = int(1/10**-7)  # 10,000,000 (100 nanoseconds or .1 microseconds)
WINDOWS_TO_POSIX_EPOCH_DIFF = (POSIX_EPOCH_DATETIME - WINDOWS_EPOCH_DATETIME).total_seconds()  # 11644473600
WINDOWS_TICKS_TO_POSIX_EPOCH = WINDOWS_TO_POSIX_EPOCH_DIFF * WINDOWS_TICKS  # 116444736000000000.0
def win32_filetime_to_timestamp(filetime):
    # Convert a windows FILETIME to a python datetime
    # https://stackoverflow.com/questions/39481221/convert-datetime-back-to-windows-64-bit-filetime
        
    filetime_value = (filetime.dwHighDateTime << 32) | filetime.dwLowDateTime
    timestamp = (filetime_value / WINDOWS_TICKS) - WINDOWS_TO_POSIX_EPOCH_DIFF
    
    return timestamp

# XXX Move to the include file, but how to express this? (.h files only support
#     #define constants, and -1 cannot be used because it note this cannot be
#     expressed via aneeds to be a positive number since comparing against -1
#     doesn't work for c_void_p)
WIN32_INVALID_HANDLE_VALUE = 2**64-1
def win32_get_last_error():
    """
    Log and return the code and message for the WIN32 API GetLastError
    """
    # Load the kernel32 DLL, which contains the GetLastError function
    kernel32 = ctypes.windll.kernel32

    # Call GetLastError to retrieve the last error code
    error_code = kernel32.GetLastError()

    # Print the error code

    # If you want to map the error code to a message, you can use FormatMessage
    # to get more information about the error (this part is optional)
    FORMAT_MESSAGE_FROM_SYSTEM = 0x00001000
    buffer = ctypes.create_unicode_buffer(512)
    kernel32.FormatMessageW(
        FORMAT_MESSAGE_FROM_SYSTEM,
        None,
        error_code,
        0,
        buffer,
        len(buffer),
        None
    )

    logger.info("%d: %r", error_code, buffer.value)

    return error_code, buffer.value

# Constants for LocalSend protocol
LOCALSEND_MULTICAST_GROUP = '224.0.0.167'
LOCALSEND_MULTICAST_PORT = 53317
LOCALSEND_HTTP_PORT = 53317
LOCALSEND_API_BASE = '/api/localsend/v2'
LocalsendDevice = collections.namedtuple("LocalsendDevice", "alias, version, deviceModel, deviceType, fingerprint, host, port, protocol, download")
def localsend_discover_devices(timeout):
    import uuid
    import socket
    import threading

    listener_started = threading.Event()

    def make_fingerprint():
        # XXX This should be the sha256 of this peer's HTTPS server certificate,
        #     but right now only uploads via client HTTPS are implemented. It's
        #     not clear peers verify that anyway, since it has zero security
        #     unless Trust On First Use or similar is implemented
        return str(uuid.uuid4())

    def listen_for_responses_udp(sock, myinfo, devices, timeout=5.0):
        """
        Listen for multicast responses on the socket. This function will run on
        a separate thread.
        """
        start = time.time()
        fingerprints = set()
        listener_started.set()
        while True:
            try:
                logger.info("recvfromming for %d/%d secs", sock.gettimeout(), timeout)
                data, addr = sock.recvfrom(4096)
                logger.info("recvfrommed %s %s bytes", addr, len(data) if data is not None else 0)
                # Parse the response JSON
                try:
                    resp = json.loads(data)
                    logger.info("%r", resp)
                except Exception as e:
                    logger.error("exception parsing %s", e)
                    continue

                # Ignore responses from our own device
                if (resp.get('fingerprint') == myinfo.get('fingerprint')):
                    logger.info("Ignoring device with own fingerprint")
                    continue

                # Reply to announcement requests Announce is v2, announcement is
                # v1, official app seems to always send both
                # XXX Disabled for now, some devices/app versions request
                #     multiple times and may cause other discovery to be lost?
                #     The peers already get this peer's information its
                #     announcement request
                reply_to_announcements = False
                if (resp.get("announce", resp.get("announcement", False)) and reply_to_announcements):
                    logger.info("Peer requested announcement, sending")
                    d = dict(myinfo)
                    d["announce"] = False
                    d["announcement"] = False
                    msg = json.dumps(d).encode('utf-8')
                    sock.sendto(msg, (LOCALSEND_MULTICAST_GROUP, LOCALSEND_MULTICAST_PORT))

                if (resp.get("fingerprint") in fingerprints):
                    logger.info("ignoring duplicated device %r", resp)
                    continue

                # Add the device to the list of discovered devices
                dev = LocalsendDevice(
                    alias=resp.get('alias'),
                    version=resp.get('version'),
                    deviceModel=resp.get('deviceModel'),
                    deviceType=resp.get('deviceType'),
                    fingerprint=resp.get('fingerprint'),
                    host=addr[0],
                    port=resp.get('port', LOCALSEND_HTTP_PORT),
                    protocol=resp.get('protocol', 'https'),
                    download=resp.get('download', False)
                )

                devices.append(dev)
                fingerprints.add(dev.fingerprint)
                
            except socket.timeout:
                logger.info("socket %d secs timeout hit", sock.gettimeout())

            except Exception as e:
                logger.error("socket exception %s", e)
                
            # Stop after the timeout duration
            if ((time.time() - start) > timeout):
                logger.info("global timeout %d secs, finishing", timeout)
                break

    def send_announcement(myinfo, sock):
        """
        Send a multicast announcement requesting other devices to reply. This
        will be done in the main thread.

        XXX Some devices/app versions don't respond to this, sometimes you need
            to reopen the app or tap the refresh devices while listening for
            replies
        """
        myinfo = dict(myinfo)
        myinfo['announce'] = True
        myinfo['announcement'] = True
        msg = json.dumps(myinfo).encode('utf-8')
        sock.sendto(msg, (LOCALSEND_MULTICAST_GROUP, LOCALSEND_MULTICAST_PORT))

    def discover_via_multicast(myinfo, timeout=5.0):
        """
        Discover devices via multicast by using two threads:
        - One to listen for responses
        - One to send the announcement

        You need to quit the Localsend app / stop the Localsend app server on
        the local machine.

        - Self announcement is received a few ms after sent
        - 1.17 protocol 2.1 on samsung responds multiple times, 1s after
          announcement, 254 bytes
        - 1.10 protocol 2.0 on hd tablet responds single time, 2s after
          announcement, 247 bytes
        """
        devices = []

        hostname, alias_list, ips = socket.gethostbyname_ex(socket.gethostname())

        # Listening on all interfaces and using as IP_ADD_MEMBERSHIP INADDR_ANY
        # sometimes causes responses not to be received on Windows 10 with wifi
        # and wired interfaces (even if wifi is "Media Disconnected" as per
        # "ipconfig"), stating the interface explicitly seems to fix it
        for ip in ips:
            # Create a UDP socket for receiving responses
            sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM, socket.IPPROTO_UDP)
            sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            # Set a small timeout so the loop has fine granularity when checking the
            # global timeout, but not too small that responses are not received (the
            # symptom is that the Localsend app on the local machine is discovered,
            # but not other machines)
            sock.settimeout(5)

            # Bind the socket to the multicast group in all the interfaces
            logger.info("Binding listener socket to %s", ip)
            sock.bind((ip, LOCALSEND_MULTICAST_PORT))
            # mreq = struct.pack("4sl", socket.inet_aton(LOCALSEND_MULTICAST_GROUP), socket.INADDR_ANY)
            mreq = struct.pack("4s4s", socket.inet_aton(LOCALSEND_MULTICAST_GROUP), socket.inet_aton(ip))
            sock.setsockopt(socket.IPPROTO_IP, socket.IP_ADD_MEMBERSHIP, mreq)

            # Start the listener thread
            timeout = 15
            listener_thread = threading.Thread(target=listen_for_responses_udp, args=(sock, myinfo, devices, timeout))
            listener_thread.start()

        # Wait for the thread to start to send the announcements, trying to
        # prevent the announcement and response from happening before the
        # listener starts. More a heuristic than anything, since there's no
        # telling when thread context switches happen
        # XXX There could be multiple if multiple ips, fix
        listener_started.wait()

        # Send a few multicast announcements while the listener thread is running
        retries = 3
        logger.info("hostname %s alias_list %s ips %s", hostname, alias_list, ips)
        for _ in xrange(retries):
            # Send via a specific interface, otherwise INADDR_ANY multicast
            # send  will fail when there are multiple interfaces even if only
            # a single interface is enabled (eg wifi and wired where Windows has
            # disabled wifi because of wired). The symptom is that it fails to
            # discover any, possibily because the announcement never arrived
            for ip in ips:
                # See https://stackoverflow.com/questions/10702870/how-to-multicast-send-to-all-network-interfaces
                sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM, socket.IPPROTO_UDP)
                sock.setsockopt(socket.IPPROTO_IP, socket.IP_MULTICAST_IF, socket.inet_aton(ip))
                
                logger.info("Sending announcement via %s", ip)
                send_announcement(myinfo, sock)
            time.sleep(timeout * 1.0/retries)

        # Wait for the listener thread to finish
        listener_thread.join()
        
        sock.close()
        return devices

    fingerprint = make_fingerprint()
    # XXX Convert to LocalsendDevice for consistency?
    myinfo = {
        'alias': 'Twin ' + APPLICATION_VERSION,
        'version': '2.1',
        'deviceModel': 'Python',
        'deviceType': 'desktop',
        'fingerprint': fingerprint,
        'port': LOCALSEND_HTTP_PORT,
        'protocol': 'https',
        'download': False,
    }
    devices = discover_via_multicast(myinfo, timeout=timeout)

    return devices, myinfo

def localsend_upload_to_device(myinfo, device, filepath):
    import httplib
    import ssl
    timeout = 10
    
    def create_ssl_context():
        # The sha256 device's certificate can be validated against the
        # fingerprint, but there's no extra security in doing so, so just use an
        # unverified context
        # XXX Assuming the certificate doesn't change with invocations,
        #     implement "trust on first use", see
        #     https://github.com/localsend/localsend/issues/357
        #     see https://en.wikipedia.org/wiki/Trust_on_first_use
        if (False):
            context = ssl._create_unverified_context()
        else:
            context = ssl.create_default_context()
            context.check_hostname = False
            context.verify_mode = ssl.CERT_NONE
        return context

    def prepare_transfer(myinfo, device, filepath):
        """
        Prepare the transfer by making an HTTP request to the device.
        The device responds with metadata for the transfer.
        """
        # XXX This could prepare multiple filepaths, will need different ids per
        #     filename in the payload below
        context = create_ssl_context()
        conn = httplib.HTTPSConnection(device.host, device.port, timeout=timeout, context=context)
        conn.set_debuglevel(10)
        conn.connect()

        filename = os.path.basename(filepath)

        headers = {'Content-Type': 'application/json'}
        payload = {
            "info" : myinfo,
            "files" : {
                filename : {
                        "id": "1",
                        "fileName": filename,
                        "size": os.path.getsize(filepath),
                        "fileType": "application/octet-stream",
                        "sha256" : None,
                        # XXX Fill in the other metadata
                        #"sha256": "*sha256 hash*", # nullable
                        #"preview": "*preview data*", # nullable
                        #"metadata": { # nullable
                        #    "modified": "2021-01-01T12:34:56Z", # nullable
                        #    "accessed": "2021-01-01T12:34:56Z", # nullable
                        #}
                }
            }
        }
        conn.request('POST', LOCALSEND_API_BASE + '/prepare-upload', json.dumps(payload), headers =headers)

        response = conn.getresponse()
        data = response.read()
        logger.info("%r", data)
        conn.close()

        if (response.status != 200):
            raise Exception("Failed to prepare transfer: %s" % data)

        return json.loads(data)

    def upload_file(device, session_id, file_id, token_id, filepath):
        """
        Upload the file to the device using the sessionId, fileId and tokenId.
        """
        # XXX This could upload multiple filepaths, will need to use the same
        #     filename ids as the prepare above
        # XXX The app can do directory uploads, test how it works, deriving the
        #     directory from the relative path in the payload?
        
        # Open file and send
        with open(filepath, 'rb') as file:
            # HTTPS connection with SSL context
            context = create_ssl_context()
            conn = httplib.HTTPSConnection(device.host, device.port, context=context, timeout=timeout)
            conn.set_debuglevel(10)
            conn.connect()

            headers = {
                'Content-Type': "application/octet-stream",
                'Content-Length': str(os.path.getsize(filepath))
            }
            conn.request('POST', LOCALSEND_API_BASE + '/upload?sessionId=%s&token=%s&fileId=%s' % (session_id, token_id, file_id), body=file, headers=headers)
            response = conn.getresponse()
            data = response.read()
            conn.close()

            logger.info("%r", data)

            if (response.status != 200):
                raise Exception("Failed to upload file: %s" % data)

        return json.loads(data)

    # XXX This could send multiple filepaths
    prep = prepare_transfer(myinfo, device, filepath)
    result = upload_file(device, prep["sessionId"], "1", prep["files"]["1"], filepath)

    return result

# MAJOR.MINOR.PATCH
# MAJOR version when you make incompatible API changes,
# MINOR version when you add functionality in a backwards compatible manner, and
# PATCH version when you make backwards compatible bug fixes.
# 0.0.1
# - Config file, tabs, bookmarks, external diff, 
# - fixes to localsend, dir comparision, ScaledIconDelegate
# 0.1.0 
# - Sorted columns, loading indicator, choosetab on right click
# - Fixes to current_tab settings, headerChooser crash, stale image crash
APPLICATION_VERSION = "0.1.0"
# 0.0.1 Added config file
# 0.1.0 Added sorting settings
CONFIG_FILE_VERSION = "0.1.0"

INCLUDE_DIR = "include"
TEMP_DIR = os.path.join("_out", "temp")

# XXX This needs to use the imagereader/PIL supported extensions
IMAGE_EXTENSIONS = ('.bmp','.enc','.gif', '.jpg', '.jpeg', '.jfif', '.png', '.webp')
FILTERED_EXTENSIONS = []
# See https://www.7-zip.org/
# Note remove ".bz2" so it uses ghisler bzip2dll for testing
# Note remove ".zip" so it uses native support
# Note remove ".iso" so it uses iso.wcx64 for testing
PACKER_7ZIP_EXTENSIONS = (".7z", ".xz", ".gz", ".tar", ".tgz", ".wim", "bz2") 
PACKER_7ZIP_EXTENSIONS_UNPACK_ONLY = (".apfs", ".ar", ".arg", ".cab", ".chm", 
    ".cpio", ".cramfs", ".deb", ".dmg", ".ext", ".fat", ".gpt", ".hfs", "ihex", 
    ".iso", ".lzh", ".lzma", ".mbr", ".msi", ".nsis", ".ntfs", ".qcow2", ".rar", 
    ".rpm", ".squashfs", ".udf", ".uefi", ".vdi", ".vhd", ".vhdx", ".vmdk", ".xar", 
    ".z")
# See https://totalcmd.net/plugring/total7zip.html
# XXX Total7zip creates a total7zip.xml file when initialized with the supported
#     extensions, etc, use it?
TOTAL7ZIP_EXTENSIONS = PACKER_7ZIP_EXTENSIONS + PACKER_7ZIP_EXTENSIONS_UNPACK_ONLY
PACKER_EXTENSIONS = (".iso",".bz2")  + TOTAL7ZIP_EXTENSIONS

EXTERNAL_VIEWER_FILEPATH = R"C:\Program Files\totalcmd\TOTALCMD%s.EXE" % ("" if platform_is_32bit() else "64")

EXTERNAL_DIFF_FILEPATH = R"C:\Program Files\KDiff3\kdiff3.exe"

# Size of the thumbnails stored in the model
IMAGE_WIDTH = 256
IMAGE_HEIGHT = 256

# Size of the images displayed on each item of the listview
DISPLAY_WIDTH = 128
DISPLAY_HEIGHT = 128

# XXX Make this dependent in images per viewport and memory consumed
MAX_CACHE_ENTRIES = 128
# Reduce the cache by this number of entries when the cache overflows
MAX_CACHE_ENTRIES_WATERMARK = 10

# Time in milliseconds to display the search string tooltip when typing
SEARCH_STRING_DISPLAY_TIME_MS = 2000

# Number of PixmapReader threads in charge of reading the image, decoding and
# scaling. On slow sources, this can cause stale reads to block newer ones when
# navigating the directory
READING_THREADS = 10
READING_THREADS = 1

# This prefix is used to access the network share directory, which also contains
# the WFX plugins.
# - it's a UNC-like path so it works with path.os. functions
# - It uses | as server since it's a protected character it doesn't collide with
#   real server names
# - It uses "Network" as UNC server name so
#   normpath("\\\\|\\Network\\webdav\..") is  "\\\\|\\Network\\webdav\", without
#   Network as server name, eg webdav would be considered as server name and
#   normpath .. would never remove it 
# This has the drawback that it needs an explicit command to change to this
# directory since the default change directory command requires the directory to
# be valid and can't enter this synthetic directory (note magic directories like
# Network on windows don't return a valid value from getExistingDirectory)
SHARE_ROOT = "\\\\*\\Network"

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
use_incremental_row_loading = False

# Set to force all listings to be single thread, this simplifies debugging
force_single_thread = False

# Force Everything listings single thread (Everything is actually single thread 
# and will actually block other processes until that query is done)
# XXX When this is False there's a race condition in Everything and
#     CTypesHelper that causes c.Everything_GetResultDateModified to to use the
#     wrong FILETIME pointer?
force_everything_single_thread = True

# Currently this must be set to true at least for sftpplug, otherwise listing
# will work but extract will fail with error 3 (FS_FILE_READERROR), since the
# first happens on a worker thread and the second on the UI thread. By setting
# to True everything happens on the UI thread.
#
# WFX plugins have flags for multithread (even if the calls are not made
# simultanously they are made from different threads), they may also be
# thread-affine (may expect to run from the thread that initialized it), set to
# True to call it serially from the UI thread 
#
# XXX In the future have a thread per WFX or for all WFX if necessary? 
#
force_wfx_single_thread = True

# XXX Is the above also the case for WCX?
force_wcx_single_thread = True

# Run ctypes parsing tests
do_parse_test = False

# Cached localsend information, defaults retrieved from the configuration
g_localsend_devices = []
g_localsend_myinfo = None

# These are read initialized to the constants and later read from the config
# file
g_external_viewer_filepath = EXTERNAL_VIEWER_FILEPATH
g_external_diff_filepath = EXTERNAL_DIFF_FILEPATH

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

g_shell32 = CTypesHelper("windows.h", "shell32.dll")
def qGetSystemIcon(filepath, default=None, small=True, fake_filename=True, is_dir = False, is_system=False, is_hidden=False, is_link=False):
    """
    - if filepath is empty, it will display the hard drive icon
    - filepath can be just an extension ".zip"if fake_filename is True
    """
    from PyQt5.QtWinExtras import QtWin

    c = g_shell32()
        
    shinfo = c.SHFILEINFOW()

    # Pretend the file exists using USEFILEATTRIBUTES
    result = c.SHGetFileInfoW(
        unicode(filepath),
        # XXX Not clear what combination, if any, makes red bang icon appear on
        #     readonly hidden system etc?
        c.FILE_ATTRIBUTE_NORMAL |
        (c.FILE_ATTRIBUTE_HIDDEN if is_hidden else 0) | 
        (c.FILE_ATTRIBUTE_SYSTEM if is_system else 0) | 
        (c.FILE_ATTRIBUTE_DIRECTORY if is_dir else 0) |
        # This doesn't force the linkoverlay, but SHGFI_LINKOVERLAY below does
        (c.FILE_ATTRIBUTE_REPARSE_POINT if is_link else 0)
        ,
        ctypes.byref(shinfo),
        ctypes.sizeof(shinfo),
        # SHGFI_ICON | SHGFI_LARGEICON | SHGFI_USEFILEATTRIBUTES
        (c.SHGFI_SMALLICON if small else c.SHGFI_LARGEICON) | c.SHGFI_ICON | 
        (c.SHGFI_USEFILEATTRIBUTES if fake_filename else 0) | 
        c.SHGFI_ADDOVERLAYS | (c.SHGFI_LINKOVERLAY if is_link else 0)
    )

    if (result == 0):
        return default

    return QIcon(QtWin.fromHICON(shinfo.hIcon))

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

def qGetExistingDirectory(parent, title, default_dir):
    """
    Popup a dialog box asking to choose an existing directory
    """
    dirpath = QFileDialog.getExistingDirectory(None, "Select Folder", os.getcwd())
    if (dirpath != ""):
        # getExistingDirectory returns forward slashes on win32, which later
        # confuses os.path.join mixing separators, and then the OS. Also don't
        # normalize the empty string, since it normalizes to "." but caller
        # needs to be able to tell between cancel and accept by checking for
        # empty string
        dirpath = os.path.normpath(dirpath)

    return dirpath

g_debounced_call_timers = {}
def qDebounceCall(fn, delay_ms):
    """
    Schedule a call to fn in delay_ms time. Extend the timeout by delay_ms if
    another call is made to debounce fn before the timeout expires.
    """
    def call_and_cleanup(fn):
        key = fn
        timer, debounced_calls = g_debounced_call_timers.pop(key)
        logger.info("Debouncing timer expired for %r debounced_calls %s", fn, debounced_calls)
        fn()
        
    key = fn
    
    timer, debounced_calls = g_debounced_call_timers.get(key, (None, 0))
    if (timer is None):
        logger.info("Debouncing timer not found for %s %r", key, fn)
        # First debounce call, set a timer
        timer = QTimer()
        timer.setSingleShot(True)
        timer.timeout.connect(lambda : call_and_cleanup(fn))
        timer.start(delay_ms)

        g_debounced_call_timers[key] = (timer, 0)

    else:
        assert None is logger.debug("Debouncing timer found for %s %r debounced_calls %d", key, fn, debounced_calls)
        # Second or later debounce the call, restart the timer
        g_debounced_call_timers[key] = (timer, debounced_calls + 1) 
        timer.start(delay_ms)

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
        # First rate limiting call:
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

    Some cases need casting because Python doesn't get the casted value because 
    the type can be extended, eg
    print EnumString(Qt, Qt.ItemDataRole(role))
    SizeHintRole
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

    QFrame.Shadow values:

    qBitNamesToStr(QFrame, QFrame.Plain, QFrame.Raised) ['Raised']

    qBitNamesToStr(QFrame, QFrame.Sunken, QFrame.Sunken) ['Plain', 'Raised']

    QFrame.Shape values:

    qBitNamesToStr(QFrame, QFrame.VLine, QFrame.VLine) ['Box', 'HLine']

    XXX but it won't work with the combined style. Make sample_value allow a
    list of values from both enums?

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
    QItemSelectionModel.Select) 
    Select 
    
    print BitmaskString(QItemSelectionModel, QItemSelectionModel.NoUpdate, 2)
    Select 
    
    print BitmaskString(QItemSelectionModel, QItemSelectionModel.NoUpdate, 3)
    Clear,Select

    print BitmaskString(QStyle, QStyle.State_None, QStyle.State_Raised)
    State_Raised 
    
    print BitmaskString(QStyle, QStyle.State_None, 2)
    State_Raised

    """
    def __init__(self, enum_type, sample_value, bits):
        self.enumType = enum_type
        self.sampleValue = sample_value
        self.bits = bits

    def __str__(self):
        return qBitNamesToStr(self.enumType, self.sampleValue, self.bits)


class FileInfoIterator(object):
    def getFileInfos(self, batch_size = 0):
        """
        - return FileInfos, return empty array if end of iteration and iterator
          is useless from then on
        - batch_size of 0 means return all fileinfos without batching

        XXX If the iterator is created in the UI thread, any thread-affine
            objects probably need to be created in getFileInfos with an init
            flag and not in __init__?
        """
        raise NotImplementedError
    
    def isDone(self):
        """
        This function has to be threadsafe, called from the UI thread, updated
        from the worker thread

        XXX Setting this from the worker thread and consuming directly in the UI
            thread is not good for possible future out of process
            implementations, would need to generate a signal so it's queue
            friendly or set it by the caller when it receives empty fileinfos or
            such.
        """
        raise NotImplementedError

    """
    XXX Have a createFile deleteFile createDirectory deleteDirectory or move that to
        a filesystem class since many fileinfos may share that? have a base class
        for those?
    """

class EverythingFileInfoIterator(FileInfoIterator):
    """
    This needs Everything64.dll from the freely available sdk at
    https://www.voidtools.com/Everything-SDK.zip 

    - See https://www.voidtools.com/support/everything/sdk/
    - See https://www.voidtools.com/support/everything/sdk/python/
    - See https://github.com/voidtools/everything_sdk3
    

    XXX The DLL is just a layer on top of the WM_COPYDATA IPC, so that could
        also be used directly without the need for the DLL?
        See https://github.com/doublecmd/doublecmd/blob/master/plugins/dsx/everything/src/everything.pas
        See https://github.com/voidtools/ES

    Another option is to use the command line interface
    """
    c = None
    def __init__(self, query, first_result = 0, max_results=50000, hwnd = None, sort_field = 2, sort_reverse=False, *args, **kwargs):
        # XXX Missing search order, is_regexp, etc
        logger.info("query %s first %d max %d hwnd %s sort_field %d sort_reverse=%s", 
            query, first_result, max_results, hwnd, sort_field, sort_reverse)
        
        self.query = query
        self.num_results = None
        self.tot_results = None
        self.curr_result = 0
        self.max_results = max_results
        self.done = False
        self.offset = 0
        self.sort_field = sort_field
        self.sort_reverse = sort_reverse
        
        # On XP 32-bit there's a warning when WinDLL cannot load a DLL, don't
        # load 64 bit and fallback to 32, check 32 bit explicitly
        if (platform_is_32bit()):
            everything_dll = ctypes.WinDLL(R"_out\Everything32.dll")

        else:
            everything_dll = ctypes.WinDLL(R"_out\Everything64.dll")
            
        self.everything_dll = everything_dll

        s_everything_h = open(os.path.join(INCLUDE_DIR, "Everything.h"), "r").read()
        # This uses 
        # EVERYTHINGUSERAPI DWORD EVERYTHINGAPI Everything_GetNumFileResults(void);
        # XXX These are #defines, support by looking at the constants?
        #       #define EVERYTHINGAPI __stdcall
        #       #define EVERYTHINGUSERAPI __declspec(dllimport)
        # Replacing EVERYTHINGUSERAPI below makes the define break, remove the
        # define too
        s_everything_h = s_everything_h.replace("#define EVERYTHINGUSERAPI __declspec(dllimport)", "")
        s_everything_h = s_everything_h.replace("EVERYTHINGUSERAPI", "")
        # XXX This tries to store __stdcall as field, find out why
        # s_everything_h = s_everything_h.replace("EVERYTHINGAPI", "__stdcall")
        s_everything_h = s_everything_h.replace("#define EVERYTHINGAPI __stdcall", "")
        s_everything_h = s_everything_h.replace("EVERYTHINGAPI", "")

        if (self.__class__.c is None):
            # Store in class variable, no need to parse and load per instance
            self.__class__.c = CTypesHelper(["windows.h", s_everything_h], everything_dll)
             
        self.c = self.__class__.c

    def setupQuery(self):
        c = self.c()

        #setup search
        hwnd = None
        # This seems to support the advanced search format, eg
        #  - ext:jpg;gif;webp
        #  - foo|bar
        #  - "exact phrase"
        #  - dupe:
        # See https://www.voidtools.com/support/everything/searching/
        # But needs 1.5 for filters/macros like
        # - pic:
        # - filter:document
        # Go to Organize Filters to see the expansion of that macro
        # eg ext:ani;bmp;gif;ico;jpe;jpeg;jpg;pcx;png;psd;tga;tif;tiff;webp;wmf
        # XXX Replace macros manually on < 1.5?
        # See https://www.voidtools.com/forum/viewtopic.php?t=12802
        c.Everything_SetSearchW(safe_unicode(self.query))
        c.Everything_SetMatchPath(True)
        c.Everything_SetMatchCase(False)
        c.Everything_SetRequestFlags(c.EVERYTHING_REQUEST_FILE_NAME | c.EVERYTHING_REQUEST_PATH | c.EVERYTHING_REQUEST_SIZE | c.EVERYTHING_REQUEST_DATE_MODIFIED | c.EVERYTHING_REQUEST_ATTRIBUTES)
        # FileInfo: Filename, size, mtime, attr
        # Model: Full filename, Filename, ext, size, date, attr
        everything_sort = 0
        if (self.sort_field == 0):
            everything_sort = c.EVERYTHING_SORT_NAME_ASCENDING

        elif (self.sort_field == 1):
            everything_sort = c.EVERYTHING_SORT_SIZE_ASCENDING

        elif (self.sort_field == 2):
            everything_sort = c.EVERYTHING_SORT_DATE_MODIFIED_ASCENDING

        elif (self.sort_field == 3):
            everything_sort = c.EVERYTHING_SORT_ATTRIBUTES_ASCENDING

        else:
            assert False, "Unknown sort field %d" % self.sort_field
        if (self.sort_reverse):
            everything_sort += 1

        logger.info("Setting everything sort %d", everything_sort)
        c.Everything_SetSort(everything_sort)

        # XXX Direct WM_COPYDATA not supported yet
        if (hwnd is not None):
            logger.info("Setting reply window 0x%x", hwnd)
            c.Everything_SetReplyWindow(hwnd)

    def isDone(self):
        return self.done

    def getFileInfos(self, batch_size = 0):
        logger.info("starting batch_size %d", batch_size)

        c = self.c()

        if (self.tot_results is None):
            # Setup the query, needs to be done in the worker thread because
            # Everything settings are thread-local
            self.setupQuery()
            # Requesting a high max or no max (thousands of files) causes stalls
            # when first querying because of all the data that needs to be
            # copied to this process from the everything process
            # XXX Updating the offset and max requires reissuing the query which
            #     may give inconsistent results on busy disks, eg if sorting
            #     recent first on a disk that is being updated, the files at
            #     offset N for the old query will be different than the ones at
            #     that offset, making successive offsets inonsistent with the
            #     old query. This is probably a known issue with offset and max?
            c.Everything_SetOffset(0)
            c.Everything_SetMax(batch_size * 10)
            # If doing background, old searches will be cancelled by issuing a new one
            hwnd = None
            # When hwnd is None, this will block until results are received
            res = c.Everything_QueryW(hwnd is None)
            if (not res):
                logger.error("Everything error %s", c.Everything_GetLastError())

            # Get the number of results
            # XXX Set the max with Everything_SetMax / _SetOffset to resume
            num_results = c.Everything_GetNumResults()
            tot_results = c.Everything_GetTotResults()

            self.tot_results = tot_results
            self.num_results = num_results
            self.curr_result = 0
            self.offset = 0

            logger.info("Result Count: %d of %d", num_results, tot_results)

        # XXX Needs long filename support, images fail to load
        
        filepath_buffer = ctypes.create_unicode_buffer(c.MAX_PATH)
        date_modified_filetime = c.FILETIME()
        file_size = c.LARGE_INTEGER()

        #logger.info("Setting offset %d max %s", self.offset, batch_size)
        #everything_dll.Everything_SetOffset(self.offset)
        #everything_dll.Everything_SetMax(self.offset + batch_size)
        #num_results = everything_dll.Everything_GetNumResults()
        #self.num_results = num_results
        #logger.info("Result Count after setting offset/max: %d of %d", self.num_results, self.tot_results)

        # XXX This could convert only part of the entries and delay the conversion
        #     until needed? (would break with match score sorting, though)
        file_infos = []
        dir_infos_set = set()
        # Can't batch if merging because the bath needs to be the full directory
        # XXX Think about this, ideally would like to have incremental loading
        #     of rows when everything is used?
        while ((self.curr_result-self.offset < self.num_results) and ((batch_size == 0) or (len(file_infos) < batch_size))):

            c.Everything_GetResultFullPathNameW(self.curr_result-self.offset, filepath_buffer, c.MAX_PATH)
            c.Everything_GetResultDateModified(self.curr_result-self.offset, date_modified_filetime)
            attribs = c.Everything_GetResultAttributes(self.curr_result - self.offset)
            c.Everything_GetResultSize(self.curr_result-self.offset, file_size)
            file_size_value = ((file_size.HighPart << 32) | file_size.LowPart)
            
            # XXX Missing other attributes
            is_dir = ((attribs & c.FILE_ATTRIBUTE_DIRECTORY) != 0)
            is_readonly = ((attribs  & c.FILE_ATTRIBUTE_READONLY) != 0)
            is_hidden = ((attribs & c.FILE_ATTRIBUTE_HIDDEN) != 0)
            is_link = ((attribs & c.FILE_ATTRIBUTE_REPARSE_POINT) != 0)
            filepath = ctypes.wstring_at(filepath_buffer)

            mtime = win32_filetime_to_timestamp(date_modified_filetime)
            file_info = FileInfo(filepath, file_size_value, mtime, fileinfo_build_attr(is_dir, is_hidden, not is_readonly, is_link))
            file_infos.append(file_info)

            # XXX This is currently not sorting directories before files, do the
            #     sorting or hook into everything sorting?
            if (is_dir):
                dir_infos_set.add(file_info)
                logger.info("Found dir %r, size 0x%x attribs 0x%x", filepath, file_size_value, attribs)
            else:
                logger.info("Found file %r, size 0x%d, attrib 0x%x", filepath, file_size_value, attribs)

            self.curr_result += 1
            
        logger.info("ending cur %d num %d of tot %d batch %s len %d", self.curr_result, self.num_results, self.tot_results, batch_size, len(file_infos))

        self.done = (len(file_infos) == 0)

        # self.offset = self.curr_result

        return dir_infos_set, file_infos

    def __del__(self):
        logger.info("")
        # Setting a new query already frees the query results, but this also
        # resets the search to the default 
        # if (self.everything_dll is not None):
        self.c().Everything_Reset()
        # XXX This completely releases the SDK resources, not clear it should be
        #     called, probably needs to unload the DLL too so the next load does
        #     load the DLL?
        # self.everything_dll.Everything_Cleanup()


class Win32FileInfoIterator(FileInfoIterator):
    """
    win32-optimized iterator, calling the api directly via ctypes, much faster
    than Python listdir and probably close to Qt but also completely
    non-blocking
    """
    c = CTypesHelper("windows.h", "kernel32.dll")

    def __init__(self, dirpath, recurse, *args, **kwargs):
        logger.info("%r %s", dirpath, recurse)
        
        self.c = self.__class__.c
        
        self.dirpath = dirpath
        self.recurse = recurse
        self.dirpath_stack = [""]
        self.current_dirpath = dirpath
        self.handle = WIN32_INVALID_HANDLE_VALUE
        
        self.done = False
        
    def getFileInfos(self, batch_size = 0):
        logger.info("starting batch_size %d", batch_size)

        c = self.c()

        dir_infos_set = set()
        file_infos = []

        find_data = c.WIN32_FIND_DATAW()

        # Stack is relative to self.dirpath
        dirpath_stack = self.dirpath_stack
        dirpath = self.current_dirpath
        handle = self.handle
        
        assert None is logger.debug("Reading next entries")
        while (True):
            if (handle == WIN32_INVALID_HANDLE_VALUE):
                if (len(dirpath_stack) == 0):
                    break
                # Start the search
                dirpath = dirpath_stack.pop()
                # Add wildcard, required by FindFirstFile
                abs_dirpath = os.path.join(self.dirpath, dirpath, "*")
                assert None is logger.debug("Reading first entry for %r %r %r", dirpath, self.dirpath, abs_dirpath)
                handle = c.FindFirstFileW(abs_dirpath, ctypes.byref(find_data))
                
                if (handle == WIN32_INVALID_HANDLE_VALUE):
                    logger.warn("Unable to open directory or invalid path %r %r %r" % (dirpath, self.dirpath, abs_dirpath))
                    continue
            else:
                # Resume previous Find
                fileinfo_ready = c.FindNextFileW(handle, ctypes.byref(find_data))
                if (not fileinfo_ready):
                    assert None is logger.debug("Closing handle 0x%x", handle)
                    c.FindClose(handle)
                    handle = WIN32_INVALID_HANDLE_VALUE
                    continue

            # Fetch the filename
            filename = find_data.cFileName

            # FindFirst returns both "." and "..", ignore "."
            if (filename == "."):
                continue

            is_dotdot = (filename == "..")
            filename = os.path.join(dirpath, filename)
            
            is_dir = ((find_data.dwFileAttributes & c.FILE_ATTRIBUTE_DIRECTORY) != 0)
            is_readonly = ((find_data.dwFileAttributes & c.FILE_ATTRIBUTE_READONLY) != 0)
            is_hidden = ((find_data.dwFileAttributes & c.FILE_ATTRIBUTE_HIDDEN) != 0)
            is_link = ((find_data.dwFileAttributes & c.FILE_ATTRIBUTE_REPARSE_POINT) != 0)
            
            last_write_time = win32_filetime_to_timestamp(find_data.ftLastWriteTime)

            file_info = FileInfo(
                filename, 
                # Symlinks return the size of the target, not the symlink
                # file, use os.path instead. There's a way to get the size
                # of the .lnk file, but it's involved having to read the
                # file, etc
                # https://stackoverflow.com/questions/53411886/qfileinfo-size-is-returning-shortcut-target-size
                (find_data.nFileSizeHigh << 32) | find_data.nFileSizeLow, 
                # XXX Check if this is also returning the wrong date for .lnk files
                # XXX Find out if this is UTC, fix UTC elsewhere
                last_write_time,
                fileinfo_build_attr(is_dir, is_hidden, not is_readonly, is_link)
            )

            if (is_dir):
                dir_infos_set.add(file_info)
                if (self.recurse and (not is_dotdot)):
                    dirpath_stack.append(filename)

            else:
                file_infos.append(file_info)
        
            # Finish when done with this batch, other parts above finish when
            # done with this directory and the directory stack
            if ((batch_size > 0) and ((len(file_infos) + len(dir_infos_set)) > batch_size)):
                break
        
        # Update the resume values in case any was modified in the loop (no need
        # to update dirpath_stack since it's a reference to self.dirpath_stack)
        self.handle = handle
        # This is modified when recursing, save
        self.current_dirpath = dirpath

        file_infos = list(dir_infos_set) + file_infos 

        self.done = (len(file_infos) == 0)

        return dir_infos_set, file_infos

    def isDone(self):
        return self.done

    def __del__(self):
        if (self.handle != WIN32_INVALID_HANDLE_VALUE):
            self.c().FindClose(self.handle)

# WFX plugins are initialized as loaded calling FsINit, this stores any required
# initialization state that needs to be retrieved when making WFX API calls
g_fs_init_states = {} 

class WFXFileInfoIterator(FileInfoIterator):
    """
    Total Commander filesystem plugin WFX iterator.

    https://github.com/ghisler/WFX-SDK
    https://ghisler.github.io/WFX-SDK/contents.htm

    The iteration functions work with sftpplug.wcx64 and davplug.wcx64, crash
    with Double Commander ftp.wfx

    There are several pitfalls supporting WFX:
    - Callbacks can be called without checking if they had been provided and
      crash (eg initializing the plugin via FsInitW but callback being used is
      the one for FsInit)
    - Need to call both FsInitW and FsInit (see above)
    - Callbacks can be garbage collected by Python causing crashes, needs to
      keep a reference to them
    - Plugins using a mix of widechar and ansi functions (eg StatusInfo, FsInit)
    - Plugins would crash if the wrong path was passed in (empty string, etc)
    - Plugin crash if FsSetDefaultParams wasn't implemented (missing ini
      filepath?)


    ftp.wfx sftp plugin

    https://github.com/doublecmd/doublecmd/tree/master/plugins/wfx/ftp
    https://github.com/j2969719/doublecmd-plugins/tree/master/plugins/wfx

    https://github.com/doublecmd/doublecmd/wiki/Plugins
    https://github.com/doublecmd/doublecmd/wiki/Plugins-development
    https://github.com/doublecmd/doublecmd/blob/master/sdk/extension.h

    https://github.com/j2969719/doublecmd-plugins/blob/master/plugins/sdk/extension.md

    This comes from double commander, it's possible it's incompatible since it
    has an extra export ExtensionInitialize. Right now this lists the default
    entries (<Add connection>, <Quick connection>) but crashes with null access
    violation when ExecuteFileW of the "<Add connection>" entry:

    2025-09-30 16:25:55,243 INFO:twin.py(2034):[54088]
    WFXFileInfoIterator.executeFile: ExecuteFileW hwnd 16f0ab8 remote u'\\<Add
    connection>' verb open <type 'exceptions.WindowsError'>,
    WindowsError('exception: access violation writing 0x0000000000000000',),
    <traceback object at 0x00000000064DBD08>)


    sftpplug.wfx64 sftp plugin

    https://www.ghisler.ch/board/viewtopic.php?f=6&t=19994
    https://www.totalcommander.ch/beta/sftpplug310b9.zip
    https://www.totalcommander.ch/beta/sftpplug_src310b9.zip

    XXX The implemented functionality works (saving connections, connecing and
        listing remotes,etc), missing deleting files, copying, etc


    davplug.wfx64 webdav plugin

    https://plugins.ghisler.com/fsplugins/webdav.zip
    https://plugins.ghisler.com/fsplugins/webdav_src.zip

    XXX The implemented functionality works, missing deleting files, copying,
        etc
    """
    def __init__(self, rootpath, dllpath, dirpath, recurse, plugin_id, *args, **kwargs):
        self.dllpath = dllpath
        
        # XXX this should default to FsGetDefRootName
        #     void __stdcall FsGetDefRootName(char* DefRootName,int maxlen);
        self.rootpath = rootpath
        
        self.dirpath = dirpath
        # The root contains configuration options, recursing triggers the dialog
        # boxes, etc, don't recurse
        self.recurse = recurse and (dirpath != "\\")
        self.dirpath_stack = [""]
        self.current_dirpath = dirpath
        self.plugin_id = plugin_id
        
        self.done = False
        self.c = None

    def getFileInfos(self, batch_size):
        assert None is logger.debug("starting batch_size %d", batch_size)
    
        dir_infos_set = set()
        file_infos = []

        if (self.c is None):
            logger.info("Initializing")
            plugin_id = self.plugin_id
            dllpath = self.dllpath
            dirpath = self.dirpath
            
            if (plugin_id in g_fs_init_states):
                logger.info("Reusing c %r from global state for plugin_id %d", dllpath, plugin_id)
                self.c = g_fs_init_states[plugin_id].c
            
            else:
                logger.info("Loading c %r for plugin_id %d", dllpath, plugin_id)
                self.c = CTypesHelper(["windows.h", "fsplugin.h"], dllpath)
                
                c = self.c()

                # MAX_PATH is 1024 when a plugin implements FindFirstW (this is not true
                # in win32 structs).
                # See https://ghisler.github.io/WFX-SDK/unicode_support.htm
                # See #define wdirtypemax 1024 in 
                # See https://learn.microsoft.com/en-us/windows/win32/fileio/naming-a-file
                MAX_WPATH = 1024

                def empty_progress_proc(PluginNr, SourceName, TargetName, PercentDone):
                    # XXX Hook into progress report/abort dialog,
                    logger.info("%d %s %s %d", PluginNr, SourceName, TargetName, PercentDone)
                    # 1 Abort, 0 Continue
                    return 0

                def empty_log_proc(PluginNr, MsgType, LogString):
                    logger.info("PluginNr %d MsgType %d LogString %r", PluginNr, MsgType, LogString)

                def empty_request_proc(PluginNr, RequestType, CustomTitle, CustomText, ReturnedText, maxlen):
                    # XXX Hook into remote machine fingerprint approval request dialog
                    logger.info("PluginNR %d, RequestType %d, CustomTitle %r, CustomText %r, ReturnedText %r, maxlen %d", 
                        PluginNr, RequestType, CustomTitle, CustomText, ReturnedText, maxlen)
                    # You could optionally fill ReturnedText here
                    # ReturnedText[:maxlen] = "dummy response"
                    # True OK, False Cancel
                    return 1

                # int __stdcall CryptProc(int PluginNr, int CryptoNumber, int mode, char* ConnectionName, char* Password, int maxlen);
                def empty_crypt_proc(PluginNr, CryptoNumber, mode, ConnectionName, Password, maxlen):
                    logger.info("PluginNr %d CryptoNumber %d mode %d ConnectionName %s Password %s maxlen %d", 
                        PluginNr, CryptoNumber, mode, ConnectionName, Password, maxlen)
                    return c.FS_FILE_NOTFOUND
                
                logger.info("Calling FsInit for plugin_id %r", plugin_id)
                    
                # Keep a reference to ctype callback wrappers to avoid crashes
                # due to garbage collection
                procs = []
                
                # Need to initialize both the ansi and widechar procs because even
                # if all plugins are widechar, some report using the ansi procs
                # (sftpplug). Not doing so causes null pointer accesses when
                # starting the connection because of uninitialized ProgressProc
                # being called
                if (hasattr(c, "FsInit")):
                    logger.info("FsInit")
                    ps = [c.tProgressProc(empty_progress_proc), c.tLogProc(empty_log_proc), c.tRequestProc(empty_request_proc)]
                    res = c.FsInit(plugin_id, *ps)
                    procs.extend(ps)

                ps = [c.tProgressProcW(empty_progress_proc), c.tLogProcW(empty_log_proc), c.tRequestProcW(empty_request_proc)]
                logger.info("FsInitW")
                res = c.FsInitW(plugin_id, *ps)
                procs.extend(ps)

                # XXX Returns 0 when successful, check it
                if (hasattr(c, "FsSetDefaultParams")):
                    logger.info("Calling FsSetDefaultParams")
                    default_params = c.FsDefaultParamStruct()
                    default_params.size = ctypes.sizeof(c.FsDefaultParamStruct)
                    default_params.PluginInterfaceVersionLow = 0
                    default_params.PluginInterfaceVersionHigh = 2
                    # sftp ignores the ini name and only uses the directory,
                    # where it stores sftpplug.ini, similarly davplug
                    default_params.DefaultIniName = R"_out\twin.ini"

                    c.FsSetDefaultParams(default_params)

                do_doublecommander = False
                if (do_doublecommander):
                    # XXX Double commander WFX plugins don't currently work, eg
                    #     ftp requires a lot of plumbing for configuration
                    #     dialog procs, etc

                    # For double commander, first FsInit, then FsSetDefaultParams,
                    # then ExtensionInitialize
                    # See https://github.com/doublecmd/doublecmd/blob/master/src/uwfxmodule.pas#L865

                    if (hasattr(c, "ExtensionInitialize")):
                        logger.info("Calling ExtensionInitialize")
                        
                        # typedef int (DCPCALL *tMessageBoxProc)(char* Text, char* Caption, long Flags);
                        def message_box(text, caption, flags):
                            logger.info("%r %r 0x%x", text, caption, flags)
                            return 0

                        # typedef intptr_t (DCPCALL *tDlgProc)(uintptr_t pDlg, char* DlgItemName, intptr_t Msg, intptr_t wParam, intptr_t lParam);
                        def dialog(pDlg, DlgItemName, Msg, wParam, lParam):
                            logger.info("pDlg %r DlgItemName %r Msg %r wParam %r lParam %r", pDlg, DlgItemName, Msg, wParam, lParam)
                            return 0

                        startup_info = c.tExtensionStartupInfo()
                        startup_info.PluginConfDir = "_out\\"
                        
                        msgbox_proc = c.tMessageBoxProc(message_box)
                        startup_info.MessageBox = msgbox_proc
                        procs.append(msgbox_proc)

                        dlg_proc = c.tDlgProc(dialog)
                        startup_info.DlgProc = dlg_proc
                        procs.append(dlg_proc)

                        c.ExtensionInitialize(startup_info)

                if (hasattr(c, "FsSetCryptCallbackW")):
                    logger.info("Calling SetCryptCallbackW")
                    crypt_proc = c.tCryptProcW(empty_crypt_proc)
                    c.FsSetCryptCallbackW(crypt_proc, 0, 0)
                    procs.append(crypt_proc)
                    
                elif (hasattr(c, "FsSetCryptCallback")):
                    logger.info("Calling SetCryptCallback")
                    # sftpplug has SetCryptCallback but no SetCryptCallbackW
                    crypt_proc = c.tCryptProc(empty_crypt_proc)
                    c.FsSetCryptCallback(crypt_proc, 0, 0)
                    procs.append(crypt_proc)

                # Store in global state for reusing
                g_fs_init_states[plugin_id] = WFXState(procs, self.c)

            dir_infos_set = set([FileInfo("..", 0, 0, fileinfo_build_attr(True, False, True, False))])
            self.handle = WIN32_INVALID_HANDLE_VALUE

        c = self.c()

        # Stack is relative to self.dirpath
        dirpath_stack = self.dirpath_stack
        dirpath = self.current_dirpath
        handle = self.handle

        FsStatusInfo =  c.FsStatusInfo if (hasattr(c, "FsStatusInfo")) else c.FsStatusInfoW

        find_data = c.WIN32_FIND_DATAW()
        
        while (True):
            if (handle == WIN32_INVALID_HANDLE_VALUE):
                if (len(dirpath_stack) == 0):
                    break
                # Start the search
                dirpath = dirpath_stack.pop()
                abs_dirpath = os.path.join(self.dirpath, dirpath)
                logger.info("StatusInfo start list %r", abs_dirpath)
                FsStatusInfo(abs_dirpath, c.FS_STATUS_START, c.FS_STATUS_OP_LIST)
                
                assert None is logger.info("Reading first entry for self.dirpath %r dirpath %r abs_dirpath %r", self.dirpath, dirpath, abs_dirpath)
                handle = c.FsFindFirstW(abs_dirpath, ctypes.byref(find_data))
                
                if (handle == WIN32_INVALID_HANDLE_VALUE):
                    logger.warn("Unable to open directory or invalid path self.dirpath %r dirpath %r abs_dirpath %r" % (self.dirpath, dirpath, abs_dirpath))
                    win32_get_last_error()
                    continue
                
            else:
                # Resume previous Find
                fileinfo_ready = c.FsFindNextW(handle, ctypes.byref(find_data))
                if (not fileinfo_ready):
                    assert None is logger.info("Closing handle 0x%x", handle)
                    c.FsFindClose(handle)
                    handle = WIN32_INVALID_HANDLE_VALUE
                    logger.info("StatusInfo end list %r", dirpath)
                    FsStatusInfo(dirpath, c.FS_STATUS_END, c.FS_STATUS_OP_LIST)
                    continue

            assert None is logger.info("Got entry %r attr 0x%x res0 0x%x res1 0x%x", find_data.cFileName, find_data.dwFileAttributes, find_data.dwReserved0, find_data.dwReserved1)

            # Fetch the filename
            filename = find_data.cFileName

            # Not all WFX have dotdot (eg webdav), so it's added above
            # unconditionally, ignore it here
            if (filename in [".", ".."]):
                continue

            is_dotdot = (filename == "..")
            if (dirpath != "\\"):
                filename = os.path.join(dirpath, filename)

            is_dir = ((find_data.dwFileAttributes & c.FILE_ATTRIBUTE_DIRECTORY) != 0)
            # When UNIX_MODE is set, dwReserved0 has the Unix attributes
            # See https://ghisler.github.io/WFX-SDK/fsfindfirst.htm
            is_link = (stat.S_ISLNK(stat.S_IFMT(find_data.dwReserved0)) if ((find_data.dwFileAttributes & c.FILE_ATTRIBUTE_UNIX_MODE) != 0) else False)
            is_readonly = ((find_data.dwFileAttributes & c.FILE_ATTRIBUTE_READONLY) != 0)
            is_hidden = ((find_data.dwFileAttributes & c.FILE_ATTRIBUTE_HIDDEN) != 0)

            mtime = win32_filetime_to_timestamp(find_data.ftLastWriteTime)
            
            # XXX In sftp, Quick connection appears as link, f7 to create a new
            #     connection, stored connection appear as link, alt enter to
            #     edit the connection

            file_info = FileInfo(
                filename, 
                find_data.nFileSizeHigh * 2**32 + find_data.nFileSizeLow, 
                # XXX Find out if this is UTC, fix UTC elsewhere
                mtime,
                fileinfo_build_attr(is_dir, is_hidden, not is_readonly, is_link)
            )

            # XXX Have an option to recurse links?
            if (is_dir):
                dir_infos_set.add(file_info)
                if (self.recurse and (not is_dotdot)):
                    dirpath_stack.append(filename)

            else:
                file_infos.append(file_info)
        
            # Finish when done with this batch, other parts above finish when
            # done with this directory and the directory stack
            if ((batch_size > 0) and ((len(file_infos) + len(dir_infos_set)) > batch_size)):
                break
        
        file_infos = list(dir_infos_set) + file_infos 

        # Update the resume values in case any was modified in the loop (no need
        # to update dirpath_stack since it's a reference to self.dirpath_stack)
        self.handle = handle
        # This is modified when recursing, save
        self.current_dirpath = dirpath
        
        self.done = (len(file_infos) == 0)

        return dir_infos_set, file_infos

    def mkDir(self, path):
        # Remove root
        relpath = path[len(self.rootpath):]
        logger.info("path %r relpath %r", path, relpath)
        # XXX Missing StatusInfo?
        res = self.c().FsMkDirW(relpath)
        logger.info("returns %d", res)

    def executeFile(self, hwnd, path, verb):
        # Remove root
        relpath = path[len(self.rootpath):]
        logger.info("hwnd %x path %r relpath %r verb %s", hwnd, path, relpath, verb)

        c = self.c()

        if (hasattr(c, "FsStatusInfo")):
            FsStatusInfo =  c.FsStatusInfo
        else:
            FsStatusInfo =  c.FsStatusInfoW

        # XXX Make this a context so it auto sends fs_status_end?
        logger.info("StatusInfo start exec %r", relpath)
        FsStatusInfo(relpath, c.FS_STATUS_START, c.FS_STATUS_OP_EXEC)

        # Plugin can write to RemoteName, make sure there's room for 1024 WCHAR
        # as per the Unicode notes at
        # https://ghisler.github.io/WFX-SDK/unicode_support.htm
        MAX_PATH_EX = 1024 
        remote_name_c = ctypes.create_unicode_buffer(relpath, MAX_PATH_EX)
        logger.info("ExecuteFileW hwnd %x remote %r verb %s", hwnd, remote_name_c.value, verb)
        res = c.FsExecuteFileW(ctypes.c_void_p(hwnd), remote_name_c, verb)
        logger.info("ExecuteFileW returns %d remote %r", res, remote_name_c.value)
        
        logger.info("StatusInfo end exec %r",relpath)
        FsStatusInfo(relpath, c.FS_STATUS_END, c.FS_STATUS_OP_EXEC)
        
        return res

    def extract(self, filepath):
        # XXX This is called in the UI thread, which may not be the wfx thread.
        #     Probably needs to schedule in the wfx thread, which also allows
        #     cancellable/background

        # XXX This preamble is common between zip and wcx, probably others, find
        #     a way to refactor to the caller, but it needs the arcpath,
        #     which createIterator already calculates, store it there?
        arcpath = self.rootpath
        relpath = filepath[len(arcpath)+1:]
        # Entries in WCX use backward slashes with no starting forward slash
        entrypath = relpath
        temp_subdir = "%x" % (hash(arcpath) + (sys.maxint - 1))
        temp_relpath = os.path.join(temp_subdir, relpath)
        temp_dir = os.path.join(TEMP_DIR, temp_subdir)

        filepath = os.path.join(temp_dir, relpath)
        filepath = os.path.abspath(filepath)
        dirpath = os.path.dirname(filepath)
        
        os_makedirs(dirpath)

        c = self.c()

        remote_info = c.RemoteInfoStruct()
        # XXX Missing setting flags
        res = c.FsGetFileW(entrypath, filepath, 0, remote_info)

        # XXX There are many other result codes for resuming, ovewriting etc,
        #     implement
        if (res != c.FS_FILE_OK):
            filepath = None

        return filepath

    def isDone(self):
        return self.done

    def __del__(self):
        logger.info("")
        if (self.handle != WIN32_INVALID_HANDLE_VALUE):
            self.c().FindClose(self.handle)


class WCXFileInfoIterator(FileInfoIterator):
    """
    Total commander WCX packer plugin iterator.

    Tested with total7zip.wcx64, iso.wcx64, bzip2dll.wcx64

    See https://ghisler.github.io/WCX-SDK/table_of_contents.htm
    see https://github.com/ghisler/WCX-SDK

    XXX Missing support for packing, unpacking
    """
    def __init__(self, dllpath, arcpath, dirpath, recurse, *args, **kwargs):
        logger.info("dllpath %r arcpath %r dirpath %r recurse %s", dllpath, arcpath, dirpath, recurse)
        if (not dirpath.endswith("\\")):
            dirpath += "\\"
        
        self.dllpath = dllpath
        self.arcpath = arcpath
        self.dirpath = dirpath
        self.recurse = recurse
        self.done = False

        self.c = None
        
    def getFileInfos(self, batch_size = 0):
        file_infos = []
        dir_infos_set = set()

        if (self.c is None):
            # XXX keep a global WCXState so WCX plugins are not reloaded multiple
            #     times?
            self.c = CTypesHelper(["windows.h", "wcxhead.h"], self.dllpath)
            c = self.c()

            d = {}
            # Not all packers have all the ReadHeader functions:
            # - If ReaderHeaderExW exists, use that one, in this case ReadHeaderW may not exist
            # - otherwise use ReaderHeaderW
            # Eg total7zip and bzip2dll have ReadHeader and ReadHeaderExW but no ReadHeaderW
            # See https://ghisler.github.io/WCX-SDK/readheaderex.htm
            if (hasattr(c, "ReadHeaderExW")):
                d["ReadHeaderXX"] = c.ReadHeaderExW
                d["tHeaderDataXX"] = c.tHeaderDataExW
            else:
                d["ReadHeaderXX"] = c.ReadHeaderW
                d["tHeaderDataXX"] = c.ReadHeaderW
            
            # https://ghisler.github.io/WCX-SDK/setprocessdataproc.htm
            # void __stdcall SetProcessDataProc (HANDLE hArcData, tProcessDataProc pProcessDataProc);
            # typedef int (__stdcall *tProcessDataProc)(char *FileName, int Size);
            # iso.wcx64 has SetProcessDataProc but not SetProcessDataProcW even if it supports ReadHeaderExW
            if (hasattr(c, "SetProcessDataProcW")):
                d["SetProcessDataProcXX"] = c.SetProcessDataProcW
                d["tProcessDataProcXX"] = c.tProcessDataProcW
                
            else:
                d["SetProcessDataProcXX"] = c.SetProcessDataProc
                d["tProcessDataProcXX"] = c.tProcessDataProc

            c = self.c.update(d)
            
            # Path to archive to open
            archive_path = self.arcpath  # Replace with your test archive file
            #archive_path_c = ctypes.create_string_buffer(archive_path)

            # Prepare OpenArchiveData
            open_data = c.tOpenArchiveDataW()
            open_data.ArcName = archive_path
            open_data.OpenMode = c.PK_OM_LIST
            open_data.CmtBuf = None
            open_data.CmtBufSize = 0

            # Open archive
            open_data_ptr = ctypes.pointer(open_data)
            handle = c.OpenArchiveW(open_data_ptr)
            
            if (not handle):
                raise Exception("Failed to open archive.")
            self.handle = handle

            dir_infos_set = set([FileInfo("..", 0, 0, fileinfo_build_attr(True, False, True, False))])

        c = self.c()
        header = c.tHeaderDataXX()
        
        # Some wcx files wrap around once res returns E_END_ARCHIVE, skip afer
        # the first listing 
        while (not self.done):
            res = c.ReadHeaderExW(self.handle, ctypes.byref(header))
            assert None is logger.debug("ReadHeaderExW returned %d", res)
            if (res != c.PK_OK):
                self.done = True
                break
            
            # https://ghisler.github.io/WCX-SDK/topenarchivedata.htm says
            # ProcessFileW(PK_SKIP) is not necessary when listing, but at least
            # total7zip with rar files won't advance the record if not called
            # (the bz2 plugin does advance the record without calling
            # ProcessFileW)
            res = c.ProcessFileW(self.handle, c.PK_SKIP, None, None)
            assert None is logger.debug("ProcessFile returned %d", res)
            if (res != c.PK_OK):
                self.done = True
                break

            filename = "\\" + header.FileName
            # XXX filename can be "" in single-item archives (eg bz2), fix so at
            #     least displays the filename?
            assert None is logger.debug("File in archive: %r", filename)
            if (filename.startswith(self.dirpath) and (
                    # Recursing or strictly inside self.dirpath
                    self.recurse or 
                    ("\\" not in filename[len(self.dirpath):])
                )):
                relpath = filename[len(self.dirpath):]

                mtime = 0
                # Some .iso files have 0 as date (eg boot.images dir from Linux
                # images) which make datetime.datetime raise, ignore
                if (header.FileTime != 0):
                    # FileTime = (year - 1980) << 25 | month << 21 | day << 16 | hour << 11 | minute << 5 | second/2;
                    mtime = datetime.datetime(
                        (header.FileTime >> 25) + 1980, 
                        (header.FileTime >> 21) & 0xF, 
                        (header.FileTime >> 16) & 0x1F, 
                        (header.FileTime >> 11) & 0x1F, 
                        (header.FileTime >> 5) & 0x1F, 
                        (header.FileTime & 0x1F) * 2
                    )
                    
                    mtime = datetime_to_utctimestamp(mtime)
                # See https://ghisler.github.io/WCX-SDK/theaderdata.htm
                is_dir = ((header.FileAttr & 0x10) != 0)
                attr = fileinfo_build_attr(is_dir, (header.FileAttr & 0x2) != 0, (header.FileAttr & 0x1) != 0, False)
                
                file_info = FileInfo(relpath, header.UnpSize, mtime, attr)

                if (is_dir):
                    dir_infos_set.add(file_info)
                    
                else:
                    file_infos.append(file_info)

                if ((batch_size > 0) and (len(file_infos) + len(dir_infos_set)) > batch_size):
                    break

        file_infos = list(dir_infos_set) + file_infos 

        self.done = (self.done or (len(file_infos) == 0))

        return dir_infos_set, file_infos

    def extract(self, filepath):
        # XXX This preamble is common between zip and wcx, probably others, find
        #     a way to refactor to the caller, but it needs the arcpath,
        #     which createIterator already calculates, store it there?
        relpath = filepath[len(self.arcpath)+1:]
        # Entries in WCX use backward slashes with no starting forward slash
        entrypath = relpath
        temp_subdir = "%x" % (hash(self.arcpath) + (sys.maxint - 1))
        temp_relpath = os.path.join(temp_subdir, relpath)
        temp_dir = os.path.join(TEMP_DIR, temp_subdir)

        c = self.c()
        
        # Open the archive
        open_data = c.tOpenArchiveDataW()
        open_data.ArcName = self.arcpath
        open_data.OpenMode = c.PK_OM_EXTRACT
        open_data.CmtBuf = None
        open_data.CmtBufSize = 0
        open_data_ptr = ctypes.pointer(open_data)
        handle = c.OpenArchiveW(open_data_ptr)
        
        if (not handle):
            raise Exception("Failed to open archive.")

        def process_data(filename, size):
            """
            Size can be:
            - >0 bytes processed since the previous call
            - -1..-100 for the first progress bar
            - -1000..-1100 for the second progress bar

            Return 0 to abort, 1 to continue

            See https://ghisler.github.io/WCX-SDK/tprocessdataproc.htm
            """
            # XXX Actually do something with this, extract() should run in a
            #     thread and send signals to the caller, with the thread abort
            #     that connects to that process_data callback
            logger.info("%r %d", filename, size)
            # Return 0 to abort
            return 1

        # Store in a variable to prevent crashes because of being garbage
        # collected
        fn = c.tProcessDataProcXX(process_data)
        c.SetProcessDataProcXX(handle, fn)
        
        header = c.tHeaderDataXX()

        while (True):
            res = c.ReadHeaderXX(handle, ctypes.byref(header))
            assert None is logger.debug("ReadHeaderXX returned %d", res)
            if (res != c.PK_OK):
                break

            assert None is logger.debug("Found file header %r", header.FileName)
            filename = header.FileName
            
            assert None is logger.debug("Got %r need %r", filename, entrypath)
            if (filename == entrypath):
                logger.info("Found entrypath %r", entrypath)
                break

            else:
                res = c.ProcessFileW(handle, c.PK_SKIP, None, None)
            assert None is logger.debug("ProcessFile returned %d", res)
            if (res != c.PK_OK):
                break

        if (res == c.PK_OK):
            filepath = os.path.join(temp_dir, relpath)
            filepath = os.path.abspath(filepath)
            dirpath = os.path.dirname(filepath)
            
            os_makedirs(dirpath)

            # Calling with null destpath, so destname contains full path
            res = c.ProcessFileW(handle, c.PK_EXTRACT, None, filepath)
            logger.info("ProcessFileW returned %d", res)
        
        if (res != c.PK_OK):
            filepath = None

        c.CloseArchive(handle)
        
        return filepath

    def isDone(self):
        return self.done

    def __del__(self):
        # Close archive
        self.c().CloseArchive(self.handle)


class QtFileInfoIterator(FileInfoIterator):
    """
    Qt API iterator, much faster than Python listdir, but blocks the UI.

    XXX ctypes is supposed to release the GIL, try calling this with ctypes in a
        platform agnostic way? Since ctypes is C only looks like this needs a
        C++ to C bridge. OTOH since QDirIterator is in Qt5Core.dll, constructor,
        destructor and member functions are exported separately and there may be
        a way to create the instance and call the methods either via the vtable
        or proper ctypes parameter definition.
    """
    def __init__(self, dirpath, recurse, *args, **kwargs):
        self.it = None
        self.dirpath = dirpath
        self.recurse = recurse

    def getFileInfos(self, batch_size=0):
        if (self.it is None):
            # Use positional arguments to QDirIterator since keyword arguments
            # seem to fail with "unknown keyword argument"?
            self.it = QDirIterator(
                unicode(self.dirpath), 
                [("*%s" % ext) for ext in IMAGE_EXTENSIONS] if (len(FILTERED_EXTENSIONS) > 0) else ["*"], 
                QDir.Files | QDir.AllDirs | QDir.NoDot | QDir.Hidden | QDir.System, 
                QDirIterator.Subdirectories if self.recurse else QDirIterator.NoIteratorFlags)

        it = self.it

        dir_infos_set = set()
        file_infos = []
        last_sleep_time = time.time()
        logger.info("Reading dir")
        while (it.hasNext()):
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
                fileinfo_build_attr(is_dir, it.fileInfo().isHidden(), it.fileInfo().isWritable(), it.fileInfo().isSymbolicLink())
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
            if ((not it.hasNext()) or ((batch_size > 0) and (len(file_infos) + len(dir_infos_set)) > batch_size)):
                break

        file_infos = list(dir_infos_set) + file_infos 
        self.done = (len(file_infos) == 0)
               
        return dir_infos_set, file_infos

    def isDone(self):
        return self.done

    def __del__(self):
        logger.info("")
        pass

class ListdirFileInfoIterator(FileInfoIterator):
    """
    Python native iterator using os.listdir. Non-UI blocking, but slow and
    getting the file list is not-interruptible (getting the file attributes is)
    """
    def __init__(self, dirpath, recurse, *args, **kwargs):
        self.dirpath = dirpath
        self.recurse = recurse
        self.filenames = None

    def getFileInfos(self, batch_size=0):
        assert not self.recurse, "Recursion not supported yet on the listdir path"
        
        file_infos = []
        dir_infos_set = set()
        
        # listdir takes ~34s. and processing another ~30s on slow drives. UI
        # is very responsive, none of the two seem to take. This was on a
        # directory with lots of images and 2 subdirs, but also lots of mp4,
        # which explains the slowness in processing (isdir path being hit),
        # once .mp4 are added to the extensions, the processing time is
        # negligible.
        l = self.filenames
        if (l is None):
            logger.info("listdiring")
            # Force unicode on listdir parameter so results are unicode too
            l = os.listdir(unicode(self.dirpath))
            self.filenames = l
            dir_infos_set = set([FileInfo("..", 0, 0, fileinfo_build_attr(True, False, True, False))] if (os.path.dirname(self.dirpath) != self.dirpath) else [])
        
        logger.info("processing")
        # XXX Sort first and emit later in batches at processing time? But
        #     cannot be done until directories are known, which is at
        #     processing time anyway. Sort after the fact?

        while (len(l) > 0):
            filename = l.pop()
            filepath = os.path.join(self.dirpath, filename)
            # XXX os.stat/os.path.isdir can be slow on network drives
            st = os.stat(filepath)
            #is_dir = os.path.isdir(filepath)
            is_dir = stat.S_ISDIR(st.st_mode)
            is_link = stat.S_ISLNK(st.st_mode)
            #size = 0
            size = st.st_size
            #mtime = 0
            mtime =  st.st_mtime
            file_info = FileInfo(filename, size, mtime, fileinfo_build_attr(is_dir, False, True, is_link))
            if (is_dir):
                dir_infos_set.add(file_info)

            elif ((len(FILTERED_EXTENSIONS) == 0) or filename.lower().endswith(FILTERED_EXTENSIONS)):
                file_infos.append(file_info)

            else:
                logger.info("Ignoring filtered out file %r", filename)

            if (((batch_size > 0) and ((len(dir_infos_set) + len(file_infos)) >= batch_size)) or (len(l) == 0)):
                break

        file_infos = list(dir_infos_set) + file_infos 
        
        return dir_infos_set, file_infos

class ZipFileInfoIterator(FileInfoIterator):
    """
    Iterator using Python native zipfile support
    """
    # XXX This should be a generic ArchiveFileInfoIterator that works with Zip
    #     and Tar?
    
    # XXX How to support zips inside zips, would need to uncompress to a
    #     temporary or to memory, but the zip directory is at the end of the
    #     file so it would require uncompressing the whole file to memory?
    #     Either way would need store the file it's coming from (use the history
    #     stack?) so it can go back from a temp file to a real file?

    # XXX Support tarfile (.tgz, .tar.gz, .tar.bz2, .tbz2)
    # XXX Support gzipfile (.gz)
    
    def __init__(self, arcpath, dirpath, recurse, *args, **kwargs):
        """
        - arcpath full path to the zip file
        - dirpath path to get fileinfos from, will be relative to the root
          inside the zip file using backward slashes, will be converted to
          forward slashes as required by the zip file format
        """
        logger.info("%r %r %s", arcpath, dirpath, recurse)
        # Change to forward slashes
        
        dirpath = dirpath.replace("\\", "/")
        # Make sure dirpath ends in unless it's the root, the rest of
        # subdirectories end in "/" in the zip filename list
        if (not dirpath.endswith("/")):
            dirpath += "/"
        # filenames start without slash inside the zip directory
        if (dirpath.startswith("/")):
            dirpath = dirpath[1:]
        
        self.dirpath = dirpath
        self.arcpath = arcpath
        self.zip = None
        self.done = False
        self.recurse = recurse

    def getFileInfos(self, batch_size=0):
        dir_infos_set = set()
        file_infos = []

        if (self.zip is None):
            # XXX Split the path into path to the zip file and path inside the
            #     zip file
            self.zip = zipfile.ZipFile(self.arcpath)
            self.current_file = 0
            logger.info("filelisting")
            self.namelist = self.zip.namelist()
            # There are no .. entries in a zip, add them no matter the directory
            # being listed
            # XXX This should use the parent directory mtime, if present
            dir_infos_set = set([FileInfo("..", 0, 0, fileinfo_build_attr(True, False, True, False))])
            self.dir_names = set([".."])

        # XXX Is doing filelist first and then info more efficient?
        
        logger.info("processing")
        z = self.zip
        l = self.namelist
        
        while (len(l) > 0):
            # Filenames inside zip
            # - use forward slashes
            # - start without slash
            # - end with slash if directories, but it may not have explicit
            #   directory entries
            filename = l.pop()

            # Check if this file is in the requested directory. Note paths in
            # filename use forward slashes and directories end in forward slash
            
            # Allow only files inside dirpath (no / or direct subdirectories, ie / at the end)
            if (filename.startswith(self.dirpath) and (filename != self.dirpath)):
                relpath = filename[len(self.dirpath):]
                i = index_of(relpath, "/")
                if ((i != -1) and (i != (len(relpath) - 1))):
                    # If recursing, fall through to create this entry, otherwise
                    # recreate the subdir of this entry if ot already done
                    if (not self.recurse):
                        # This entry is in some subdirectory, some zips don't
                        # have entries for directories at all, so create an
                        # entry for this subdirectory if not already created.
                        # Include the trailing slash that identifies directory
                        # entries when present
                        relpath = relpath[:i+1] 
                        # Recreate the theoretical entry filename for this
                        # subdirectory
                        filename = self.dirpath + relpath
                        if (relpath not in self.dir_names):
                            assert None is logger.debug("Adding subdirpath %r filename %r", relpath, filename)
                            # Fall through below to create this subdirpath

                        else:
                            assert None is logger.debug("Discarding relpath %r deep inside dirpath %r filename %r", relpath, self.dirpath, filename)
                            continue
            else:
                assert None is logger.debug("Discarding filename %r not inside dirpath %r", filename, self.dirpath)
                continue
            
            assert None is logger.debug("Accepting filename %r in dirpath %r relpath %r", filename, self.dirpath, relpath)

            if (filename.endswith("/")):
                # Fetch the directory mtime if there's an entry for this
                # directory: not all directories may have an entry so this may
                # be a synthetic name created above
                if (relpath not in self.dir_names):
                    try:
                        zipinfo = z.getinfo(filename)
                        mtime = datetime.datetime(*zipinfo.date_time)
                        mtime = datetime_to_utctimestamp(mtime)
                    except KeyError:
                        logger.info("Directory %r not available", filename)
                        mtime = 0
                    
                    # Remove the final slash
                    filename = relpath[:-1]
                    attr = fileinfo_build_attr(True, False, True, False)
                    file_info = FileInfo(filename, 0, mtime, attr)
                    dir_infos_set.add(file_info)
                    self.dir_names.add(filename)

            else:
                zipinfo = z.getinfo(filename)
                filename = relpath

                # file_size is the uncompressed size, compress_size is the
                # compressed size
                size = zipinfo.file_size
                mtime = datetime.datetime(*zipinfo.date_time)
                mtime = datetime_to_utctimestamp(mtime)
                attr = fileinfo_build_attr(False, False, True, False)
                file_info = FileInfo(filename, size, mtime, attr)
                file_infos.append(file_info)

            if (((batch_size > 0) and ((len(dir_infos_set) + len(file_infos)) >= batch_size)) or (len(l) == 0)):
                break

        file_infos = list(dir_infos_set) + file_infos 
        
        self.done = (len(file_infos) == 0)
        
        return dir_infos_set, file_infos

    def extract(self, filepath):
        relpath = filepath[len(self.arcpath)+1:]
        # Entries in the zip file use forward slashes with no starting
        # forward slash
        entrypath = relpath.replace("\\", "/")
        # extract will recreate the same directory as the zip
        # XXX Using .extract() is simple but has several issues: no progress
        #     report, no cancel, no background, hardcoded destination path
        # Put each file in a semi unique temp subdirectory
        temp_subdir = "%x" % (hash(self.arcpath) + (sys.maxint - 1))
        temp_relpath = os.path.join(temp_subdir, relpath)
        temp_dir = os.path.join(TEMP_DIR, temp_subdir)
        # Extract with stored path to the unique temp subdirectory
        self.zip.extract(entrypath, temp_dir)
        filepath = os.path.join(temp_dir, relpath)
        filepath = os.path.abspath(filepath)
        return filepath

    def isDone(self):
        return self.done

class CsvFileInfoIterator(FileInfoIterator):
    """
    XXX This is slow in CSV files with many rows, and even slower in
        mergeDirEntries once there are many.

        Convert to EFU and load in Everything Options->indexes->file lists, 
        Everything will auto-reload the EFU files when modified. There's even an 
        embedded file list editor tools->file list editor

    See
    - https://www.voidtools.com/support/everything/file_lists/#what_is_the_format_of_an_efu_file_list
    - https://www.voidtools.com/support/everything/file_lists/#include_a_file_list_in_the_everything_index


    "Everything.exe -create-file-list "ab.efu" "c:\somefolder" 

    ES -export-efu "ab.efu" "C:\somefolder\"

    EFU format

    Filename,Size,Date Modified,Date Created,Attributes
    "C:\pagefile.sys",14742704128,132315493941588771,,0

    https://www.voidtools.com/forum/viewtopic.php?t=13808
    https://www.voidtools.com/forum/viewtopic.php?t=14086

    https://github.com/zybexXL/EFUtool
    https://github.com/tobbez/everything-efu-gen
    """
    def __init__(self, filepath_or_string_list, file_dir = "", *args, **kwargs):
        """
        This accepts:
        - A list of rows, each row a single string with comma separated fields
          (same as csv.reader) filename,dirname,size,mtime 
        - A path to a csv file
        - A path to a gzip compresed csv file
        """
        self.string_list = None
        self.filepath = None
        self.file_dir = file_dir
        
        if (isinstance(filepath_or_string_list, (list, tuple))):
            self.string_list = filepath_or_string_list
            
        else:
            self.filepath = filepath_or_string_list

        # Don't create the reader here in case it's thread-affine
        self.csv_reader = None
        self.done = False

    def getFileInfos(self, batch_size=0):
        import gzip
        import csv

        dir_infos_set = set()
        file_infos = []
        
        # XXX Missing implementing recurse (but disable it for Network entries
        #     since they are plugins)
        # XXX Missing implementing restricting entries to dirpath
        if (self.csv_reader is None):
            if (self.string_list is not None):
                # csv.reader already supports list of strings
                f = self.string_list
                logger.info("Opened csv string list")
            else:
                # Allow gzip and regular csv
                filepath = self.filepath
                try:
                    # XXX Check if this needs reading something to throw exception
                    f = gzip.open(self.filepath, "rb")
                    logger.info("Opened gzip csv file %r", self.filepath)
                except:
                    f = open(self.filepath, "rb")
                    logger.info("Opened regular csv file %r", self.filepath)
            reader = csv.reader(f)
            self.csv_reader = reader
            # XXX Does this need to keep a reference to f or is reader enough?

        for row in self.csv_reader:
            # filename, dirpath, file size if positive else dir, mtimeutc
            filename, dirpath, is_dir_or_size, mtime = row

            filepath = os.path.join(dirpath, filename)
            
            if (self.file_dir != ""):
                filepath = filepath[len(self.file_dir)+1:]
            is_dir_or_size = int(is_dir_or_size)
            is_dir = (is_dir_or_size < 0)
            size = 0 if (is_dir) else is_dir_or_size
            mtime = int(mtime) / 1000

            # Entries can be utf-8 but csv module doesn't have utf-8 decoding
            # and standard open() wich does support utf-8 decoding is not used
            # on gzipped csvs, so this works with both gzipped and non-gzipped
            # csvs
            file_info = FileInfo(filepath.decode("utf-8"), size, mtime, fileinfo_build_attr(is_dir, False, True, False))
            if (is_dir):
                dir_infos_set.add(file_info)
                
            else:
                file_infos.append(file_info)

            if ((batch_size > 0) and ((len(file_infos) + len(dir_infos_set)) >= batch_size)):
                # This is pure Python which hogs the GIL, give time to other
                # Python threads
                # XXX This wouldn't be needed if run out of process
                time.sleep(1)
                break

        file_infos = list(dir_infos_set) + file_infos 
        self.done = (len(file_infos) == 0)
            
        return dir_infos_set, file_infos

    def isDone(self):
        return self.done

class FileSearchFileInfoIterator(FileInfoIterator):
    def __init_(*args, **kwargs):
        """
        
        Scenarios:
        - Search a file by name in a directory/selected files/file mask/regex/iterator
        - Search a file by content in a directory/selected files/file mask/regex/iterator
        - Limit search to selected files
        - Recurse dirs or not
        - Recurse zips

        Input files:
        - List of fileinfos
        - List of filepaths
        - FileInfo Iterator
        - Iterator plus regexp / wildcard
        - Wildcard and use the default iterator

        Flags:
        - Recurse
        - Recurse zips

        Search:
        - No search string
        - Search string 
        """
        raise NotImplementedError

def safe_unicode(s):
    """
    Convert s to unicode if not already using utf-8 and falling back to latin1
    on error (some filenames will fail to decode using utf-8
    
    This is used on win32 api results when the results are opaque to Python
    """
    if isinstance(s, unicode):
        return s
    elif isinstance(s, str):
        try:
            return s.decode('utf-8')
        except UnicodeDecodeError:
            try:
                return s.decode('latin1')
            except:
                return unicode(s, errors='ignore')
    else:
        return unicode(s)


class EditablePopupMenu(QMenu):
    """
    Popup menu that
    - can be checked/unchecked, via ctrl+click or spacebar 
    - options can be deleted via DEL
    without those causing the menu to close
    """
    def __init__(self, parent=None, allow_delete = False, allow_check = True):
        """
        A global allow_check is arguably redundant since menu options already
        have setCheckable, but sometimes a check mark is desired as visual
        indicator even if allow_check is false, and setCheckable is necessary
        since otherwise setChecked is ignored
        """
        # XXX Should allow passing a minimum number of undeleted options? (some
        #     callers allow deleting all, some must leave at least one
        #     undeleted?)
        super(EditablePopupMenu, self).__init__(parent)
        self.allow_delete = allow_delete
        self.allow_check = allow_check
        self.next_number = 0
        # Note this is in deletion order, the caller may need to sort it reverse
        # if holding indices and removing entries from an array
        self.deleted_datas = []
    
    def addAction(self, title, data=None, auto_number=False):
        logger.info("%s", title)

        if (auto_number):
            shortcuts = string.digits + string.ascii_uppercase
            title = "&%s. %s" % (shortcuts[self.next_number], title)
            self.next_number += 1

        action = super(EditablePopupMenu, self).addAction(title)
        action.setData(data)
        return action

    def exec_(self, pos):
        logger.info("")

        # The menu pops up without an action active, set one
        self.setActiveAction(self.actions()[0])
        # The menu doesn't grab the keyboard focus when first displayed until a
        # cursor key is pressed. If the first key is space this causes the key
        # to go to the parent widget, which is wrong, force a focus
        self.setFocus()
        return super(EditablePopupMenu, self).exec_(pos)

    def keyPressEvent(self, event):
        logger.info("%r", event)
        # Check if the pressed key is the spacebar
        if ((event.key() == Qt.Key_Space) and self.allow_check):
            # Get the currently active/highlighted action in the menu
            active_action = self.activeAction()
            if (active_action and active_action.isCheckable()):
                # Manually trigger the action and accept the event
                active_action.setChecked(not active_action.isChecked())
                event.accept()
                return
                
        elif ((event.key() == Qt.Key_Delete) and self.allow_delete):
            active_action = self.activeAction()
            data = active_action.data()
            if (data is not None):
                i = index_of(self.actions(), active_action)

                self.deleted_datas.append(data)
                self.removeAction(active_action)
                # Focus on the next action
                self.setActiveAction(self.actions()[min(i, len(self.actions())-1)])
        
        # For all other key events, let the base class handle them
        super(EditablePopupMenu, self).keyPressEvent(event)

    def mousePressEvent(self, event):
        logger.info("%r", event)

        if (((event.button() == Qt.LeftButton) and (event.modifiers() & Qt.ControlModifier)) and self.allow_check):
            # Get the currently active/highlighted action in the menu
            active_action = self.activeAction()
            if (active_action and active_action.isCheckable()):
                active_action.setChecked(not active_action.isChecked())
                event.accept()
                return

        super(EditablePopupMenu, self).mousePressEvent(event)


class DirectoryReader(QThread):
    direntryRead = pyqtSignal(set, list)
    def __init__(self, dirpath, batch_size = 0, parent=None, it=None, loop=True):
        super(DirectoryReader, self).__init__(parent)
        self.dirpath = dirpath
        self.batch_size = batch_size
        self.it = it
        self.loop = loop
        
    def start(self, single_thread = False):
        logger.info("single_thread %s", single_thread)
        self.single_thread = single_thread
        if (single_thread):
            # Emit signals so callers still get them
            logger.info("Emitting fake started")
            self.started.emit()
            self.run()
            logger.info("Emitting fake finished")
            self.finished.emit()

        else:
            super(DirectoryReader, self).start()
            
    def abort(self):
        logger.info("Requesting abort")
        self.requestInterruption()
        
    def mustAbort(self):
        return self.isInterruptionRequested()

    def run(self):
        logger.info("Starting %r", self.dirpath)

        # XXX Have a mode that evicts/delay loads other data (stats, etc) in a
        #     similar way to thumbnails?

        assert self.it is not None
        it = self.it

        while (not self.mustAbort()):
            dir_infos_set, file_infos = it.getFileInfos(self.batch_size)
            if (len(file_infos) == 0):
                break
            self.direntryRead.emit(dir_infos_set, file_infos)
            if (not self.loop):
                break

        logger.info("Aborted" if (self.mustAbort()) else "Ended" )
        
        if (not self.single_thread):
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
        self.watcher = None

        # Create the bare minimum so things don't crash
        self.file_dir = None
        self.loaded_rows = 0
        self.file_infos = []
        self.dir_infos_set = set()
        self.is_search_string = False

        # XXX These are actually stored on the headerview, remove if using
        #     proxymodel?
        self.sort_order = None
        self.sort_field = None
        self.sort_column = None

        self.it = None

        self.initCache()
        
        def receive_pixmap(row_hint, filepath, pixmap):
            """
            Receive a pixmap from the PixmapReader thread. Put it in the cache
            for the given key and trigger datachanged for the given row.

            The row is a hint because the row may have changed since the image
             was requested (elements inserted/deleted, directory navigated away)

            This is connected to a signal fired by in the PixmapReader and runs
            in the UI thread, so it's safe to modiy the cache, etc.
            """
            logger.info("row_hint %d %r", row_hint, filepath)

            # This could be out of bounds if a stale request gets here, assign
            # an invalid index explicitly if so (isValid()
            # doesn't check for bounds, Qt 5.11 introduces checkIndex for that).
            # See
            # https://stackoverflow.com/questions/20530638/should-qabstractitemmodelindexrow-column-parent-check-for-invalid-inputs
            index = self.createIndex(row_hint, 0) if (row_hint < self.rowCount()) else QModelIndex()

            # The index may no longer contain that filepath because the
            # directory was navigated away or some other index deleted, find the
            # new index, if any
            if ((not index.isValid()) or (index.data(Qt.UserRole).filename != filepath)):
                # Find the new new row, if any, don't bother finding in the
                # normal case where the directory was navigated away
                if (self.is_search_string or (self.file_dir == os.path.basename(filepath))):
                    row = self.findFileInfoRow(filepath) 
                    index = self.createIndex(row, 0) if (row != -1) else QModelIndex()

            if (index.isValid()):
                self.dataChanged.emit(index, index, [Qt.DecorationRole])
            
            # Arguably this could skip the cache if the row is no longer valid,
            # but since it did the work of fetching the image, let the cache
            # purging take care of that
            key = filepath
            self.request_set.remove(key)
            
            if (pixmap.isNull()):
                logger.error("Error receiving %r", filepath)
                pixmap = self.image_cache[":error"]
                
            self.cacheImage(key, pixmap)
                
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
                    key = filepath
                    logger.info("purging request row %d %r", row, filepath)
                    assert key in self.request_set
                    assert key not in self.image_cache
                    self.request_set.remove(key)

                    # Trigger new requests, ignore stale requests
                    if ((os.path.dirname(filepath) == self.file_dir) or self.is_search_string):
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

    def needsExtracting(self):
        # XXX is self.it ever None?
        return ((self.it is not None) and hasattr(self.it, "extract"))

    def findFileInfoRow(self, filename):
        """
        Return the row number for the given filename, -1 if the filename is 
        not in the model
        """
        return index_of([f.filename for f in self.file_infos], filename)

    def createIterator(self, file_dir_or_search=None, is_search_string=False, recurse=False):
        """
        Create an iterator for file_dir, depending on the path (packed files,
        regular files) or search string
        """
        loop = True
        file_dir = file_dir_or_search
        file_dir_lower = file_dir.lower()
        it = None
        # XXX Read installed wcx/wfx from a config file, could also discover from
        #     plugin directory and use CanYouHandleThisFile, but that's an optional
        #     function
        
        # XXX This is likely to be the same iterator that is current, have some
        #     state that remembers which iterator it came from or a hint of what
        #     iterator to try first?

        dllext = ".wfx" if platform_is_32bit() else ".wfx64"
        wfx_infos = [
            WFXInfo(SHARE_ROOT + "\\webdav", R"_out\davplug\davplug" + dllext),
            WFXInfo(SHARE_ROOT + "\\sftp", R"_out\sftpplug\sftpplug" + dllext) ,
            # XXX Disabled for now since it's crashing, it's from double
            #     commander and has extra entry points, may not be enough with
            #     hooking the total commander ones
            # WFXInfo(SHARE_ROOT + "\\ftp", R"_out\ftp\ftp.wfx"),
        ]
            
        if (is_search_string):
            it = EverythingFileInfoIterator(file_dir, sort_field=self.sort_field, sort_reverse=(self.sort_order == Qt.DescendingOrder))
            loop = False

        elif (os_path_contains(SHARE_ROOT, file_dir)):
            # Hook the WFX plugins and network from here 

            # XXX Find out what to do with plugin_id, it's only used:
            #     - for initialization
            #     - for callback functions into twin.py so it can identify what
            #       wfx plugin is making the call
            #     - as key into the global per wfx plugin state dict
            #     Should probably be generated in the constructor rather than 
            #     passed in?
            for wfx_info in wfx_infos:
                if (os_path_contains(wfx_info.root, file_dir)):
                    relpath = file_dir[len(wfx_info.root):] + "\\"
                    it = WFXFileInfoIterator(wfx_info.root, wfx_info.dllpath, relpath, recurse, hash(wfx_info.dllpath))
                    break
                
            else:
                # XXX Hook network shares, probably using wmi or "net view"/"net
                #     share" command ("net view" can take a long time to
                #     execute, though) or NetServerEnum/NetShareEnum from pywin32
                # XXX Get icons from extracticon, etc
                # name, path, size (<0 if dir), mtime
                l = [ "%s, %s, -1, 1624206883116" % (os.path.basename(wfx_info.root), os.path.dirname(wfx_info.root)) for wfx_info in wfx_infos]
                # Can't recurse into the entries since they are different WFX
                # plugins, disable
                it = CsvFileInfoIterator(l, SHARE_ROOT + "\\", False)
                
        elif (os.path.isdir(file_dir)):
            try:
                it = Win32FileInfoIterator(file_dir, recurse)
            
            except Exception as e:
                # Expected on non-Windows OSs, fall back to Qt
                logger.warn("Falling back to QtFileInfoIterator due to exception loading Win32FileInfoIterator %r", e)
                it = QtFileInfoIterator(file_dir, recurse)
            
        else:
            # XXX These will fail on non-windows OS
            # XXX Listing archives inside archives is not currently implemented
            #     and will fail, but don't want to output dialog boxes here,
            #     check and raise?
            arcpath = os_path_physpath(file_dir)
            dirpath = file_dir[len(arcpath):]
            ext_lower = os.path.splitext(arcpath)[1].lower()

            dllext = ".wcx" if platform_is_32bit() else ".wcx64"

            # XXX Refactor below into table
            # XXX Fix for 32-bit, pass multiple DLLs? preload the DLL?
            # XXX All these should fall back to the plugin's "CanYouHandleThisFile" function
            if (ext_lower in TOTAL7ZIP_EXTENSIONS):
                it = WCXFileInfoIterator(R"_out\total7zip\total7zip" + dllext, arcpath, dirpath, recurse)
                
            elif (ext_lower == ".bz2"):
                it = WCXFileInfoIterator(R"_out\bzip2dll" + dllext, arcpath, dirpath, recurse)
                
            elif (ext_lower == ".iso"):
                it = WCXFileInfoIterator(R"_out\iso" + dllext, arcpath, dirpath, recurse)
                
            else:
                # XXX This is hit when there's a permission violation accessing
                #     a real directory. Should probably raise and the caller
                #     retry the parent directory. Doing it befhore hand is hard
                #     because there are many ad-hoc paths that are not real
                #     directories but are valid to switch to (virtual archive
                #     paths, network plugin paths...)
                assert zipfile.is_zipfile(arcpath)
                it = ZipFileInfoIterator(arcpath, dirpath, recurse)
                
        return it, loop


    def getFiles(self, insert_only = False, create_it=True):
        logger.info("reading dir")

        def receive_direntry(dir_infos_set, file_infos):
            
            # Sorting is redundant for is_search_string and also lumps
            # directories on top which doesn't honor Everything's sorting (eg
            # more directories could be coming as rows are loaded if sorting by
            # name)
            if (not self.is_search_string):
                sort_fileinfos(file_infos, self.sort_field, self.sort_order)

            self.mergeDirEntries(dir_infos_set, file_infos, insert_only)
            # New files received, there are begin and delete emits that will
            # update the view if they are visible, but if loaded_rows is not the
            # maximum, it could happen that directories are not shown. Call
            # fetchmore to guarantee that at least directories are shown
            
            # XXX This is probably no longer needed since there's a bugfix for
            #     requesting as long as the new rows are visible in
            #     fetchMoreIfVisible? (the bugfix is currently only applied when
            #     use_incremental_row_loading but is probably needed whenever a
            #     DirectoryModel can be updated?)
            if (self.rowCount() < len(self.dir_infos_set)):
                self.fetchMore(QModelIndex())
            
        if ((self.directoryReader is not None) and self.directoryReader.isRunning()):
            # Stop signals from the old thread, they are probably form a
            # previous directory listing and they would to the current grid but
            # fail to load due to the changed path
            logger.info("Disconnecting signal from old DirectoryReader finished %s running %s", 
                self.directoryReader.isFinished(), self.directoryReader.isRunning())
            self.directoryReader.direntryRead.disconnect()
            self.directoryReader.abort()

        # Batch and deletions are incompatible since, it cannot detect deletions
        # vs. a partial list (batch), only batch if insert_only
        
        # XXX This gets blocked behind image load, pause image loading while
        #     entries are being read
        loop = True
        # XXX Create the iterator in the filepane? But DirectoryModel.reload
        #     needs to reset the iterator
        # create_it will be False when resuming a previous getFiles
        if (create_it):
            self.it, loop = self.createIterator(self.file_dir, self.is_search_string)
        
        # XXX Is self.it ever None?
        self.directoryReader = DirectoryReader(self.file_dir, 500 if insert_only else 0, it=self.it, loop=True if (self.it is None) else loop)
        self.directoryReader.direntryRead.connect(receive_direntry)
        single_thread = (force_single_thread or 
            (force_wfx_single_thread and isinstance(self.it, WFXFileInfoIterator)) or
            (force_wcx_single_thread and isinstance(self.it, WCXFileInfoIterator)) or
            (force_everything_single_thread and isinstance(self.it, EverythingFileInfoIterator))
        )
        self.directoryReader.start(single_thread)

    def calculateSubdirSizes(self, subdir_index=QModelIndex()):
        """
        - subdir_index is a directory then calculate sizes for that subdir
        - subdir_index is invalid then calculate sizes for all subdirs in the
          table view
        - subdir_index is a file, do nothing
        """
        logger.info("reading dir")

        # XXX Allow queueing multiple single directory requests?
        
        if (subdir_index.isValid()):
            subdir_fileinfo = self.file_infos[subdir_index.row()]
            if (not fileinfo_is_dir(self.file_infos[subdir_index.row()])):
                # This gets called for non-directories, ignore those
                return
            subdir = subdir_fileinfo.filename
        else:
            # Search string doesn't have a "parent directory" to list and find
            # subdirectory sizes for, ignore
            
            # XXX Actually implement search string "subdirectory" size
            #     calculation by doing directory by directory calculation
            if (self.is_search_string):
                return

            subdir = None

        # dict with state so it can be shared and modified across inside the
        # different local functions
        subdir_sizes = {}

        def set_fileinfo_size(row, size):
            assert None is logger.debug("row %d, size %d", row, size)
            # XXX Remove dir_infos_set completely? use nameddicts so file_info
            #     can be modified vs. recreated?

            file_info = self.file_infos[row]
            self.dir_infos_set.remove(file_info)
            file_info = file_info._replace(size = size)
            self.dir_infos_set.add(file_info)
            self.file_infos[row] = file_info

            index = self.index(row, 3)
            # XXX This emit is really slow with 10s of directories, coalesce?
            #     debounce? rate limit?
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
            assert None is logger.info("Received direntry %s", file_infos)

            # Note because of using named tuples, subdir_fileinfo reference
            # changes on every size modification, refresh it
            # subdir_fileinfo = self.file_infos[subdir_index.row()]
            # Size is negative while it's being calculated
            #size = subdir_fileinfo.size - sum([file_info.size for file_info in file_infos])
            
            # XXX When in search mode this should go through all the directories in
            #     the search?
            # XXX Calculate one with WCXFileInfoIterator seems to set the parent
            #     size the single subdir, calculate all works
            for file_info in file_infos:
                if (file_info.filename == ".."):
                    continue
                #relpath = os.path.relpath(file_info.filename, self.file_dir)
                # XXX This assumes filename is relative, which won't be for
                #     search results
                
                # Get the subdirectory for this entry, relative to the root, ie
                # the topmost dir being iterated
                this_subdir = os_path_root(file_info.filename)
                # When this_subdir is None, it means this is an entry in the
                # topmost dir being iterated, which shouldn't be included in the
                # calculation
                this_subdir = subdir if (subdir is not None) else this_subdir 
                # Note this will store the current dir size in the None entry
                # XXX This could update the model incrementally with a negative
                #     size but this is faster than emitting signals etc and the "?"
                #     indicator is good enough?
                if (this_subdir is not None):
                    if (current_state["subdir"] != this_subdir):
                        # This is the first time this directory is updated,
                        # change icon to being updated and finalize the size for
                        # the subdir previously being updated
                        
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

        
        for row in xrange(self.file_infos):
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
        dirpath = self.file_dir if subdir is None else os.path.join(self.file_dir, subdir)
        it, loop = self.createIterator(dirpath, self.is_search_string, recurse=True)
        self.directoryReader = DirectoryReader(dirpath, 100, it=it, loop=loop)
        self.directoryReader.direntryRead.connect(receive_direntry)
        self.directoryReader.finished.connect(finish_size_calculation)
        single_thread = (force_single_thread or (force_wfx_single_thread and isinstance(self.it, WFXFileInfoIterator)))
        self.directoryReader.start(single_thread)
        
    def reloadDirectory(self, clear_cache=False):
        if (clear_cache):
            self.clearCache()
            # Clearing the caches is not enough to refresh the visible items,
            # since Qt may have its own DecorationRole cache, emit a dataChanged
            topleft = self.createIndex(0, 0)
            bottomright = self.createIndex(self.rowCount(), self.columnCount())
            self.dataChanged.emit(topleft, bottomright, [Qt.DecorationRole])
        
        # Reload and merge the new entries to not perturb the UI
        self.getFiles(create_it=True)

    def mergeDirEntries(self, new_dir_infos_set, new_file_infos, insert_only = False):
        """
        Merge new_ into the existing fileinfos
        - insert_only: the new_ is a partial list so deletions cannot be done,
          only perform insertions, properly sorted in the existing list
        - otherwise new_ is a complete list and make so the existing fileinfos
          ends up matching, but done in a way that sends incremental updates to
          the view

        Does two things:
        - Merge entries preserving UI (selection, currentindex)
        - Merges entries preserving sort order
        """
        # XXX Test if blocksignals help with speed
        # self.blockSignals(True)
        logger.info("num dirs %d num files %d insert only %s", len(new_dir_infos_set), len(new_file_infos), insert_only)
        #logger.info("%s %s", new_dir_infos_set, new_file_infos)
        i_old = 0
        i_new = 0
        # XXX This will fail to load the rows if there are less than one screen
        #     worth of entries in some getFiles codepath, gets fixed if history
        #     is navigated back and forth or even ctrl+r, so some other path is ok?
        incremental_loading = use_incremental_row_loading or self.use_incremental_row_loading
        dummy_inserts = 0
        while (True):
            f_old = self.file_infos[i_old] if (i_old < len(self.file_infos)) else None
            f_new = new_file_infos[i_new] if (i_new < len(new_file_infos)) else None

            if ((f_old is None) and (f_new is None)):
                break

            assert None is logger.debug("Comparing old %r vs. new %r", f_old, f_new)

            if (self.is_search_string):
                # Everything search entries come presorted, doing sort on top of
                # that would break since the Everything sort is different from
                # the standard sort (eg no directory lumping at the beginning),
                # but still want to do dummy row inserting etc, so just fudge c
                # so it concatenates new entries at the end of old entries
                c = 1 if (f_old is None) else -1

            else:
                # Pick new if old is none, old if new is none, compare if both are not none
                c = 1 if (f_old is None) else (-1 if (f_new is None) else fileinfo_cmp(f_old, f_new, self.sort_field, self.sort_order == Qt.DescendingOrder))

            if (c == 0):
                # Matching fileinfos, no need to insert
                # XXX Update date/attribs if different? Then it will need to
                #     send a datachanged?
                i_old += 1
                i_new += 1
            
            elif (c == -1):
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
                        filepath = os.path.join(self.file_dir, f_old)
                        key = filepath
                        del self.image_cache[key]
                        self.lru_image_keys.remove(key)
            else:
                # f_new was added
                assert None is logger.debug("Inserted %r", f_new)
                
                # Prevent triggering "Invalid index", only report insertion if
                # row was loaded, including after the last loaded row, which
                # takes care of forcing a refresh when file_infos increase
                # (otherwise the view is stale if files are added when
                # loaded_rows == len(file_infos) )
                # When doing incremental loading, only insert a single dummy
                # row, otherwise incrementing loaded_rows below will defeat
                # incremental loading
                is_loaded_row = (
                    (i_old <= self.loaded_rows) and (
                        (not incremental_loading)
                    )
                )
                dummy_inserts = 1
                if (is_loaded_row):
                    dummy_inserts += 1
                    self.beginInsertRows(QModelIndex(), i_old, i_old)
                self.file_infos.insert(i_old, f_new)
                if (is_loaded_row):
                    self.loaded_rows += 1
                    self.endInsertRows()
                
                # Increment the old index as well as the new, since it has been
                # inserted in the old list
                i_new += 1
                i_old += 1

        # assert len(self.file_infos) == len(new_file_infos)
        # assert self.file_infos == new_file_infos
        
        if (insert_only):
            self.dir_infos_set |= new_dir_infos_set
        else:
            self.dir_infos_set = new_dir_infos_set

        if (incremental_loading and (dummy_inserts > 0)):
            if (self.canFetchMore(QModelIndex())):
                # Emit a dummy insert (note 0 row range below) so insertRows
                # gets emitted and the view can fetch until all the visible rows
                # have been fetched
                logger.info("Emitting dummy insert")
                self.beginInsertRows(QModelIndex(), self.loaded_rows, self.loaded_rows - 1)
                self.endInsertRows()

        # self.blockSignals(False)
        # self.layoutChanged.emit()
        logger.info("Done")

    def initCache(self):
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
        # XXX Should the cache be preserved across directory changes?
        # XXX Should the cache be shared across models?
        # XXX Needs a way to force cache invalidation, eg when reloading the dir?
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

        icon = qGetSystemIcon("test", qApp.style().standardIcon(QStyle.SP_DirIcon), is_dir=True)
        self.image_cache[":directory_icon"] = icon
        pixmap = qResizePixmap(icon.pixmap(256, 256), IMAGE_WIDTH, IMAGE_WIDTH)
        self.image_cache[":directory"] = pixmap

        icon = qGetSystemIcon(".lnk", qApp.style().standardIcon(QStyle.SP_FileLinkIcon), is_link = True)
        self.image_cache[":file_link_icon"] = icon
        pixmap = qResizePixmap(icon.pixmap(256, 256), IMAGE_WIDTH, IMAGE_WIDTH)
        self.image_cache[":file_link"] = pixmap

        icon = qGetSystemIcon("test", qApp.style().standardIcon(QStyle.SP_DirLinkIcon), is_dir = True, is_link=True)
        self.image_cache[":directory_link_icon"] = icon
        pixmap = qResizePixmap(icon.pixmap(256, 256), IMAGE_WIDTH, IMAGE_WIDTH)
        self.image_cache[":directory_link"] = pixmap

        icon = qApp.style().standardIcon(QStyle.SP_FileDialogNewFolder)
        icon = qApp.style().standardIcon(QStyle.SP_BrowserReload)
        self.image_cache[":directory_sizing_icon"] = icon

        icon = qGetSystemIcon(".sys", qApp.style().standardIcon(QStyle.SP_MessageBoxCritical), is_system=True)
        self.image_cache[":file_system_icon"] = icon
        pixmap = qResizePixmap(icon.pixmap(256, 256), IMAGE_WIDTH, IMAGE_WIDTH)
        self.image_cache[":file_system"] = pixmap

        #dir_icon = qGetSystemIcon("", qApp.style().standardIcon(QStyle.SP_MessageBoxWarning), is_hidden=True)
        icon = qApp.style().standardIcon(QStyle.SP_MessageBoxWarning)
        self.image_cache[":file_hidden_icon"] = icon
        pixmap = qResizePixmap(icon.pixmap(256, 256), IMAGE_WIDTH, IMAGE_WIDTH)
        self.image_cache[":file_hidden"] = pixmap

        icon = qGetSystemIcon(".zip", qApp.style().standardIcon(QStyle.SP_DialogOpenButton))
        self.image_cache[":file_packed_icon"] = icon
        pixmap = qResizePixmap(icon.pixmap(256, 256), IMAGE_WIDTH, IMAGE_WIDTH)
        self.image_cache[":file_packed"] = pixmap

        icon = qApp.style().standardIcon(QStyle.SP_DialogOkButton)
        self.image_cache[":directory_up_icon"] = icon
        pixmap = qResizePixmap(icon.pixmap(256, 256), IMAGE_WIDTH, IMAGE_WIDTH)
        self.image_cache[":directory_up"] = pixmap

        icon = qApp.style().standardIcon(QStyle.SP_FileIcon)
        self.image_cache[":file_icon"] = icon
        pixmap = qResizePixmap(icon.pixmap(256, 256), IMAGE_WIDTH, IMAGE_WIDTH)
        self.image_cache[":file"] = pixmap

    def clearCache(self):
        self.image_cache = { key: entry for key, entry in self.image_cache.iteritems() if key.startswith(":") }
        # Keep only the default entries
        self.lru_image_keys = []

    def setDirectory(self, file_dir, is_search_string=False):
        # XXX This needs to idle the threads
        # XXX Also treat archives (.zip, etc) as directories?
        # XXX Remember selections per directory?
        logger.info("%r %s", file_dir, is_search_string)

        self.beginResetModel()

        self.file_dir = file_dir
        self.is_search_string = is_search_string
        self.use_incremental_row_loading = self.is_search_string
        self.loaded_rows = 0
        self.file_infos = []
        if (self.is_search_string):
            logger.info("Not watching search string")
            self.watcher = None
        else:
            watch_dir = os_path_physpath(self.file_dir)
            logger.info("Watching dir %r", watch_dir)
            # XXX This doesn't watch recursively and it won't watch new directories
            #     (which may be ok since the panel doesn't display a directory
            #     recursively and the signa will still trigger if some parent is
            #     deleted?)
            self.watcher = QFileSystemWatcher([watch_dir])
            # XXX What if the directory (or file in case of archives) is removed? or
            #     generally if the directory is invalid? Should setDirectory to the
            #     deepest valid path
            self.watcher.directoryChanged.connect(self.reloadDirectory)
            
        # XXX getFiles can fail for eg permission errors, don't set file_dir
        #     until getFiles works and return error or raise
        self.getFiles(True)

        self.endResetModel()

    def setSearchString(self, search_string):
        logger.info("%r", search_string)
        # XXX The merge files path is not necessary, remove
        merge_entries = False
        if (merge_entries):
            self.file_dir = search_string
            self.is_search_string = True
            self.getFiles(False)
        else:
            self.setDirectory(search_string, True)

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
            logger.info("cache_keys %s", self.image_cache.keys())
            logger.info("lru_image_keys %s", self.lru_image_keys)
            logger.info("purging cache rows %s", [self.findFileInfoRow(purge_key) for purge_key in self.lru_image_keys[:MAX_CACHE_ENTRIES_WATERMARK]])
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
        """
        - Qt will fetch the data for all the rows, whether they are visible or not
        - 

        This is the order of role requests when displaying the table view, which 
        starts at column 2, not clear why it doesn't request the column 1

        2025-09-18 11:55:14,117 INFO:twin.py(1562):[13680] data: index 0,2 role SizeHintRole
        2025-09-18 11:55:14,118 INFO:twin.py(1562):[13680] data: index 0,2 role FontRole
        2025-09-18 11:55:14,119 INFO:twin.py(1562):[13680] data: index 0,2 role TextAlignmentRole
        2025-09-18 11:55:14,121 INFO:twin.py(1562):[13680] data: index 0,2 role ForegroundRole
        2025-09-18 11:55:14,122 INFO:twin.py(1562):[13680] data: index 0,2 role CheckStateRole
        2025-09-18 11:55:14,124 INFO:twin.py(1562):[13680] data: index 0,2 role DecorationRole
        2025-09-18 11:55:14,125 INFO:twin.py(1562):[13680] data: index 0,2 role DisplayRole
        2025-09-18 11:55:14,127 INFO:twin.py(1562):[13680] data: index 0,2 role BackgroundRole
        
        And then for each column

        Then eventually 

        2025-09-18 11:55:15,904 INFO:twin.py(1562):[13680] data: index 0,1 role FontRole
        2025-09-18 11:55:15,904 INFO:twin.py(947):[27616] run: exifing
        2025-09-18 11:55:15,904 INFO:twin.py(1562):[13680] data: index 0,1 role TextAlignmentRole
        2025-09-18 11:55:15,907 INFO:twin.py(954):[27616] run: Found exif orientation 1
        2025-09-18 11:55:15,907 INFO:twin.py(1562):[13680] data: index 0,1 role ForegroundRole
        2025-09-18 11:55:15,907 INFO:twin.py(962):[27616] run: toqpixmapping
        2025-09-18 11:55:15,908 INFO:twin.py(1562):[13680] data: index 0,1 role CheckStateRole
        2025-09-18 11:55:15,910 INFO:twin.py(964):[27616] run: closing
        2025-09-18 11:55:15,910 INFO:twin.py(1562):[13680] data: index 0,1 role DecorationRole
        2025-09-18 11:55:15,911 INFO:twin.py(1022):[27616] run: done with 0 u'c:\\users\\public\\pictures\\grzegorz-rutkowski-winter-landscape-study-1500.jpg'
        2025-09-18 11:55:15,911 INFO:twin.py(1562):[13680] data: index 0,1 role DisplayRole
        2025-09-18 11:55:15,911 INFO:twin.py(1562):[13680] data: index 0,1 role BackgroundRole
        2025-09-18 11:55:15,915 INFO:twin.py(1562):[13680] data: index 0,2 role FontRole
        2025-09-18 11:55:15,915 INFO:twin.py(1562):[13680] data: index 0,2 role TextAlignmentRole
        2025-09-18 11:55:15,917 INFO:twin.py(1562):[13680] data: index 0,2 role ForegroundRole
        2025-09-18 11:55:15,917 INFO:twin.py(1562):[13680] data: index 0,2 role CheckStateRole
        2025-09-18 11:55:15,917 INFO:twin.py(1562):[13680] data: index 0,2 role DecorationRole
        2025-09-18 11:55:15,917 INFO:twin.py(1562):[13680] data: index 0,2 role DisplayRole

        """
        if (not index.isValid() or (index.row() >= self.rowCount())):
            return None
        assert None is logger.debug("index %d,%d role %s", index.row(), index.column(), EnumString(Qt, Qt.ItemDataRole(role)))

        file_info = self.file_infos[index.row()]

        if (index.column() > 1):
            if (role == Qt.DecorationRole):
                return None

        if (role == Qt.TextAlignmentRole):
            # Align filename, extension to the left, size to the right
            if ((index.column() == 2) and (fileinfo_is_dir(file_info))):
                # On directories extension (column 2) and size (column 3) are
                # joined and only the first is requested, align "<DIR>" and
                # directory size to the right
                return Qt.AlignRight
            elif (index.column() == 3):
                return Qt.AlignRight
            

        elif (role == Qt.EditRole):
            return file_info.filename

        elif (role == Qt.ToolTipRole):
            # XXX Display the filepath of the current file in some label too?
            #     Useful for different long filepaths like search or everything
            #     results
            return os.path.join(self.file_dir, file_info.filename)

        elif (role == Qt.DisplayRole):            
            # XXX Should this take the basename at least for index 0 (listview)
            #     in case the filename is a deep relative path or absolute
            #     because of coming from Everyting or some search? But elision
            #     should fix this?
            
            # t = os.path.basename(file_info.filename)
            t = file_info.filename
            
            is_dir = fileinfo_is_dir(file_info)
            is_link = fileinfo_is_link(file_info)

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

                elif (is_link):
                    t = "<LNK>"

                else:
                    size = file_info.size
                    t = QLocale().toString(size)

            elif (index.column() == 4):
                # XXX Fix UTC?
                try:
                    t = datetime.datetime.fromtimestamp(file_info.mtime)
                    # XXX Get this from locale
                    t = t.strftime("%Y-%m-%d %H:%M:%S")
                except ValueError:
                    logger.error("Bad mtime %d", file_info.mtime)
                    t = "1980-01-01 00:00:00"
                
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
        
        elif (role == Qt.DecorationRole):
            file_name = file_info.filename
            filepath = os.path.join(self.file_dir, file_name)
            key = filepath
            is_dir = fileinfo_is_dir(file_info)

            if (index.column() == 1):
                # Use the small icons so they fit and get transparency, don't
                # use pixmaps, which are opaque. Don't bother using thumbnails
                # since they are too small
                if (is_dir):
                    if (file_info.size == -2):
                        # Size being calculated
                        return self.image_cache[":directory_sizing_icon"]

                    elif (file_name == ".."):
                        return self.image_cache[":directory_up_icon"]

                    elif (fileinfo_is_link(file_info)):
                        return self.image_cache[":directory_link_icon"]

                    else:
                        return self.image_cache[":directory_icon"]

                else:
                    if (fileinfo_is_link(file_info)):
                        return self.image_cache[":file_link_icon"]
                        
                    elif (fileinfo_is_hidden(file_info)):
                        return self.image_cache[":file_hidden_icon"]

                    elif (not fileinfo_is_writable(file_info)):
                        return self.image_cache[":file_system_icon"]
                    
                    elif (fileinfo_is_packed(file_info)):
                        return self.image_cache[":file_packed_icon"]
                    
                    else:
                        ext = os.path.splitext(file_info.filename)[1]
                        key = ":%s_icon" % ext
                        icon = self.image_cache.get(key, None)
                        if (icon is None):
                            icon = qGetSystemIcon(file_info.filename, self.image_cache[":file_icon"])
                            self.cacheImage(key, icon)
                        return icon

            if (is_dir):
                if (file_name == ".."):
                    pixmap = self.image_cache[":directory_up"]
                elif (fileinfo_is_link(file_info)):
                    pixmap = self.image_cache[":directory_link"]
                else:
                    pixmap = self.image_cache[":directory"]

            elif ((not file_name.lower().endswith(IMAGE_EXTENSIONS)) or 
                # XXX Don't do thumbnails inside packed archives for now, implement?
                self.needsExtracting()):
                # XXX This is similar to the _icon above but it uses the pixmap
                #     versions which pixmaps and properly scaled, refactor?
                if (fileinfo_is_link(file_info)):
                    pixmap = self.image_cache[":file_link"]
                elif (fileinfo_is_hidden(file_info)):
                    pixmap = QPixmap(self.image_cache[":file_hidden"])

                elif (not fileinfo_is_writable(file_info)):
                    pixmap = QPixmap(self.image_cache[":file_system"])
                
                elif (fileinfo_is_packed(file_info)):
                    pixmap = QPixmap(self.image_cache[":file_packed"])
                
                else:
                    ext = os.path.splitext(file_info.filename)[1]
                    key = ":%s" % ext
                    pixmap = self.image_cache.get(key, None)
                    if (pixmap is None):
                        icon = qGetSystemIcon(file_info.filename, None, False)
                        if (icon is None):
                            pixmap = self.image_cache[":file"]
                        else:
                            pixmap = qResizePixmap(icon.pixmap(256, 256), IMAGE_WIDTH, IMAGE_WIDTH)
                        self.cacheImage(key, pixmap)
            else:
                # pixmap = self.image_cache[":requesting"]
                pixmap = self.image_cache.get(key, None)

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
                    if (key not in self.request_set):
                        pixmap = self.image_cache[":requesting"]
                        logger.debug("requesting index %d %r ", index.row(), key)
                        self.request_set.add(key)
                        self.request_queue.put((index.row(), filepath))
                    
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
        return ((self.rowCount() < len(self.file_infos)) or ((self.it is not None) and (not self.it.isDone())))

    def fetchMore(self, index):
        """ Load more rows when the user scrolls to the end """
        logger.info("loaded_rows before %d total %d", self.loaded_rows, len(self.file_infos))
        if (self.canFetchMore(QModelIndex())):
            if (self.rowCount() < len(self.file_infos)):
                if (use_incremental_row_loading or self.use_incremental_row_loading):
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
            elif ((self.it is not None) and (not self.it.isDone()) and (not self.directoryReader.isRunning())):
                self.getFiles(True, create_it = False)
        
    def sort(self, column, order):
        # XXX Having the sort in the main model is not ideal since it modifies
        #     the model for all the views, but since there's only one view per
        #     model (actually two, the list and the table, having the same sort
        #     is desirable since the list has no columns to sort by), this is ok
        #     for the time being. The alternative is to use a proxy model on the
        #     view, but that requires hooking all the extra source model
        #     functionality in the proxymodel or mapping between one and the
        #     other when necessary
        
        logger.info("column %d, order %s (0x%x)", column, EnumString(Qt, order), order)

        # The sort order can be changed via actions or via clicking on headers,
        # centralize here the current sort order, can also be obtained from the
        # view header horizontalHeader().sortIndicatorSection() and
        # horizontalHeader().sortIndicatorOrder())
        self.sort_order = order
        self.sort_column = column
        # FileInfo: Filename, size, mtime, attr
        # Model: Full filename, Filename, ext, size, date, attr
        # XXX Missing sorting by extension
        sort_field = 0 if (column <= 1) else (column - 2)
        self.sort_field = sort_field

        if (self.is_search_string):
            self.setSearchString(self.file_dir)
        
        else:

            self.layoutAboutToBeChanged.emit()

            # Preserve the persistent indices (seem to be used among others for the
            # selection model)
            
            persistent_indices = self.persistentIndexList()
            logger.info("Building before sort %d persistent index mapping", len(persistent_indices))
            row_mapping = {i: row for i, row in enumerate(self.file_infos)}

            sort_fileinfos(self.file_infos, self.sort_field, self.sort_order)
            
            logger.info("Building after sort %d persistent index mapping", len(self.file_infos))
            new_order = {id(row): i for i, row in enumerate(self.file_infos)}

            # Rebuild persistent indexes
            logger.info("Rebuilding %d persistent indices", len(persistent_indices))
            for idx in persistent_indices:
                old_row = idx.row()
                new_row = new_order[id(row_mapping[old_row])]
                idx_internal = self.index(new_row, idx.column())
                self.changePersistentIndex(idx, idx_internal)
            
            # XXX The currentitem index is still valid, but the view is now showing
            #     the old position (pressing cursors will bring the new index into
            #     view), would need to scroll to the new value of the current index,
            #     but that's a view thing, needs to hook on layoutChanged (or some
            #     new signal)

            self.layoutChanged.emit()

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
        logger.debug("decorationSize %r row %d col %d", option.decorationSize, index.row(), index.column())
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
            # Override the text with empty, text will be elided so don't want
            # sizeFromContents to look at the text to calculate the size since
            # it would enlarge the size beyond the icon size
            opt.text = ""

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
        logger.info("%r", event)
        super(FileTableView, self).focusInEvent(event)
        # XXX Uncomment to also enable tableheader accent on focus, note this is
        #     not useful in icon view since there are no headers in that view
        # self.horizontalHeader().setStyleSheet("QHeaderView::section { background-color: #cceeff; }")
        
    def focusOutEvent(self, event):
        logger.info("%r", self)
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

    def selectionCommand(self, index, event):
        """
        By default multiselect will toggle the selection when clicking, which is
        undesirable, return to change currentIndex but don't update the
        selection. To toggle, use right button, ctrl + left button or left
        button drag

        The other option is to override mousePressEvent, but this way it
        preserves itemActivate call when doubleclick and the select on single
        click drag.

        See
        https://github.com/qt/qtbase/blob/5.3/src/widgets/itemviews/qabstractitemview.cpp#L3875
        """
        logger.info("%d,%d %s", index.row(), index.column(), EnumString(QEvent, event.type()))

        if (event.type() == QEvent.MouseButtonPress):
            if ((event.button() == Qt.LeftButton) and (not (event.modifiers() & Qt.ControlModifier))):
                # Disable toggle on single click, this still enables toggle on
                # single drag, ctrl+click
                return QItemSelectionModel.NoUpdate
            elif (event.button() == Qt.RightButton):
                # Enable toggle on right button
                return QItemSelectionModel.Toggle | QItemSelectionModel.Rows
        return super(FileTableView, self).selectionCommand(index, event)

class FilePane(QWidget):
    directoryLabelChanged = pyqtSignal(str)
    def __init__(self, display_width = DISPLAY_WIDTH, sort_column=1, sort_order=Qt.AscendingOrder, *args, **kwargs):
        logger.info("")
        super(FilePane, self).__init__(*args, **kwargs)

        self.dir_history = []
        self.current_dir_history = -1
        self.search_mode = False
        self.old_file_dir = None

        self.search_string = ""
        self.search_string_display_ms = SEARCH_STRING_DISPLAY_TIME_MS
        self.search_string_timer = QTimer()
        self.search_string_timer.setSingleShot(True)
        self.search_string_timer.timeout.connect(self.resetSearchString)

        self.display_width = display_width

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
        # XXX This needs to be able to elide for very long dir names, see 
        #     https://stackoverflow.com/questions/68092087/one-line-elideable-qlabel
        self.directory_label = QLabel(self.file_dir)

        self.setModels(model)

        # Cofigure the listview
        self.list_view.setViewMode(QListView.IconMode)
        self.list_view_style = FixedWidthStyle()
        #self.list_view.setStyle(self.list_view_style)
        #self.list_view.setGridSize(QSize(DISPLAY_WIDTH, DISPLAY_HEIGHT+20))

        # setUniformItemSizes is important so past items are not data()ed, which
        # kills the LRU cache. ListViewPrivate::itemSize uses it to prevent
        # calling the delegate. Unfortunately this requires doing elision in the
        # model. Using a delegate avoids having to do elision in the model's
        # data() 
        if (use_delegate):
            delegate = ScaledIconDelegate(self.list_view)
            delegate.setWidth(self.display_width)
            self.list_view_style.setWidth(self.display_width)
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
        
        # setSortingEnabled and sortByColumn below cause a double call to sort
        # but here doesn't seem to be a way of avoding it
        self.table_view.setSortingEnabled(True)
        self.table_view.horizontalHeader().setSectionsClickable(True)
        self.sortByColumn(sort_column, sort_order)
        
        # Don't display row numbers
        self.table_view.verticalHeader().setVisible(False)
        # Shrink the row height to roughly font height
        self.table_view.verticalHeader().setDefaultSectionSize(self.table_view.fontMetrics().height() + 6)
        # Don't display the big thumbnail column
        self.table_view.hideColumn(0)
        self.table_view.setIconSize(QSize(16, 16))
        self.table_view.setShowGrid(False)
        self.table_view.activated.connect(self.itemActivated)
        # This is important for Evertyhing panels that have full paths in the
        # filename
        self.table_view.setTextElideMode(Qt.ElideMiddle)
        
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
        #       selection of the item found on every leter pressed. Fixed by
        #       eventFiltering letters (and enhanced to substring matching)
        #     - Multiselection causes clicking with the left mouse button to
        #       focus *and* select. This is fixed by overriding selectionCommand
        #       for left (and for ctrl left and right clicks, so they work as
        #       selection toggle now that left click doesn't)
        #     - The movement is still at cell level, left and right are still
        #       enabled and the focus rectangle drawn on the individual cell.
        #       This is fixed by eventFiltering left/right movement.
        #     - The focus rectangle is still on a single cell, not on the full
        #       row. This is fixed by using a delegate that removes the focus
        #       flag, which removes the focus rect altogether and triggering view
        #       updates on currentIndex changes
        # XXX Look into overriding QAbstractItemView::selectionCommand?
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

        self.directory_label.setFrameStyle(QFrame.Panel | QFrame.Sunken)
        self.directory_label.setAlignment(Qt.AlignVCenter | Qt.AlignLeft)

        layout.addWidget(self.directory_label)
        layout.setSpacing(0)
        layout.addLayout(self.view_layout)
        
        layout.addWidget(self.summary_label)

        # Install eventfilters on children views to trap focusin/out and change
        # header button color
        self.directory_label.installEventFilter(self)
        self.list_view.installEventFilter(self)
        self.table_view.installEventFilter(self)

        # Label font is too small, increase
        font = QFont(self.disk_info_label.font().family(), self.disk_info_label.font().pointSize()+2)
        self.disk_info_label.setFont(font)
        self.directory_label.setFont(font)
        self.summary_label.setFont(font)

        self.setLayout(layout)

        logger.info("ListView font %s pointSize %d height %d", self.list_view.font().family(), 
            self.list_view.font().pointSize(), self.list_view.fontMetrics().height())

        # Some actions are only for the tableview, call setupActions after all
        # the widgets are created
        self.setupActions()

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
        
        self.model.rowsInserted.connect(self.fetchMoreIfVisible)

        # Updating the summary is expensive and can be called frequently when
        # inserting/removing rows or calculating directory sizes, rate-limit the
        # update
        self.selection_model.selectionChanged.connect(self.rateLimitedUpdateSummary)
        self.model.rowsInserted.connect(self.rateLimitedUpdateSummary)
        self.model.rowsRemoved.connect(self.rateLimitedUpdateSummary)
        self.model.dataChanged.connect(self.rateLimitedUpdateSummary)
        self.model.modelReset.connect(self.rateLimitedUpdateSummary)

        self.model.modelReset.connect(self.updateDirectoryLabel)

        # Set an item delegate to do proper row-aware focus 
        self.table_view.setItemDelegate(CurrentRowHighlightDelegate(self.selection_model, self.table_view))

    def mergeDirSizeExt(self):
        model = self.table_view.model()
        self.table_view.clearSpans()
        for row in xrange(model.rowCount()):
            file_info = model.index(row, 0).data(Qt.UserRole)
            if (fileinfo_is_dir(file_info)):
                assert None is logger.debug("Merging %d", row)
                self.table_view.setSpan(row, 2, 1, 2)
            else:
                # This assumes directories go first and there are no spans in
                # files
                break
                
    def rateLimitedMergeDirSizeExt(self):
        # Don't rate limit this call too much, otherwise the UI takes time to
        # enlarge the <DIR> columns and the UX is bad
        qRateLimitCall(self.mergeDirSizeExt, 10)

    def fetchMoreIfVisible(self):
        if (use_incremental_row_loading or self.search_mode):
            logger.info("")
            # Always load a full viewport worth of rows, otherwise when:
            # - The view is showing all the available rows, canFetchMore has
            #   returned False
            # - New rows are inserted 
            # - The dummy insertion is emitted
            # then the view will only callfetchMore/fetchMore once if all the
            # returned rows are visible.

            # To fix that, 
            # - connect fetchMoreIfVisible on the model's rowsInserted
            # - fetch as many rows as they fit in the viewport
            # - this causes Qt to start the canFetchMore/fetchMore state when
            #   scrolling in new rows (which wouldn't happen if the rows didn't
            #   overflow the viewport)

            # Ideally the model would just beginInsertRow on each new inserted
            # row instead of sending a single dummy beginInsertRow at the end,
            # but in the general case this defeats incremental row loading since
            # the model has no way of knowing when to stop calling
            # beginInsertRows, since it has no knowledge of visible rows

            for view in [self.table_view, self.list_view]:
                if (view.model().canFetchMore(QModelIndex())):
                    # XXX A simpler check would be the vertical scrollbar? If
                    #     there's scrollbar it means there are still rows to be
                    #     displayed?
                    #index = view.model().index(0, 1 if view is self.table_view else 0)
                    #rowHeight = view.visualRect(index).height()
                    rowHeight = view.rowHeight(0) if view is self.table_view else view.gridSize().height()
                    # rowHeight = max(1, view.rowHeight(0) if view is self.table_view else view.gridSize().height())
                    if (rowHeight == 0):
                        # Too early, ignore, will call again
                        logger.info("Too early, 0 rowheight")
                        break

                    min_loaded_rows = round(view.viewport().height() * 1.0 / rowHeight) + 1
                    # XXX Have a version of fetchMore that gets the number of
                    #     rows as parameter instead of looping here
                    while ((view.model().rowCount() < min_loaded_rows) and (view.model().canFetchMore(QModelIndex()))):
                        logger.info("Loading extra rows rowHeight %d min_loaded_rows %d rowCount %d ", 
                            rowHeight, min_loaded_rows, view.model().rowCount())
                        view.model().fetchMore(QModelIndex())


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
        
        enable_proxy_model_sorting = False
        if (enable_proxy_model_sorting):
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

    def sortByColumn(self, col, order):
        """
        Sort by column and order (Qt.AscendingOrder, Qt.DescendingOrder) if the
        same as current, toggle
        """
        logger.info("col %d order %s (0x%x)", col, EnumString(Qt, order), order)

        # Toggle if same column and order
        if ((col == self.model.sort_column) and (order == self.model.sort_order)):
            order = Qt.AscendingOrder if (self.model.sort_order == Qt.DescendingOrder) else Qt.DescendingOrder

        # There's a bug for which QHeaderView "forgets" column visibility when
        # sorting and the model is invalidated, restore
        # XXX This should hook into header.sectionClicked.connect(save_and_restore_hidden_columns)
        #     since the fix here won't fix it eg when clicking on column headers
        hidden = [i for i in range(self.model.columnCount()) if self.table_view.isColumnHidden(i)]

        self.table_view.sortByColumn(col, order)

        for i in hidden:
            self.table_view.setColumnHidden(i, True)

    def updateDirectoryLabel(self):
        logger.info("")
        # XXX Move the focusin/focusout setstyle here too
        if (self.search_mode):
            if (self.search_string != ""):
                self.directory_label.setEnabled(True)
                self.directory_label.setText("search: %s_" % self.search_string)
            else:
                # Display some search format rules as search placeholder See
                # https://www.voidtools.com/support/everything/searching/ (note
                # that filters and macros need 1.5 to work, so they are not
                # added here)
                # XXX Check version and add filter/macro example?
                # XXX Display this elsewhere?
                self.directory_label.setEnabled(False)
                self.directory_label.setText("sizedupe: dupe: !thumbs type:folder ext:jpg \"exact phrase\" <this | that>")

        else:
            # QLabel doesn't support elision, do poor man's elision
            # XXX Remove once the label supports relision
            elided_dir = self.model.file_dir
            max_length = 63
            # XXX Looks like file_dir is None at initialization, fix?
            if ((elided_dir is not None) and (len(elided_dir) > max_length)):
                elided_dir = elided_dir[:(max_length-3) / 2] + "..." + elided_dir[-(max_length-3) / 2:]
            self.directory_label.setEnabled(True)
            self.directory_label.setText(elided_dir)

        label_text = ("search:" + self.search_string) if self.search_mode else self.model.file_dir
        # Don't emit None as it will crash silently
        # XXX file_dir is None at initialization because of the two step
        #     initialization performed when starting the app, fix?
        self.directoryLabelChanged.emit(label_text or "")

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
            # Ignore for SHARE_ROOT, it's possible it confuses XP and takes a
            # long time to return
            # XXX Not clear, verify
            if (os_path_contains(SHARE_ROOT, self.file_dir)):
                drive = SHARE_ROOT
            else:
                drive = os.path.splitdrive(self.file_dir)[0]
                unc = os.path.splitunc(self.file_dir)[0]
                drive = unc if (drive == "") else (drive + "\\")
                try:
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
            # XXX Show the selected size in smaller units?
            locale.toString(selected_size / 2**10),
            locale.toString(total_size / 2**10),
            locale.toString(selected_files),
            locale.toString(total_files),
            locale.toString(selected_dirs),
            locale.toString(total_dirs)
        ))
        
        # The loading indicator is shown in the tab title, which takes from the
        # directory label, update so it emits the change and the main app
        # updates the tab
        # XXX Do this more fine grain so it only updates when start and
        #     stop the thread?
        self.updateDirectoryLabel()

        logger.info("Done")

    def rateLimitedUpdateSummary(self):
        qRateLimitCall(self.updateSummary, 500)

    def toggleSearchMode(self):
        logger.info("")
        self.search_mode = not self.search_mode
        if (self.search_mode):
            # XXX Stop overwriting file_dir
            self.old_file_dir = self.file_dir
            self.setSearchString(self.file_dir)

        else:
            # XXX Store the old search string?
            self.file_dir = self.old_file_dir
            self.setDirectory(self.file_dir)

    def resetSearchString(self):
        logger.info("")
        if (not self.search_mode):
            QToolTip.hideText()
            self.search_string = ""
            self.search_string_timer.stop()

    def setSearchString(self, search_string):
        old_search_string = self.search_string
        self.search_string = search_string
        if (self.search_string == ""):
            # In non-search mode, need to reset tooltip, etc
            self.resetSearchString()
            
        else:
            # Setting a new search string, refresh the thumbnail timer, and the
            # string in case it changed. Use an "infinite" display time and
            # manual hiding timer since there's no way to restart the default
            # QToolTip timer without hiding and showing the QTooltip which does
            # bad UX flash
            if (not self.search_mode):
                QToolTip.showText(
                    self.getActiveView().parentWidget().mapToGlobal(self.getActiveView().geometry().topLeft()), 
                    self.search_string, 
                    self, 
                    QRect(),
                    sys.maxint
                )
                self.search_string_timer.start(self.search_string_display_ms)
            
        if (self.search_mode):
            self.file_dir = search_string
            self.updateDirectoryLabel()
            qFindMainWindow().updateWindowTitle()
            # Don't redo the search if only a space was added, this makes
            # spacebar selection be less disruptive when search is on, while at
            # the same time allowing spaces in search strings
            if (old_search_string.rstrip() != self.search_string.rstrip()):
                qDebounceCall(self.searchEverything, 1000)

    def searchEverything(self):
        try:
            self.model.setSearchString(self.file_dir)
            
        except Exception as e:
            QMessageBox.critical(
                self, "Search Mode", "Can't switch to search mode, error '%s'" % e,
                buttons=QMessageBox.Ok,
                # Set it explicitly. Despite what docs say, the default is Yes
                defaultButton=QMessageBox.Ok
            )
            self.toggleSearchMode()
    
        #self.model.file_dir = self.file_dir
        #self.model.getFiles(False)
        # XXX In addition to missing tableview column resizing, the listview
        #     text is not eliding properly until the window is resized 
        # XXX This doesn't make a lot of sense since entries are still
        #     coming in, should be done at the end of receiving? It also needs
        #     to merge the size & extension cells on directories
        #self.table_view.horizontalHeader().setSectionResizeMode(1, QHeaderView.Stretch)
        #for i in xrange(4):
        #    self.table_view.horizontalHeader().setSectionResizeMode(i + 2, QHeaderView.ResizeToContents)

    def setupActions(self):
        # Override the default tableview copy action which only copies the
        # filename, with one that copies the full filepath
        self.copyFilepathsAct = QAction('Copy Filepaths', self, shortcut="ctrl+shift+c", triggered=self.copySelectedFilepaths, shortcutContext=Qt.WidgetWithChildrenShortcut)

        self.localsendFilesAct = QAction("Send via localsend", self, shortcut="ctrl+l", triggered=self.localsendSelectedFiles, shortcutContext=Qt.WidgetWithChildrenShortcut)

        self.copyFilesAct = QAction('Copy to Clipboard', self, shortcut="ctrl+c", triggered=self.copySelectedFiles, shortcutContext=Qt.WidgetWithChildrenShortcut)
        self.cutFilesAct = QAction('Cut to Clipboard', self, shortcut="ctrl+x", triggered=self.cutSelectedFiles, shortcutContext=Qt.WidgetWithChildrenShortcut)
        # XXX Have an option to ove to trash, shift+del vs. del?
        self.deleteFilesAct = QAction('Delete', self, triggered=self.deleteSelectedFiles, shortcutContext=Qt.WidgetWithChildrenShortcut)
        self.deleteFilesAct.setShortcuts(["del", "shift+del"])

        self.pasteFilesAct = QAction('Paste from Clipboard', self, shortcut="ctrl+v", triggered=self.pasteClipboardFiles, shortcutContext=Qt.WidgetWithChildrenShortcut)

        self.openDirAct = QAction('Open Directory', self, shortcut="ctrl+o", triggered=self.openDirectory, shortcutContext=Qt.WidgetWithChildrenShortcut)
        # XXX Network Directory could request a network address to download eg
        #     http:// and default to the Network pseudo directory
        self.networkDirAct = QAction('Network Directory', self, shortcut="ctrl+n", triggered= lambda : self.setDirectory(SHARE_ROOT), shortcutContext=Qt.WidgetWithChildrenShortcut)
        self.reloadDirAct = QAction('Reload Directory', self, shortcut="ctrl+r", triggered=lambda : self.reloadDirectory(), shortcutContext=Qt.WidgetWithChildrenShortcut)
        self.reloadAllAct = QAction('Reload Directory and Caches', self, shortcut="ctrl+shift+r", triggered=lambda : self.reloadDirectory(True), shortcutContext=Qt.WidgetWithChildrenShortcut)
        self.parentDirAct = QAction('Parent Directory', self, triggered=self.gotoParentDirectory, shortcutContext=Qt.WidgetWithChildrenShortcut)
        self.parentDirAct.setShortcuts(["backspace", "ctrl+PgUp"])
        self.childDirAct = QAction('Child Directory', self, shortcut="ctrl+PgDown", triggered=self.gotoChildDirectory, shortcutContext=Qt.WidgetWithChildrenShortcut)
        # XXX Missing PgDown to enter current directory
        self.prevDirectoryAct = QAction('Previous Directory', self, shortcut="alt+left", triggered=lambda : self.gotoHistoryDirectory(-1), shortcutContext=Qt.WidgetWithChildrenShortcut)
        self.nextDirectoryAct = QAction('Next Directory', self, shortcut="alt+right", triggered=lambda : self.gotoHistoryDirectory(1), shortcutContext=Qt.WidgetWithChildrenShortcut)
        self.chooseDirectoryAct = QAction('Choose Directory', self, shortcut="alt+down", triggered=self.chooseHistoryDirectory, shortcutContext=Qt.WidgetWithChildrenShortcut)
        self.calculateSubdirSizesAct = QAction('Calculate Subdirectory Sizes', self, shortcut="space", triggered=lambda : self.calculateSubdirSizes(self.getActiveView().currentIndex()), shortcutContext=Qt.WidgetShortcut)
        self.calculateAllSubdirsSizesAct = QAction('Calculate All Subdirectory Sizes', self, shortcut="alt+shift+return", triggered=lambda : self.calculateSubdirSizes(), shortcutContext=Qt.WidgetShortcut)

        self.sortByNameAct = QAction('Sort by name', self, shortcut="ctrl+F3", triggered=lambda : self.sortByColumn(1, self.model.sort_order), shortcutContext=Qt.WidgetWithChildrenShortcut)
        self.sortByDateAct = QAction('Sort by date', self, shortcut="ctrl+F5", triggered=lambda : self.sortByColumn(4, self.model.sort_order), shortcutContext=Qt.WidgetWithChildrenShortcut)
        self.sortBySizeAct = QAction('Sort by size', self, shortcut="ctrl+F6", triggered=lambda : self.sortByColumn(3, self.model.sort_order), shortcutContext=Qt.WidgetWithChildrenShortcut)

        self.toggleSearchModeAct = QAction('Toggle search mode', self, shortcut="ctrl+s", triggered=self.toggleSearchMode, shortcutContext=Qt.WidgetWithChildrenShortcut)

        self.createDirAct = QAction('Create Directory', self, shortcut="F7", triggered=self.createDirectory, shortcutContext=Qt.WidgetWithChildrenShortcut)
        
        # XXX Make this work with F6, right now F6 is at the app level to move
        #     to the next pane directory, but F6 should work for both and this
        #     should be shift+F6 in place editing?
        self.renameFileAct = QAction('Rename File', self, shortcut="F2", triggered=self.renameFile, shortcutContext=Qt.WidgetWithChildrenShortcut)

        self.increaseIconSizeAct = QAction('Increase Icon Size', self, shortcut="ctrl++", triggered=lambda : self.resizeIcons(16), shortcutContext=Qt.WidgetWithChildrenShortcut)
        self.decreaseIconSizeAct = QAction('Decrease Icon Size', self, shortcut="ctrl+-", triggered=lambda : self.resizeIcons(-16), shortcutContext=Qt.WidgetWithChildrenShortcut)
        
        self.switchViewAct = QAction("Switch View", self, shortcut="ctrl+i", triggered=self.switchView, shortcutContext=Qt.WidgetWithChildrenShortcut)

        self.selectAndAdvanceAct = QAction("Select and Advance", self, shortcut="insert", triggered=self.selectAndAdvance, shortcutContext=Qt.WidgetWithChildrenShortcut)
        self.invertSelectionAct = QAction("Invert Selection", self, shortcut="ctrl+b", triggered=self.invertSelection, shortcutContext=Qt.WidgetWithChildrenShortcut)
        self.selectAllOrClearAct = QAction("Select all/None", self, shortcut="ctrl+a", triggered=self.selectAllOrClear, shortcutContext=Qt.WidgetWithChildrenShortcut)

        self.openInExternalViewerAct = QAction("Open in External Viewer", self, shortcut="F3", triggered=self.openInExternalViewer, shortcutContext=Qt.WidgetWithChildrenShortcut)

        # XXX LineEdit with directory name, bookmarks/favorites/history combobox
        # XXX Allow filtering files by typing name
        
        self.addAction(self.copyFilepathsAct)
        self.addAction(self.copyFilesAct)
        self.addAction(self.cutFilesAct)
        self.addAction(self.deleteFilesAct)
        self.addAction(self.pasteFilesAct)
        self.addAction(self.localsendFilesAct)
        self.addAction(self.openDirAct)
        self.addAction(self.networkDirAct)
        self.addAction(self.reloadDirAct)
        self.addAction(self.reloadAllAct)
        self.addAction(self.parentDirAct)
        self.addAction(self.childDirAct)
        self.addAction(self.prevDirectoryAct)
        self.addAction(self.nextDirectoryAct)
        self.addAction(self.chooseDirectoryAct)
        # Only calculate directory sizes on the tableview, this also helps with
        # not highlighting when pressing space on the CheckableMenu
        self.table_view.addAction(self.calculateSubdirSizesAct)
        self.table_view.addAction(self.calculateAllSubdirsSizesAct)
        self.addAction(self.createDirAct)
        self.addAction(self.renameFileAct)
        self.addAction(self.increaseIconSizeAct)
        self.addAction(self.decreaseIconSizeAct)
        self.addAction(self.switchViewAct)
        self.addAction(self.selectAndAdvanceAct)
        self.addAction(self.invertSelectionAct)
        self.addAction(self.selectAllOrClearAct)
        self.addAction(self.openInExternalViewerAct)
        self.addAction(self.toggleSearchModeAct)
        self.addAction(self.sortByNameAct)
        self.addAction(self.sortByDateAct)
        self.addAction(self.sortBySizeAct)

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
            # Deselect ".."
            index = self.model.index(0,0)
            if (index.isValid() and (index.data(Qt.UserRole).filename == "..")):
                selection_model = self.getActiveView().selectionModel()
                selection_model.select(index, QItemSelectionModel.Deselect | QItemSelectionModel.Rows)
        
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
        # Deselect ".."
        index = self.model.index(0,0)
        if (index.isValid() and (index.data(Qt.UserRole).filename == "..")):
            selection_model = self.getActiveView().selectionModel()
            selection_model.select(index, QItemSelectionModel.Deselect | QItemSelectionModel.Rows)
    
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
        def cleanup_temp_file(temp_relpath, filepath):
            logger.info("%r %r", temp_relpath, filepath)
            def remove_leaf(relpath):
                # XXX What if two instances of the program, both
                #     uncompressed the same file?
                # relpath can be empty the first time if the file was
                # already in the temp root
                logger.info("%r", relpath)
                if (relpath != ""):
                    abspath = os.path.join(TEMP_DIR, relpath)
                    logger.info("Removing dir %r %r", abspath, relpath)
                    try:
                        os.rmdir(abspath)
                        relpath = os.path.dirname(relpath)
                        remove_leaf(relpath)
                    except Exception as e:
                        # The directory was not empty, done
                        logger.info("exception %r", e)
            logger.info("Removing %r", filepath)
            os.remove(filepath)
            # Can't use os.removedirs since the deletion needs to stop at
            # TEMP_DIR
            remove_leaf(os.path.dirname(temp_relpath))
        
        file_info = self.getActiveView().currentIndex().data(Qt.UserRole)
        filename = file_info.filename

        if (fileinfo_is_dir(file_info)):
            # Ignore on directories
            logger.info("Ignoring on directory %r", filename)
            return

        # XXX Implement a default extract that returns the filepath, then check
        #     if the filepath is the same as provided and don't schedule a cleanup?
        if (self.model.needsExtracting()):
            filepath = self.model.it.extract(os.path.join(self.file_dir, filename))
            if (filepath is not None):
                p = QProcess(self)
                arguments = ["/S=L", filepath]
                # XXX At least on Windows when the app closes it doesn't kill this
                #     process, and the temp file and path remains, needs a periodic
                #     cleanup?
                temp_relpath = os.path.relpath(filepath, TEMP_DIR)
                p.finished.connect(lambda : cleanup_temp_file(temp_relpath, filepath))
                p.start(g_external_viewer_filepath, arguments)
            else:
                QMessageBox.warning(
                    self, "View File", "Error viewing file '%r'" % filename,
                    buttons=QMessageBox.Ok,
                    # Set it explicitly. Despite what docs say, the default is Yes
                    defaultButton=QMessageBox.Ok
                )

        else:
            filepath = os.path.abspath(os.path.join(self.file_dir, filename))
            arguments = ["/S=L", filepath]
            # Start detached will create an independent process instead of a child
            QProcess().startDetached(g_external_viewer_filepath, arguments)
            
    def resizeIcons(self, delta):
        logger.info("%d + %d", self.display_width, delta)
        new_width = max(64, self.display_width + delta)
        if (new_width != self.display_width):
            if (use_delegate):
                self.display_width = new_width
                self.list_view.itemDelegate().setWidth(self.display_width)
                self.list_view_style.setWidth(self.display_width)
                
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

        if (hasattr(self.model.it, "mkDir")):
            dirpath = os.path.join(self.file_dir, text)
            self.model.it.mkDir(dirpath)
            self.reloadDirectory()

        else:
            try:
                os.mkdir(os.path.join(self.file_dir, text))
                
                if (self.model.watcher is None):
                    self.reloadDirectory()

                else:
                    # Sleep a bit for the directory to be created and the reload to
                    # happen
                    
                    # XXX Do it in a better way? But this is not like the full
                    #     directory scan, could force a reload even if a watcher is
                    #     set?
                    logger.info("Sleeping to give time for reload to happen")
                    time.sleep(0.01)
                    logger.info("Processing signals")
                    qApp.processEvents()

                row = self.model.findFileInfoRow(text)
                if (row != -1):
                    index = self.model.index(row, 0)
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
                if (self.model.watcher is None):
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
            # XXX Set the next entry in the history as the current index
            #     (already done when going backwards, needs doing when going
            #     forward)

    def chooseHistoryDirectory(self):
        logger.info("")
        menu = EditablePopupMenu(self.parent(), allow_check=False, allow_delete=True)
        for i, history_entry in enumerate(reversed(self.dir_history)):
            # XXX Skip duplicated entries?
            # XXX Allow ctrl+ to goto in a new tab? Needs to move method to app
            i = len(self.dir_history) - i - 1
            action = menu.addAction(history_entry, i, True)
            action.setCheckable(True)
            action.setChecked(i == self.current_dir_history)
        menu.addSeparator()
        openAct = menu.addAction("Open...")
        clearAct = menu.addAction("Clear all")
        
        action = menu.exec_(self.directory_label.mapToGlobal(self.directory_label.rect().bottomLeft()))
        if (action is openAct):
                self.openDirectory()
                
        elif (action is clearAct):
            self.dir_history = [self.dir_history[self.current_dir_history]]
            self.current_dir_history = 0
            menu.deleted_datas = []

        elif (action is not None):
            self.gotoHistoryDirectory(action.data() - self.current_dir_history)

        # Delete history entries, last first to preserve index validity
        for history_index in sorted(menu.deleted_datas, reverse=True):
            del self.dir_history[history_index]

    def isForciblyBrowsable(self, file_info):
        """
        Used for
        - Force browsing (gotoChildDirectory)
        """
        
        return (self.isBrowsable(file_info) or
            any([file_info.filename.lower().endswith(ext) for ext in PACKER_EXTENSIONS])
        )

    def isBrowsable(self, file_info):
        """
        Used for
        - Enter (ItemActivate)
        - Calculate dir sizes
        - Left to right
        """
        # XXX Move this to the model since it also needs something like this for
        #     calculating dir sizes, or if file_info.filename is guaranteed to
        #     be absolute then can have a fileinfo_is_browsable?
        return (fileinfo_is_dir(file_info) or zipfile.is_zipfile(os.path.join(self.file_dir, file_info.filename)))

    def gotoChildDirectory(self):
        """
        - If the current index is forcibly browsable, goto its child "directory"
        - Otherwise, if in search mode, goto the parent directory and focus on
          the file
        """
        file_info = self.getActiveView().currentIndex().data(Qt.UserRole)
        logger.info("%r", file_info)
        if ((file_info is not None) and ((self.isForciblyBrowsable(file_info)) or self.search_mode)):
            # XXX This is replicated in itemactivated, refactor?
            if (self.search_string_timer.isActive()):
                logger.info("Resetting search_string")
                self.search_string_timer.stop()
                self.search_string_timer.timeout.emit()
            if (self.isForciblyBrowsable(file_info)):
                logger.info("Navigating to child %r", file_info.filename)
                # Use normpath, translate .. into parent
                dirpath = os.path.normpath(os.path.join(self.file_dir, file_info.filename))

            else:
                logger.info("Navigating to parent %r", file_info.filename)
                dirpath = os.path.dirname(os.path.normpath(os.path.join(self.file_dir, file_info.filename)))
                # XXX Missing focusing on the file

            self.setDirectory(dirpath)
            
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

        # Ignore on ".."
        if (index.isValid() and (index.data(Qt.UserRole).filename == "..")):
            return

        view = self.getActiveView()
        if ((view == self.table_view) and (not view.selectionModel().isSelected(index))):
            self.model.calculateSubdirSizes(index)

        # If the index points to a valid file/dir on any view, toggle
        # XXX Toggling is the default spacebar behavior, should it just reject
        #     the event so the default code runs in addition to calculating the
        #     dir size? What if the shortcut is ever changed?
        if (index.isValid()):
            view.selectionModel().select(index, QItemSelectionModel.Toggle | QItemSelectionModel.Rows)
    
    def setDirectory(self, file_dir, add_to_history = True):
        logger.info("%r %s", file_dir, add_to_history)

        # It's possible the directory is not listable, find a parent that is
        # (this can happen if eg the directory was navigated to through search)
        
        # XXX This doesn't work on windows because it doesn't honor the X_OK
        #     access flag to signify that a directory can be listed, it will
        #     return True if the directory entry can be read (meaning listing
        #     the parent would be valid) and display an empty dir. Needs to be
        #     trapped at directory listing time. The alternative of using
        #     os.listdir is an unnecessary penalty on slow drives for the common
        #     case
        # XXX In addition, this breaks SHARE_ROOT access and virtual path
        #     archive access, disabled
        while (not os.access(file_dir, os.X_OK)) and False:
            parent_dir = os.path.dirname(file_dir)
            if (parent_dir == file_dir):
                break
            file_dir = parent_dir

        old_file_dir = self.file_dir

        # Disable search mode
        # XXX Should search strings be pushed to history?
        if (self.search_mode):
            self.search_mode = False
            # Reset the search string
            self.search_string_timer.stop()
            self.search_string_timer.timeout.emit()

        self.file_dir = file_dir
        # XXX This should use a signal instead of hijacking the main window
        qFindMainWindow().updateWindowTitle()
        self.updateDirectoryLabel()
        
        # Don't add identical consecutive entries (can happen with left to
        # right, ctrl+d to the same dir, etc)
        if (add_to_history and ((len(self.dir_history) == 0) or (self.dir_history[self.current_dir_history] != file_dir))):
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
        # The model already updates the summary when rows are added/deleted, but
        # if no rows were added/deleted still need to update the loading
        # indicator when the thread ends.
        self.model.directoryReader.finished.connect(self.rateLimitedUpdateSummary)
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
        if (hasattr(index.model().it, "executeFile")):
            # WFX plugin support
            
            # verb can be "open", "properties" or "chmod"
            hwnd = qFindMainWindow().winId().__int__()
            verb = "open"
            
            # Prepend directory and normalize to translate .. into parent
            filepath = os.path.normpath(os.path.join(self.file_dir, filename))
            # Normalization can add a trailing slash when going up to the
            # parent, remove
            if ((filepath.endswith("\\") and (filepath != "\\"))):
                filepath = filepath[:-1]
            
            # XXX This needs to return the modified remote string
            res = index.model().it.executeFile(hwnd, filepath, verb)
            FS_EXEC_SYMLINK  = -2
            FS_EXEC_YOURSELF = -1
            # XXX ftp.wfx FsExecuteFileW returns for both <Add connection> and
            #     <Quick connection> but the code looks like it should treturn
            #     FS_EXEC_SYMLINK or FS_EXEC_OK
            
            # XXX davplug returns FS_EXEC_YOURSELF for directories (created
            #     connections, quick connection directory)
            if ((res == FS_EXEC_SYMLINK) or (res == FS_EXEC_YOURSELF)):
                # This is returned in sftpplug when activating a saved connection
                # Follow remote name
                self.setDirectory(filepath)
                
        elif (self.isBrowsable(file_info)):
            dirpath = os.path.normpath(os.path.join(self.file_dir, filename))
            self.setDirectory(dirpath)
  
        else:
            # XXX Unicode chars fail
            
            # XXX Make this work for files inside archives in a similar way to
            #     openInExternalViewer does. Unfortunately, openUrl doesn't
            #     return the process so automatic cleanup at finished() time
            #     cannot be done, and there's no cross platform facility to
            #     obtain the associated application process/command line. 
            #
            #     Can be launched by QProcess.start("cmd.exe", ["/C" "start"] ...) but
            #     then the process returned is cmd, not the started app. The
            #     solution is to either always offer an "open in background,
            #     close when done" or to invoke ShellExecuteEx using ctypes
            #     which does return the started process. Note that if the
            #     process is multifile and closes the file without closing the 
            #     process, it will still need the background approach.

            # XXX Interestingly, on Windows you can pass files inside a zip
            #     archive using the .zip\subdirectory\file naming convention to
            #     qLaunchWithPreferredApp (this even works from a cmd.exe start
            #     .zip\subdir\file). This doesn't work for eg .rar archives
            filepath =os.path.join(self.file_dir, filename)
            qLaunchWithPreferredApp(filepath)
            #p = QProcess(self)
            #p.finished.connect(lambda : logger.info("Process for %r finished", filepath))
            #process = p.start("cmd.exe", ["/C", "start", filepath])

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
            self.directory_label.setStyleSheet("text-align: left;")

        elif (event.type() == QEvent.FocusIn):
            color = QColor()
            color.setNamedColor("#cceeff")
            color = color.darker(125)
            self.directory_label.setStyleSheet("text-align: left; background-color: %s" % color.name()) 
            # XXX This should use a signal instead of hijacking the main window
            qFindMainWindow().updateWindowTitle()
        
        elif ((source is self.directory_label) and (event.type() == QEvent.MouseButtonRelease)):
            # XXX Do chooseBookmark if right click
            self.chooseHistoryDirectory()

        elif ((event.type() == QEvent.KeyPress) and (self.search_string != "") and 
              ((event.key() in [Qt.Key_Backspace] + ([] if self.search_mode else [Qt.Key_Up, Qt.Key_Down])))):
            # Allow minimal editing of the search string, navigation of hits up
            # and down

            # XXX Implement undo and allow ctrl+z?
            # XXX Implement copy/paste/selection?
            
            # XXX Navigating the matches with up and down is intuitive but far
            #     from the home row, another option is to use Enter/shift-Enter,
            #     but that may cause erroneous directory switches if pressed
            #     when the timer just expired. Show the tip until ESC is pressed
            #     or the string is deleted instead of using a timer?

            # Edit the string
            search_string = self.search_string
            if (event.key() == Qt.Key_Backspace):
                # Delete one word if ctrl is pressed, make "word1 word2" turn
                # into "word1 " and "word1 " turn into ""
                # XXX Allow any non alpha non number as word separator?
                if (event.modifiers() & Qt.ControlModifier):
                    i = rindex_of(search_string[:-1], " ")
                    if (i == -1):
                        search_string = ""
                    else:
                        search_string = search_string[:i+1]

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
              (
                  # Do space shortcut (selection) if search string is empty
                  # (other heuristics like already having a space are bad UX
                  # because if there's an item with space then the cursor moves
                  # and can no longer select the desired item, and if therer are
                  # no files with space, then space won't be accepted and never
                  # part of the search string)

                  ((event.key() == Qt.Key_Space) and (
                      # In non search mode, deleting the search string to be
                      # able to mark is ok, adding a space is not always
                      # possible 
                      ((self.search_string != "") and (not self.search_mode)) or
                      # In search mode, deleting the search string to be able to
                      # mark in perturbs the list, but adding a space is ok
                      ((not self.search_string.endswith(" ")) and (self.search_mode))
                  )) or 
                  # Do backspace shortcut (parent dir) if search string is empty
                  ((event.key() == Qt.Key_Backspace) and (self.search_string != ""))
              )
            ):
            # Prevent a few shortcuts to be used when editing the search_string
            # and accept the override, this will re-send they key event to the
            # child, which will be used below for the search_string
            event.accept()
            
        elif ((event.type() == QEvent.KeyPress) and 
              # event.text() returns empty for cursor, etc which triggers the
              # "in" clause, ignore
              ((event.text() != "") and (event.text() in (string.digits + string.letters + string.punctuation + " "))) and
              # Only allow spacebar on non empty string, so it still works as
              # selection toggle
              ((event.text() != " ") or ((self.search_string != "") and (not self.search_string.endswith(" "))))
            ):
            # The default behavior performs prefix search and selects the item,
            # perform substring search, don't select, display search string
            # on tooltip, allow backspace editing and navigating matches
            logger.info("Key %d text %r", event.key(), event.text())
            key = event.text().lower()

            search_string = self.search_string + key

            if (self.search_mode):
                # Allow search strings that don't return any indices, since a
                # partially constructed may when fully constructed return
                # indices (eg when using advanced filtering like ext:jpg)
                self.setSearchString(search_string)

            else:
                # Don't bother setting a string that is not in the listed items

                # Now search for a cell containing the typed string as a substring
                # XXX This should start searching on the current row, wrap
                #     around if not found
                current_row = self.getActiveView().currentIndex().row()
                rowCount = self.model.rowCount()
                for row in xrange(self.model.rowCount()):
                    # Set the current index to the matching cell
                    
                    index = self.createRootIndex((row + current_row) % rowCount)
                    filename = index.data(Qt.UserRole).filename.lower()
                    
                    # Check if the cell contains the typed substring (case insensitive)
                    # XXX Go to the next if this is already current?
                    # XXX Clear typed text on non alpha key (eg after pressing return)?
                    if (search_string in filename):
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

            # Reset the search string if there was any, ESC is the fast way of
            # switching from search mode to navigation mode without waiting for
            # the search_string_timer to expire
            self.resetSearchString()
        
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
        
    def openDirectory(self):
        logger.info("Requesting new directory default is %r", self.file_dir)
        # XXX Disable the action when use_everything? or just switch back to
        #     directory mode? Note this is also called explicitly, so disabling
        #     the action is not enough, also needs to be ignored here
        # XXX Have openDirectory use the header bar to type the new directory
        #     instead of popping a dialog box? (but the dialog box is a
        #     directory dialog box which is sometimes convenient, also the
        #     header would need better editing support)
        if (not self.search_mode):
            file_dir = qGetExistingDirectory(None, "Select Folder", self.file_dir)
            if (file_dir != ""):
                self.setDirectory(file_dir)

    def reloadDirectory(self, clear_cache=False):
        logger.info("clear_cache %s", clear_cache)
        # XXX This doesn't update the view sometimes, eg move a file into an
        #     empty directory and the directory will still show empty. Investigate
        self.model.reloadDirectory(clear_cache)
        # The model already updates the summary when rows are added/deleted, but
        # if not rows were added/deleted still need to update the loading
        # indicator when the thread ends.
        self.model.directoryReader.finished.connect(self.rateLimitedUpdateSummary)
        # Update unconditionally in case the reader finished before setting the
        # connect above (can't move the connect to the thread creation because 
        # the model should have no knowledge of views)
        self.updateSummary()

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
                    # XXX Missing handling directories
                    destination_path = os.path.join(current_directory, os.path.basename(source_path))

                    if (os.path.exists(destination_path) and (reply != QMessageBox.YesAll)):
                        if (reply == QMessageBox.NoAll):
                            continue
                        reply = QMessageBox.question(
                            self,
                            "Paste File",
                            "'%s' already exists, overwrite?" % os.path.basename(destination_path),
                            QMessageBox.Yes | QMessageBox.YesAll | QMessageBox.No | QMessageBox.NoAll | QMessageBox.Cancel,
                            QMessageBox.Cancel
                        )
                        if (reply == QMessageBox.Cancel):
                            break
                        if (reply in [QMessageBox.No, QMessageBox.NoAll]):
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
            
            if (self.model.watcher is None):
                self.reloadDirectory()

        else:
            logger.info("No files found in the clipboard.")


    def getSelectedFilepaths(self, strict=False):
        """
        Return selected filepaths or the current one if no selections and not
        strict
        """
        logger.info("")
        selected_filepaths = [os.path.join(self.file_dir, index.data(Qt.UserRole).filename) for index in self.getActiveView().selectionModel().selectedRows()]
        if ((len(selected_filepaths) == 0) and (not strict)):
            selected_filepaths = [os.path.join(self.file_dir, self.getActiveView().currentIndex().data(Qt.UserRole).filename)]

        return selected_filepaths

    def localsendSelectedFiles(self):
        logger.info("")

        view = self.getActiveView()
        index = view.currentIndex()
        if (view is not self.list_view):
            index = index.sibling(index.row(), view.model().columnCount()-1)
        pos = view.visualRect(index).topRight()

        if (not index.isValid()):
            return

        devices = g_localsend_devices
        global g_localsend_myinfo
        myinfo = g_localsend_myinfo
        do_discovery = (len(devices) == 0)
        while True:
            if (do_discovery):
                # XXX This msgbox causes the override cursor to be ignored? Do a really
                #     cancellable dialog box, localsend_discover_devices is just
                #     sleeping for the worker thread to end anyway, so have the function
                #     return the thread and pass in the devices
                # Use NoIcon so there's no sound when showing the messagebox
                msg_box = QMessageBox(QMessageBox.NoIcon, "Localsend Files", "Discovering devices...", QMessageBox.Cancel, self)
                msg_box.show()

                # Process events so the message box repaints fully
                qApp.processEvents()

                qApp.setOverrideCursor(Qt.WaitCursor)
                # Can take 2-3s to receive a response, use at least 5 seconds of
                # timeout
                # XXX Right now myinfo has a dynamic uuid, it should be constant and
                #     stored somewhere
                # XXX Store discovered device information, only rerun discovery if
                #     transfer fails
                # XXX Pass a list of trusted devices, implement trust on first use,
                #     allow
                # XXX This should pass the existing g_localsend_myinfo
                devices, myinfo = localsend_discover_devices(10)
                qApp.restoreOverrideCursor()

                g_localsend_myinfo = myinfo
                for device in devices:
                    # If the device is found, replace it in case it was found
                    # with a different ip, otherwise append
                    i = index_of([d.host for d in g_localsend_devices], device.host)
                    if (i != -1):
                        g_localsend_devices[i] = device
                    else:
                        g_localsend_devices.append(device)

                msg_box.close()

            # XXX There's no need for this dialog box since the popup has an
            #     option to discover again and to cancel?

            # XXX Keep listening while this popup is up? Actually have a
            #     cancellable message box with the instructions and listen all
            #     the time, but when to stop? Show the devices as they come and
            #     let the user stop when the desired one appears?
            if (len(g_localsend_devices) == 0):
                res = QMessageBox.warning(
                    self, "Localsend Files", 
                    "Can't find Localsend devices to send to." +
                    " Try again while at the same time, either:\n" +
                    "- closing the Localsend app / stop the server on the local device\n" + 
                    "- restarting the Localsend app on the target device\n" +
                    "- refreshing the nearby devices on the target device Localsend app\n" + 
                    "Retry?",
                    buttons=QMessageBox.Yes|QMessageBox.No|QMessageBox.Cancel,
                    # Set it explicitly. Despite what docs say, the default is Yes
                    defaultButton=QMessageBox.Yes
                )
                if (res != QMessageBox.Yes):
                    return
                do_discovery = True
            
            else:

                # Set the menu to the parent so the FilePane spacebar shortcut
                # doesn't override checking via spacebar
                # XXX spacebar still highlights the filepane instead of checking
                #     the menu option no matter parent() is used or
                #     qFindMainWindow() until cursors are pressed, fix

                # XXX Limit the shortcut at creation time to the table? (the
                #     listview shouldn't have it either anyway)
                menu = EditablePopupMenu(self.parent(), allow_delete=True)
                # XXX This ignores the configuration, fix
                g_localsend_myinfo = myinfo
                for device in g_localsend_devices:
                    # Localsend uses the lowest byte of the IP as #id, display the same,
                    # see https://github.com/localsend/protocol/issues/30
                    action = menu.addAction("%s #%s (%s)" % (device.alias, device.host.split(".")[-1], device.deviceModel), device, True)
                    action.setCheckable(True)
                    action.setChecked(False)
                menu.addSeparator()
                discoverAct = menu.addAction("Discover Devices")
                
                action = menu.exec_(view.viewport().mapToGlobal(pos))

                for device in menu.deleted_datas:
                    g_localsend_devices.remove(device)
                
                logger.info("Focus widget is %r", self.focusWidget())
                # XXX This doesn't focus back on the table when done,
                #     investigate and do it manually by now. focusWidget()
                #     reports the FileTableView is focusWidget, and navigating
                #     via cursor reports rows are being focused, but there's no
                #     highlighted row and the directory label is not highlighted
                #     either
                self.getActiveView().setFocus(Qt.PopupFocusReason)
                logger.info("Focus widget is %r", self.focusWidget())
                if (action is None):
                    break

                elif (action is discoverAct):
                    do_discovery = True

                else:
                    # Pressing enter on an action to dismiss the menu toggles
                    # the check, so
                    # - If the only checked action is the selected one, this
                    #   behaves like a regular popup menu
                    # - If there are more than one checked actions, ignore the
                    #   selected action
                    devices = []
                    for a in menu.actions():
                        if ((a is not action) and (a.isChecked())):
                            devices.append(a.data())

                    # No non-selected actions are checked
                    if ((len(devices) == 0) or (not action.isChecked())):
                        devices.append(action.data())
                    
                    
                    for device in devices:
                        # XXX Send multiple files in one call, but what about directories?
                        for filepath in self.getSelectedFilepaths():
                            # XXX Needs dealing with directories, recurse and send name
                            #     with relative path?
                            if (not os.path.isdir(filepath)):
                                while (True):
                                    logger.info("Localsending %r to %r", filepath, device)
                                    # XXX Allow canceling this/all
                                    # XXX This will fail if device needs to approve (eg
                                    #     "save media to gallery" is set), with "Could not
                                    #     save file. Check receiving device for more
                                    #     information.", guard against that and offer retry? 
                                    #     See https://github.com/localsend/localsend/issues/1591
                                    qApp.setOverrideCursor(Qt.WaitCursor)
                                    try:
                                        localsend_upload_to_device(myinfo, device, filepath)
                                        
                                    except Exception as e:
                                        # XXX This should have yes to all no
                                        #     to all in case of multiple
                                        #     files/failed devices?
                                        res = QMessageBox.warning(
                                            self, "Localsend Files", 
                                            "Exception %r sending %r to device %s. Make sure the localsend app is running.\nRetry?" % 
                                            (e, os.path.basename(filepath), device.alias),
                                            buttons=QMessageBox.Yes|QMessageBox.No|QMessageBox.Cancel,
                                            # Set it explicitly. Despite what docs say, the default is Yes
                                            defaultButton=QMessageBox.Yes
                                        )
                                        if (res == QMessageBox.Yes):
                                            continue
                                    
                                    finally:
                                        qApp.restoreOverrideCursor()

                                    break
                                        
                    break
            
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

    def cutOrCopySelectedFiles(self, cut = False):
        # XXX Do something to gray out if cutting? (note the file doesn't really
        #     get cut until copied elsewhere so there's no point in refreshing
        #     the database here). The watcher will refresh when done and remove,
        #     would also need to watch the clipboard to refresh in case the cut
        #     never happens
        
        # XXX Set the Qt::Itemflags to IsEnabled to False and hope the default
        #     delegate observes the flag?
        filepaths = self.getSelectedFilepaths()

        action = "Cut" if cut else "Copy"
        if ((len(filepaths) > 0) and (not self.checkOperation("%s Files" % action))):
            # XXX Implement copy or cut archives to clipboard
            return
        
        logger.info("%sing files %r", action, filepaths)
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
        self.cutOrCopySelectedFiles()

    def cutSelectedFiles(self):
        self.cutOrCopySelectedFiles(True)

    def checkOperation(self, title):
        """
        Check if this model doesn't need file extracting, display a message box
        otherwise and return False
        """
        logger.info("%s", title)
        if (self.model.needsExtracting()):
            QMessageBox.warning(
                self, title, title[0] + title.lower()[1:] + " in archives not implemented yet",
                buttons=QMessageBox.Ok,
                # Set it explicitly. Despite what docs say, the default is Yes
                defaultButton=QMessageBox.Ok
            )
            return False
        return True
    
    def deleteSelectedFiles(self):
        logger.info("")
        if (not self.checkOperation("Delete Files")):
            # XXX Implement deleting from archives
            return
        
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
                    logger.error("Unable to delete file %r %s", filepath, e)

            elif (reply == QMessageBox.Cancel):
                break
        
        if (self.model.watcher is None):
            self.reloadDirectory()


class TwinWindow(QMainWindow):
    def __init__(self, left_file_dir=None, right_file_dir=None):
        global g_localsend_myinfo
        global g_external_viewer_filepath
        global g_external_diff_filepath

        super(TwinWindow, self).__init__()
        
        # XXX Forcing ini file for the time being for ease of debugging and
        #     tweaking, eventually move to native
        self.settings = QSettings('twin.ini', QSettings.IniFormat)

        self.setupActions()

        self.profiling = False
        
        splitter = QSplitter(Qt.Horizontal)
        self.splitter = splitter
        
        # XXX Missing setting different accent color to match directory accent
        #     color?
        # XXX Missing tab reordering via drag and drop
        self.left_tab = QTabWidget(self)
        self.right_tab = QTabWidget(self)

        for tab in [self.left_tab, self.right_tab]:
            def activate_and_choose_tab(tab, pos):
                # XXX Pass the tab to chooseTab instead of activating the tab,
                #     but it's a UI handler so it needs to be done in a way that
                #     doesn't capture a possible handler parameter instead of
                #     the tab to use
                tab_bar = tab.tabBar()
                tab_index = tab_bar.tabAt(pos)
                if (tab_index == -1):
                    return  # Clicked outside any tab
                    
                active_tab = self.left_tab if self.getLeftPane() is self.getActivePane() else self.right_tab
                if (tab is not active_tab):
                    self.getTargetPane().getActiveView().setFocus()

                tab.setCurrentIndex(tab_index)

                self.chooseTab()

            tab.tabBar().setContextMenuPolicy(Qt.CustomContextMenu)
            tab.tabBar().customContextMenuRequested.connect(lambda pos, tab=tab: activate_and_choose_tab(tab, pos))

            splitter.addWidget(tab)
            # XXX Only on 5.4+ 
            # tab.setTabBarAutoHide(True)
            # Don't elide, just scroll since it exhibits better UX
            #tab.setElideMode(Qt.ElideMiddle)

        self.left_panes = []
        self.right_panes = []

        # Recreate left and right tabs, restore dirs after the app has shown
        
        # XXX This two-step creation causes parts of the code to receive None
        #     file_dir like updateDirectoryLabel which until worked around would
        #     cause a silent crash in directoryLabelChanged emitting None, maybe
        #     others fix?
        settings = self.settings
        file_dirs_panes = []

        # Root items on ini files will go in the "General" group, trying to use
        # "general" as a group will be escaped into "#general". Just use the
        # root group for simplicity
        current_pane = settings.value("current_pane", "left")

        self.setGeometry(settings.value("window_geometry", QRect(0,0,1024,768)))

        g_external_viewer_filepath = settings.value("external_viewer_filepath", g_external_viewer_filepath)
        g_external_diff_filepath = settings.value("external_diff_filepath", g_external_diff_filepath)

        # Note QSettings child/key enumeration doesn't guarantee a specific
        # order, use beginWriteArray/beginReadArray for all settings that
        # require preserve ordering (bookmarks, tabs, history, etc)

        self.bookmarks = []
        count = settings.beginReadArray("bookmarks")
        for i in xrange(count):
            settings.setArrayIndex(i)
            self.bookmarks.append(settings.value("dirpath"))
        settings.endArray()

        for tab_name in ["left", "right"]:
            settings.beginGroup(tab_name)
            tab = self.left_tab if (tab_name == "left") else self.right_tab 

            count = settings.beginReadArray("tabs")
            for i in xrange(count):
                logger.info("Restoring tab %s pane %s", tab_name, i)
                settings.setArrayIndex(i)
                file_dir = settings.value("dirpath")
                display_width = int(settings.value("display_width", DISPLAY_WIDTH))
                file_pane = self.createPane(
                    tab, 
                    display_width, 
                    int(settings.value("sort_column", 1)), 
                    int(settings.value("sort_order", Qt.AscendingOrder))
                )

                if (settings.value("mode") == "thumbnails"):
                    file_pane.switchView()

                count = settings.beginReadArray("history")
                for j in xrange(count):
                    logger.info("Restoring tab %s pane %s history %s", tab_name, i, j)
                    settings.setArrayIndex(j)
                    file_pane.dir_history.append(settings.value("dirpath"))
                settings.endArray()
                
                file_pane.current_dir_history = int(settings.value("current_history", 0))
                file_dirs_panes.append((file_dir, file_pane))

            settings.endArray()

            i = int(settings.value("current_tab", 0))
            tab.setCurrentIndex(i)

            settings.endGroup()

        settings.beginGroup("localsend")
        count = settings.beginReadArray("devices")
        for i in xrange(count):
            settings.setArrayIndex(i)
            device = settings.value("json")
            device = json.loads(device)
            g_localsend_devices.append(LocalsendDevice(**device))
        settings.endArray()
        myinfo = settings.value("myinfo", None)
        if (myinfo is not None):
            g_localsend_myinfo = json.loads(myinfo)
        settings.endGroup()
        
        if ((len(self.left_panes) == 0) and (left_file_dir is None)):
            left_file_dir = os.getcwd()

        if ((len(self.right_panes) == 0) and (right_file_dir is None)):
            right_file_dir = os.getcwd()

        if (left_file_dir is not None):
            tab = self.left_tab
            file_pane = self.createPane(tab)
            file_dirs_panes.append((left_file_dir, file_pane))
            
        if (right_file_dir is not None):
            tab = self.right_tab
            file_pane = self.createPane(tab)
            file_dirs_panes.append((right_file_dir, file_pane))
            
        central_widget = splitter
        self.setCentralWidget(central_widget)

        self.updateWindowTitle()

        self.show()

        # Set the directories after showing the app so the FilePane loading
        # directory dialog boxes show on top of the app window and not out of
        # nowhere
        for file_dir, file_pane in file_dirs_panes:
            if (file_dir.startswith("search:")):
                # XXX Set this in setSearchString
                file_pane.search_mode = True
                file_pane.old_file_dir = os.getcwd()
                file_pane.setSearchString(file_dir[len("search:"):])

            else:
                file_pane.setDirectory(file_dir, False)

        if (current_pane == "left"):
            self.getLeftPane().getActiveView().setFocus()
        else:
            self.getRightPane().getActiveView().setFocus()
        
        logger.info("App font %s pointSize %d height %d", qApp.font().family(), qApp.font().pointSize(), qApp.fontMetrics().height())

    def updateWindowTitle(self):
        self.setWindowTitle("Twin - %s" % self.getActivePane().file_dir)
        
    def setupActions(self):
        
        self.nextPaneAct = QAction("Next Pane", self, shortcut="tab", triggered=self.nextPane)

        self.leftToRightAct = QAction("Left to Right", self, shortcut="ctrl+right", triggered= lambda : self.leftToRight())
        self.rightToLeftAct = QAction("Right to Left", self, shortcut="ctrl+left", triggered= lambda: self.leftToRight(True))

        self.copySelectedFilesAct = QAction("Copy Files", self, shortcut="F5", triggered=self.copySelectedFiles, shortcutContext=Qt.ApplicationShortcut)
        self.moveSelectedFilesAct = QAction("Move Files", self, shortcut="F6", triggered=self.moveSelectedFiles, shortcutContext=Qt.ApplicationShortcut)

        self.diffDirsAct = QAction("Diff Directories", self, shortcut="ctrl+m", triggered=self.diffDirectories, shortcutContext=Qt.ApplicationShortcut)
        self.diffExternallyAct = QAction("Diff with External Tool", self, shortcut="ctrl+shift+m", triggered=self.diffExternally, shortcutContext=Qt.ApplicationShortcut)

        self.swapPanesAct = QAction("Switch Panes", self, shortcut="ctrl+u", triggered=self.swapPanes, shortcutContext=Qt.ApplicationShortcut)

        self.chooseBookmarkAct = QAction('Choose Bookmark', self, shortcut="ctrl+d", triggered=self.chooseBookmark, shortcutContext=Qt.ApplicationShortcut)
        
        self.newTabAct = QAction("New Tab", self, shortcut="ctrl+t", triggered=self.chooseTab, shortcutContext=Qt.ApplicationShortcut)
        self.closeTabAct = QAction("Close Tab", self, triggered=self.closeTab, shortcutContext=Qt.ApplicationShortcut)
        self.closeTabAct.setShortcuts(["ctrl+w", "ctrl+shift+t"])

        self.profileAct = QAction("Profile", self, shortcut="ctrl+p", triggered=self.profile, shortcutContext=Qt.ApplicationShortcut)

        # XXX LineEdit with directory name, bookmarks/favorites/history combobox
        # XXX Allow filtering files by typing name
        
        self.addAction(self.nextPaneAct)
        self.addAction(self.chooseBookmarkAct)
        self.addAction(self.newTabAct)
        self.addAction(self.closeTabAct)
        self.addAction(self.leftToRightAct)
        self.addAction(self.rightToLeftAct)
        self.addAction(self.copySelectedFilesAct)
        self.addAction(self.moveSelectedFilesAct)
        self.addAction(self.diffDirsAct)
        self.addAction(self.diffExternallyAct)
        self.addAction(self.swapPanesAct)
        self.addAction(self.profileAct)

    def leftToRight(self, reverse=False):
        logger.info("")

        source_pane = self.getRightPane() if reverse else self.getLeftPane()
        target_pane = self.getLeftPane() if reverse else self.getRightPane()

        
        # - if the cursor is on the target pane, use the source pane's dirpath/search string
        # - If the cursor is on the source pane and over a non  ".." directory,
        #   use that directory as dirpath
        # - otherwise use the source pane dirpath/search string
        dirpath = source_pane.file_dir
        search_mode = source_pane.search_mode
        if (source_pane is self.getActivePane()):
            file_info = source_pane.getActiveView().currentIndex().data(Qt.UserRole)
            if (source_pane.isBrowsable(file_info) and (file_info.filename != "..")):
                dirpath = os.path.join(dirpath, file_info.filename)
                search_mode = False
            
        if (search_mode):
            target_pane.search_mode = True
            target_pane.setSearchString(dirpath)

        else:
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
            if (
                (not self.getSourcePane().checkOperation("%s Files" % action)) or
                (not self.getTargetPane().checkOperation("%s Files" % action))
                ):
                # XXX Implement copy or moving from/to archives
                return

            # XXX Missing Yes All, No All buttons
            if (qYesNoCancelMessageBox(
                self, 
                "%s files" % action, 
                "%s %d file%s to\n%s" % (action, len(filepaths), "s" if (len(filepaths) > 1) else "", target_dir),
                QMessageBox.Yes
                ) == QMessageBox.Yes):
                
                # XXX Warn if dest inside source
                # XXX Needs to check that the selected file is not ..
                # XXX Show progress, cancel, queue/background, etc
                # XXX Implement this for packers, copying from packer to
                #     filesystem could be implemented in terms of extract
                reply = None
                for filepath in filepaths:
                    destination_path = os.path.join(target_dir, os.path.basename(filepath))
                    if (os.path.exists(destination_path) and (reply != QMessageBox.YesAll)):
                        if (reply == QMessageBox.NoAll):
                            continue
                        reply = QMessageBox.question(
                            self,
                            "Copy File",
                            "'%s' already exists, overwrite?" % os.path.basename(destination_path),
                            QMessageBox.Yes | QMessageBox.YesAll | QMessageBox.No | QMessageBox.NoAll | QMessageBox.Cancel,
                            QMessageBox.Cancel
                        )
                        if (reply == QMessageBox.Cancel):
                            break
                        if (reply in [QMessageBox.No, QMessageBox.NoAll]):
                            continue

                    try:
                        # XXX Deselect files as they are copied?
                        if (move):
                            logger.info("Moving %r to %r", filepath, target_dir)
                            shutil.move(filepath, target_dir)
                            logger.info("Moved: %r to %r", filepath, target_dir)

                        else:
                            # XXX Do this in terms of getFileInfos so it works
                            #     with WCX/WFX (or call into their own copy
                            #     APIs?)
                            logger.info("Copying %r to %r", filepath, target_dir)
                            os_copy(filepath, target_dir)
                            logger.info("Copied: %r to %r", filepath, target_dir)

                    except Exception as e:
                        # XXX Display errors, offer ignore all, cancel, etc
                        logger.error("Error processing %r %s", filepath, e)

                # XXX Update the model and emit data change instead of forcing a
                #     reload? Do the reload only on corner cases? (eg files were
                #     overwritten)
                if (self.getSourcePane().model.watcher is None):
                    self.getSourcePane().reloadDirectory()
                if (self.getTargetPane().model.watcher is None):
                    self.getTargetPane().reloadDirectory()

    def swapPanes(self):
        logger.info("")

        target_pane = self.getTargetPane()

        left_pane = self.getLeftPane()
        right_pane = self.getRightPane()

        i_left = self.left_panes.index(left_pane)
        i_right = self.right_panes.index(right_pane)

        # Remove first to remove ownership, otherwise an owned pane cannot be
        # set on a different tab
        self.left_tab.removeTab(i_left)
        self.right_tab.removeTab(i_right)
        
        self.left_panes[i_left] = right_pane
        self.left_tab.insertTab(i_left, right_pane, "")
        self.left_tab.setCurrentIndex(i_left)
        right_pane.updateDirectoryLabel()

        self.right_panes[i_right] = left_pane
        self.right_tab.insertTab(i_right, left_pane, "")
        self.right_tab.setCurrentIndex(i_right)
        left_pane.updateDirectoryLabel()

        target_pane.getActiveView().setFocus()

    def diffDirectories(self):
        """
        Mark newer or different files and directories, ignore same files (same
        name and size)
        """
        logger.info("Start")
        # Sort both directories, mark newer or unique files

        # XXX Do in background, at the very least show message box and allow
        #     cancel

        # Selecting files can be slow when signals are fired individually,
        # create a selection and select that one
        
        r_left = 0
        r_right = 0
        m_left = self.getLeftPane().getActiveView().model()
        m_right = self.getRightPane().getActiveView().model()
        rc_left = m_left.rowCount()
        rc_right = m_right.rowCount()

        # Models are sorted by whatever column, sort the indices by name (no
        # need for full fileinfo_cmp sorting as long as the loop below doesn't
        # do it either)
        si_left = sorted(xrange(rc_left), key= lambda i: m_left.data(m_left.index(i, 0), Qt.UserRole).filename.lower())
        si_right = sorted(xrange(rc_right), key= lambda i: m_right.data(m_right.index(i, 0), Qt.UserRole).filename.lower())
        
        s_left = QItemSelection()
        s_right = QItemSelection()
        qApp.setOverrideCursor(Qt.WaitCursor)
        while ((r_left < rc_left) and (r_right < rc_right)):

            i_left = m_left.index(si_left[r_left], 0)
            i_right = m_right.index(si_right[r_right], 0)

            f_left = i_left.data(Qt.UserRole)
            f_right = i_right.data(Qt.UserRole)

            c = cmp(f_left.filename.lower(), f_right.filename.lower())
            assert None is logger.debug("Compared %d %r vs. %r", c,f_left.filename, f_right.filename)

            if (c == 0):
                assert None is logger.debug("Equal filenames %r vs. %r", f_left.filename, f_right.filename)
                
                assert None is logger.debug("Comparing sizes %d vs. %d", f_left.size, f_right.size)
                # Assume same if same size
                if (f_left.size != f_right.size):
                    # Advance both, add newest
                    # Note reversed comparison so newer files are selected
                    c = cmp(f_right.mtime, f_left.mtime)

                    assert None is logger.debug("Compared times %d %r vs. %r", c, f_left.mtime, f_right.mtime)

                if (c == 0):
                    r_left += 1
                    r_right += 1

                # Fall-through for -1 and 1 cases

            if (c < 0):
                assert None is logger.debug("Selecting left file %r", f_left.filename)
                # Add left, advance left
                s_left.select(i_left, i_left)
                r_left += 1

            elif (c > 0):
                assert None is logger.debug("Selecting right file %r", f_right.filename)
                # Add right, advance right
                s_right.select(i_right, i_right)
                r_right += 1

        # Complete the selection with the remaining items if any
        while (r_left < rc_left):
            i_left = m_left.index(si_left[r_left], 0)
            s_left.select(i_left, i_left)
            r_left += 1

        while (r_right < rc_right):
            i_right = m_right.index(si_right[r_right], 0)
            s_right.select(i_right, i_right)
            r_right += 1

        self.getLeftPane().getActiveView().selectionModel().select(s_left, QItemSelectionModel.Select | QItemSelectionModel.Rows)
        self.getRightPane().getActiveView().selectionModel().select(s_right, QItemSelectionModel.Select | QItemSelectionModel.Rows)

        qApp.restoreOverrideCursor()
        logger.info("Done")

    def diffExternally(self):
        """
        Diff with external tool either:
        - The two selected entries (in source, in target, or across panes)
        - The two pane directories if no selection
        """
        logger.info("")

        # XXX Make this work with archives
        if (
            (not self.getSourcePane().checkOperation("Diff Externally")) or
            (not self.getTargetPane().checkOperation("Diff Externally"))):
            return

        src_filepaths = self.getSourcePane().getSelectedFilepaths(True)
        dst_filepaths = self.getTargetPane().getSelectedFilepaths(True)

        if ((len(src_filepaths) == 0) and (len(dst_filepaths) == 0)):
            # No selection, diff dirs
            # XXX What about search strings?
            src_filepath = self.getSourcePane().file_dir
            dst_filepath = self.getTargetPane().file_dir

        elif ((len(src_filepaths) == 1) and (len(dst_filepaths) == 1)):
            # Single selection, diff entries
            src_filepath = src_filepaths[0]
            dst_filepath = dst_filepaths[0]

        elif (len(src_filepaths) == 2):
            # Two selections on src, prioritize src over dst
            src_filepath = src_filepaths[0]
            dst_filepath = src_filepaths[1]

        elif (len(src_filepaths) == 2):
            # Two selections on dst
            src_filepath = dst_filepaths[0]
            dst_filepath = dst_filepaths[1]

        else:
            # Other combinations are invalid, ignore
            
            # XXX Could pass selected source and target files to kdiff3, does
            #     kdiff3 accept list of files?
            return

        arguments = [src_filepath, dst_filepath]
        # Start detached will create an independent process instead of a child
        QProcess().startDetached(g_external_diff_filepath, arguments)

    def getLeftPane(self):
        return self.left_panes[self.left_tab.currentIndex()]
    
    def getRightPane(self):
        return self.right_panes[self.right_tab.currentIndex()]

    def getSourcePane(self):
        if (self.focusWidget() is self.getLeftPane().getActiveView()):
            return self.getLeftPane()
        else:
            return self.getRightPane()

    def getTargetPane(self):
        if (self.getSourcePane() is self.getRightPane()):
            return self.getLeftPane()
        else:
            return self.getRightPane()

    def getActivePane(self):
        return self.getSourcePane()
            
    def nextPane(self):
        logger.info("")
        self.getTargetPane().getActiveView().setFocus()
        
        # updateWindowTitle is called in eventFilter when focusIn is detected on
        # the pane, no need to explicitly call here

    def createPane(self, tab, display_width=DISPLAY_WIDTH, sort_column=1, sort_order=Qt.AscendingOrder):
        logger.info("")

        def updateTabTitle(tab, file_pane, text):
            logger.info("%r, %r, %r", tab, file_pane, text)
            if (text.startswith("search:")):
                text = "s:" + text[len("search:"):]

            else:
                basename = os.path.basename(text)
                # basename is not useful for roots (shares, drives), in that case
                # show the incoming text
                text = basename if (basename != "") else (text if (text != "") else os.sep)
            
            index = tab.indexOf(file_pane)
            
            tab.setTabText(index, text)

            # XXX Rotate the icon on a timer, but it needs to know when not to
            #     start the timer if already started, have a generic animation
            #     timer that can be connected to for multiple animations?
            loading = False if (file_pane.model.directoryReader is None) else file_pane.model.directoryReader.isRunning()
            icon = qApp.style().standardIcon(QStyle.SP_BrowserReload) if loading else QIcon()
            tab.setTabIcon(index, icon)
            
            # Use full directory as tooltip
            if (not file_pane.search_mode):
                text = file_pane.file_dir
            tab.setTabToolTip(index, text)

        file_pane = FilePane(display_width, sort_column, sort_order)
        
        if (tab is self.left_tab):
            self.left_panes.append(file_pane)
        else:
            self.right_panes.append(file_pane)

        # Tab title will be set when calling setDirectory
        tab.addTab(file_pane, "")

        # Use the runtime parent instead of the current value of "tab" since
        # FilePanel can be reparented at runtime when swapPanes is used. Note
        # the hierarchy is FilePane->QStackWidget-> QTabWidget
        file_pane.directoryLabelChanged.connect(lambda a: updateTabTitle(file_pane.parent().parent(), file_pane, a))

        return file_pane

    def chooseTab(self):
        """
        Show popup of tabs, allow creating, deleting or switching to a tab
        """
        logger.info("")
        
        active_pane = self.getActivePane()
        tab = self.left_tab if (active_pane is self.getLeftPane()) else self.right_tab
        
        menu = EditablePopupMenu(self, allow_check=False, allow_delete=True)
        action = menu.addAction("New tab")
        action.setData(tab.count())
        closeTabAct = menu.addAction("Close tab")
        if (tab.count() == 1):
            closeTabAct.setEnabled(False)
        menu.addSeparator()
        for i in xrange(tab.count()):
            file_pane = tab.widget(i)

            tab_title = ("search:%s" % file_pane.search_string) if file_pane.search_mode else file_pane.file_dir
            action = menu.addAction(tab_title, i, True)
            # Needs checkable before checked, otherwise checked is ignored
            action.setCheckable(i == tab.currentIndex())
            action.setChecked(i == tab.currentIndex())

        action = menu.exec_(tab.tabBar().mapToGlobal(tab.tabBar().rect().bottomLeft()))
        tab_index_set = set([a.data() for a in menu.actions() if a.data() is not None])

        if (action is not None):
            if (action is closeTabAct):
                self.closeTab()

            elif ((action.data() == tab.count()) or (QApplication.keyboardModifiers() & Qt.ControlModifier)):
                # XXX Make it so it opens the tab on the other pane if shift is pressed?
                # Create a new tab
                logger.info("Creating and activating tab %d", action.data())
                if (action.data() < tab.count()):
                    # Ctrl was pressed on a valid entry, duplicate that entry
                    active_pane = tab.widget(action.data())

                # XXX Insert after the current one?
                file_pane = self.createPane(tab, active_pane.display_width, active_pane.model.sort_column, active_pane.model.sort_order)
                
                if (active_pane.search_mode):
                    file_pane.search_mode = True
                    file_pane.old_file_dir = active_pane.old_file_dir
                    file_pane.setSearchString(active_pane.search_string)

                else:
                    file_pane.setDirectory(active_pane.file_dir)

                if (active_pane.getActiveView() is active_pane.list_view):
                    file_pane.switchView()

                tab.setCurrentWidget(file_pane)
            
            else:
                logger.info("Activating tab %d", action.data())
                # Activate into a new tab if ctrl is pressed
                tab.setCurrentIndex(action.data())
        
        # Close deleted tabs, last first to preserve index validity
        for tab_index in sorted(menu.deleted_datas, reverse=True):
            logger.info("Removing tab %d", tab_index)
            self.removeTab(tab, tab_index)

    def removeTab(self, tab, index):
        logger.info("index %d", index)

        file_panes = self.left_panes if (tab is self.left_tab) else self.right_panes
        
        if (len(file_panes) == 1):
            logger.info("Not deleting last pane")
            return

        must_refocus = (self.getActivePane() is file_panes[index])
        tab.removeTab(index)
        del file_panes[index]

        if (must_refocus):
            i = tab.currentIndex()
            file_panes[i].getActiveView().setFocus()

    def closeTab(self):
        logger.info("")
        active_pane = self.getActivePane()

        tab = self.left_tab if (active_pane is self.getLeftPane()) else self.right_tab
        file_panes = self.left_panes if (tab is self.left_tab) else self.right_panes

        i = file_panes.index(active_pane)
        self.removeTab(tab, i)

    def chooseBookmark(self):
        """
        Show a popup of bookmarks, allow creating, deleting or switching to a
        bookmark.

        This needs to be handled at the app level rather than at FilePane
        because the bookmark can open in a new tab with ctrl+enter.

        In addition, bookmarks are application-global, handling them here
        simplifies things (although the bookmark reference could be shared
        across FilePanes).
        """
        logger.info("")

        active_pane = self.getActivePane()
        tab = self.left_tab if (active_pane is self.getLeftPane()) else self.right_tab

        menu = EditablePopupMenu(self, allow_check=False, allow_delete=True)
        for i, bookmark in enumerate(self.bookmarks):
            action = menu.addAction(bookmark, bookmark, True)
        menu.addSeparator()
        addCurrentAct = menu.addAction("Add current")
        
        action = menu.exec_(active_pane.directory_label.mapToGlobal(active_pane.directory_label.rect().bottomLeft()))
        
        # Remove the the deleted bookmarks, don't change the ordering
        for bookmark in menu.deleted_datas:
            self.bookmarks.remove(bookmark)
        
        if (action is addCurrentAct):
            if (active_pane.search_mode):
                bookmark = "search:" + active_pane.search_string
            else:
                bookmark = active_pane.file_dir
            
            # Ignore duplicates
            if (bookmark not in self.bookmarks):
                logger.info("Adding current bookmark %r", bookmark)
                self.bookmarks.append(bookmark)
                # XXX Is there value in preserving the creation order which
                #     translates into a predictible shortcut?
                # XXX Allow a human friendly name?
                self.bookmarks = sorted(self.bookmarks)
        
        elif (action is not None):
            logger.info("Switching to bookmark %r", action.data())
            # Switch the other opane if shift is pressed
            if (QApplication.keyboardModifiers() & Qt.ShiftModifier):
                tab = self.left_tab if (active_pane is self.getRightPane()) else self.right_tab
                active_pane = self.getTargetPane()
                
            # Switch to that bookmark, in a new tab if ctrl is pressed
            if (QApplication.keyboardModifiers() & Qt.ControlModifier):
                # XXX Insert after the current one?
                active_pane = self.createPane(
                    tab, 
                    active_pane.display_width, 
                    active_pane.model.sort_column, 
                    active_pane.model.sort_order
                )
                tab.setCurrentWidget(active_pane)
                
            bookmark = action.data()
            if (bookmark.startswith("search:")):
                active_pane.search_mode = True
                active_pane.setSearchString(bookmark[len("search:"):])

            else:
                active_pane.setDirectory(bookmark)


    def closeEvent(self, event):
        logger.info("closeEvent")
        # XXX Ignore cleanup at closeEvent time since it blocks unnecessarily
        #     at exit time when there are pending prefetches
        # self.cleanup()

        # Collect current state into settings
        
        # XXX Do this in the places where the settings change? Per docs,
        #     QSettings already saves periodically
        settings = self.settings
        # XXX All entries are written here for the time being, delete all.
        #     Remove once entries are saved periodically
        settings.remove("")
        # Root items on ini files will go in the "General" group, trying to use
        # "general" as a group will be escaped into "#general". Just use the
        # root group for simplicity
        settings.setValue("file_version", CONFIG_FILE_VERSION)
        settings.setValue("app_version", APPLICATION_VERSION)
        settings.setValue("current_pane", "left" if (self.getActivePane() is self.getLeftPane()) else "right")
        # XXX Store main window geometry (position, size, monitor?), one entry
        #     per screen resolution?
        settings.setValue("window_geometry", self.geometry())
        settings.setValue("external_viewer_filepath", g_external_viewer_filepath)
        settings.setValue("external_diff_filepath", g_external_diff_filepath)
        # XXX Store plugin info (and edit by hand for now?)
        for file_panes in (self.left_panes, self.right_panes):
            group_name = "left" if (file_panes is self.left_panes) else "right"
            tab = self.left_tab if (group_name == "left") else self.right_tab
            settings.beginGroup(group_name)
            settings.setValue("current_tab", tab.currentIndex())
            settings.beginWriteArray("tabs")
            for i, file_pane in enumerate(file_panes):
                settings.setArrayIndex(i)
                file_dir = ("search:%s" % file_pane.file_dir) if file_pane.search_mode else file_pane.file_dir
                settings.setValue("dirpath", file_dir)
                settings.setValue("mode", "thumbnails" if (file_pane.getActiveView() is file_pane.list_view) else "files")
                settings.setValue("display_width", file_pane.display_width)
                settings.setValue("sort_column", file_pane.model.sort_column)
                settings.setValue("sort_order", file_pane.model.sort_order)
                
                settings.beginWriteArray("history")
                for j, dirpath in enumerate(file_pane.dir_history):
                    settings.setArrayIndex(j)
                    settings.setValue("dirpath", dirpath)
                settings.endArray()
                settings.setValue("current_history", file_pane.current_dir_history)
                
            settings.endArray()
            settings.endGroup()

        settings.beginWriteArray("bookmarks")
        for i, bookmark in enumerate(self.bookmarks):
            settings.setArrayIndex(i)
            settings.setValue("dirpath", bookmark)
        settings.endArray()

        settings.beginGroup("localsend")
        settings.beginWriteArray("devices")
        for i, device in enumerate(g_localsend_devices):
            settings.setArrayIndex(i)
            # device is a named tuple, which jsonifies as a list, convert to
            # dict first
            settings.setValue("json", json.dumps(device._asdict()))
        settings.endArray()
        # XXX myinfo is already a dict, convert to localsenddevice for
        #     consistency or viceversa?
        settings.setValue("myinfo", json.dumps(g_localsend_myinfo))
        settings.endGroup()

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


def restore_python_exceptions():
    # Remove pyqt except hook that hides exceptions
    sys._excepthook = sys.excepthook

    def exception_hook(exctype, value, traceback):
        print(exctype, value, traceback)
        sys._excepthook(exctype, value, traceback)
        sys.exit(1)

    sys.excepthook = exception_hook

logger = logging.getLogger(__name__)
setup_logger(logger)
logger.setLevel(logging.WARNING)
logger.setLevel(logging.INFO)
#logger.setLevel(logging.DEBUG)


if (do_parse_test):
    ctypes_parse_test()


def main():
    restore_python_exceptions()

    app = QApplication(sys.argv)

    file_dirs = [None, None]
    if (len(sys.argv) > 1):
        file_dirs[0] = sys.argv[1]
        file_dirs[1] = sys.argv[min(2, len(sys.argv)-1)]
        for i, file_dir in enumerate(file_dirs):
            # These could be relative, abspath so they can be traversed up (in
            # addition that makes it appear properly and resolve the disk total
            # and free sizes in the directory label), but don't abspath network
            # root since it breaks    
            if (not(os_path_contains(SHARE_ROOT, file_dir))):
                # If it doesn't exist, ask for a directory
                if (not os.path.exists(file_dir)):
                    file_dir = qGetExistingDirectory(None, "Select Folder", os.getcwd())
                    if (file_dir == ""):
                        file_dir = os.getcwd()
                file_dir = os.path.abspath(file_dir)
                file_dirs[i] = file_dir

    window = TwinWindow(file_dirs[0], file_dirs[1])
    window.show()
    sys.exit(app.exec_())


if __name__ == '__main__':
    main()
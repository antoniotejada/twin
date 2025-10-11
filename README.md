# Twin : Twin Panel File Manager

PyQt5 twin panel file manager playground, but functional

## Screenshots

### Thumbnail pane and table pane

![image](https://github.com/user-attachments/assets/180f7a31-7e46-46ee-b3e9-8a29a6ae540b)

*[Art &copy; Greg Rutkowski](https://www.artstation.com/artwork/k4lYqK)*

### Directory comparison in table mode

![image](https://github.com/user-attachments/assets/d5e76a81-da54-470e-98cc-bf23b73a638d)

### Voidtools Evertyhing search pane in thumbnail mode

![image](https://github.com/user-attachments/assets/b8b09379-6159-4855-8709-423c8c69faf2)

*[Art &copy; Greg Rutkowski](https://www.artstation.com/artwork/k4lYqK)*

## Features

- Twin panel
- Incremental/Background/Cancellable directory listing
- Optimized directory listing on win32 using ctypes
- Table and thumbnail views
- PIL supported file formats for thumbnails, EXIF rotationc
- Automatically sizable/show/hide columns
- Resizable thumbnails
- Cached & background loaded thumbnails
- Select all/none/invert files
- Copy/Cut files to/from system clipboard
- Copy/Move files to other panel
- Create directory
- Delete/rename file/directory
- Directory comparison
- Filename substring keyboard navigation
- Navigation history
- Directory size calculation in background
- View file in external editor
- Current directory keyboard file search
- C include file parsing for automatic DLL hooking from Python
- Load Total Commander WCX packer plugins  (total7zip, iso...)
- Load Total Commander WFX filesystem plugins (sftp dav...)
- [Voidtools Everything](https://www.voidtools.com/) integration, realtime search string typing and and display results in file panel
- Directory history navigation by popup menu
- Zip Python native compressed archive listing, view with external editor
- [Localsend](https://github.com/localsend/localsend) integration, discover devices, send selected files to selected devices

## TODO

- Sorting by column
- Use multiprocessing instead of multithreading to avoid GIL UI blocking
- Keyboard file filtering
- Copy/move error overwrite reporting
- Report copy/move progress
- Background copy, move 
- Backround task management
- Tabs
- Bookmarks
- Full compressed archive / WCX packer support (create, read, update, delete)
- Config file (current state, recent directories, plugins, recent searches...)
- Drag & Drop
- Menus, About

## Requirements

- Python 2.7
- PyQt5
- PIL
- Total Commander for external viewer

## Optional Tools

### Voidtools Everything

- Install Everything from https://www.voidtools.com/downloads/
- Copy Voidtools Everything SDK from https://www.voidtools.com/Everything-SDK.zip into the _out directory

### Total Commander Plugins

WCX and WFX Total Commander plugins can be copied to the _out directory
- Unpack Total7Zip from https://www.ghisler.ch/board/viewtopic.php?t=28125 into _out\total7zip
- Unpack sftp from https://www.ghisler.ch/board/viewtopic.php?f=6&t=19994 into _out\sftpplug

### Localsend

Install the app https://github.com/localsend/localsend

Send files to other machines or devices in the local network with automatic device discovery
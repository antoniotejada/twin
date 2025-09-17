# Twin : Twin Panel File Manager

PyQt5 twin panel file manager playground, but functional

## Screenshots

### Thumbnail pane and table pane

![image](https://github.com/user-attachments/assets/180f7a31-7e46-46ee-b3e9-8a29a6ae540b)

*[Art &copy; Greg Rutkowski](https://www.artstation.com/artwork/k4lYqK)*

## Directory comparison in table mode

![image](https://github.com/user-attachments/assets/d5e76a81-da54-470e-98cc-bf23b73a638d)

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

## TODO

- Voidtools Everything integration
- Sorting by column
- Use multiprocessing instead of multithreading to avoid GIL UI blocking
- Keyboard file filtering
- Copy/move error overwrite reporting
- Report copy/move progress
- Background copy, move 
- Backround task management
- Tabs
- Bookmarks
- Directory history navigation by combobox
- Drag & Drop
- Compressed archive listing
- Menus, About

## Requirements

- Python 2.7
- PyQt5
- PIL
- Total Commander for external viewer
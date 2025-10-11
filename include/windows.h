typedef char CHAR;
typedef wchar WCHAR;
typedef WCHAR TCHAR;
typedef uint16 WORD;
typedef uint32 DWORD;
typedef int32 LONG;
typedef int32 BOOL;

typedef uintptr_t WPARAM;
typedef intptr_t LPARAM;

typedef void* HANDLE;
typedef HANDLE HICON;
typedef HANDLE HBITMAP;
typedef HANDLE HWND;

// minwindef.h

typedef int INT;
typedef unsigned int UINT;

// winnt.h

typedef CONST WCHAR *LPCWSTR,*PCWSTR;
typedef CONST CHAR *LPCSTR,*PCSTR;
typedef WCHAR *NWPSTR,*LPWSTR,*PWSTR;
typedef CHAR *NPSTR,*LPSTR,*PSTR;

typedef uintptr_t DWORD_PTR;

// Could use unsigned long long instead of the low/high struct so it
// gets automatically converted by Python, but that requires setting a pack of
// 1, since with the default packing the natural alignment of the struct is 4
// but when using long long it would change to 8. Since changing the default
// pack (which is reported to be 16) can bring problems down the line, better be
// conservative and do the conversion manually.
typedef struct {
    DWORD LowPart;
    LONG HighPart;
} LARGE_INTEGER;

// See LARGE_INTEGER note above on why not to use "unsigned long long" even if 
// it provides automatic Python conversion (breaks struct packing)
typedef struct {
    DWORD LowPart;
    DWORD HighPart;
} ULARGE_INTEGER;

typedef LARGE_INTEGER *PLARGE_INTEGER;
typedef LARGE_INTEGER *PLARGE_INTEGER;
typedef ULARGE_INTEGER *PULARGE_INTEGER;

#define FILE_ATTRIBUTE_READONLY 0x00000001
#define FILE_ATTRIBUTE_HIDDEN 0x00000002
#define FILE_ATTRIBUTE_SYSTEM 0x00000004
#define FILE_ATTRIBUTE_DIRECTORY 0x00000010
#define FILE_ATTRIBUTE_ARCHIVE 0x00000020
#define FILE_ATTRIBUTE_DEVICE 0x00000040
#define FILE_ATTRIBUTE_NORMAL 0x00000080
#define FILE_ATTRIBUTE_TEMPORARY 0x00000100
#define FILE_ATTRIBUTE_SPARSE_FILE 0x00000200
#define FILE_ATTRIBUTE_REPARSE_POINT 0x00000400
#define FILE_ATTRIBUTE_COMPRESSED 0x00000800
#define FILE_ATTRIBUTE_OFFLINE 0x00001000
#define FILE_ATTRIBUTE_NOT_CONTENT_INDEXED 0x00002000
#define FILE_ATTRIBUTE_ENCRYPTED 0x00004000
#define FILE_ATTRIBUTE_VIRTUAL 0x00010000

// windef.h

#define MAX_PATH 260

// winbase.h

// See LARGE_INTEGER note above on why not to use "unsigned long long" even if 
// it provides automatic Python conversion (breaks struct packing)
typedef struct _FILETIME { 
    DWORD dwLowDateTime; 
    DWORD dwHighDateTime; 
} FILETIME,*PFILETIME,*LPFILETIME;

typedef struct _WIN32_FIND_DATAW {
    DWORD dwFileAttributes;
    FILETIME ftCreationTime;
    FILETIME ftLastAccessTime;
    FILETIME ftLastWriteTime;
    DWORD nFileSizeHigh;
    DWORD nFileSizeLow;
    DWORD dwReserved0;
    DWORD dwReserved1;
    WCHAR cFileName[MAX_PATH];
    WCHAR cAlternateFileName[14];
} WIN32_FIND_DATAW,*LPWIN32_FIND_DATAW;

typedef WIN32_FIND_DATAW WIN32_FIND_DATA;

// fileapi.h

HANDLE FindFirstFileW(WCHAR* lpFileName,LPWIN32_FIND_DATAW lpFindFileData);
BOOL FindNextFileW(HANDLE hFindFile,LPWIN32_FIND_DATAW lpFindFileData);
BOOL FindClose(HANDLE hFindFile);


// shellapi.h

#define SHGFI_ICON 0x000000100
#define SHGFI_DISPLAYNAME 0x000000200
#define SHGFI_TYPENAME 0x000000400
#define SHGFI_ATTRIBUTES 0x000000800
#define SHGFI_ICONLOCATION 0x000001000
#define SHGFI_EXETYPE 0x000002000
#define SHGFI_SYSICONINDEX 0x000004000
#define SHGFI_LINKOVERLAY 0x000008000
#define SHGFI_SELECTED 0x000010000
#define SHGFI_ATTR_SPECIFIED 0x000020000

#define SHGFI_LARGEICON 0x000000000
#define SHGFI_SMALLICON 0x000000001
#define SHGFI_OPENICON 0x000000002
#define SHGFI_SHELLICONSIZE 0x000000004
#define SHGFI_PIDL 0x000000008
#define SHGFI_USEFILEATTRIBUTES 0x000000010

#define SHGFI_ADDOVERLAYS 0x000000020
#define SHGFI_OVERLAYINDEX 0x000000040

typedef struct _SHFILEINFOA {
    HICON hIcon;
    int iIcon;
    DWORD dwAttributes;
    CHAR szDisplayName[MAX_PATH];
    CHAR szTypeName[80];
} SHFILEINFOA;

typedef struct _SHFILEINFOW {
    HICON hIcon;
    int iIcon;
    DWORD dwAttributes;
    WCHAR szDisplayName[MAX_PATH];
    WCHAR szTypeName[80];
} SHFILEINFOW;

// SHSTDAPI_(DWORD_PTR) SHGetFileInfoA (LPCSTR pszPath, DWORD dwFileAttributes, SHFILEINFOA *psfi, UINT cbFileInfo, UINT uFlags);
DWORD_PTR SHGetFileInfoA (LPCSTR pszPath, DWORD dwFileAttributes, SHFILEINFOA *psfi, UINT cbFileInfo, UINT uFlags);
// SHSTDAPI_(DWORD_PTR) SHGetFileInfoW (LPCWSTR pszPath, DWORD dwFileAttributes, SHFILEINFOW *psfi, UINT cbFileInfo, UINT uFlags);
DWORD_PTR SHGetFileInfoW (LPCWSTR pszPath, DWORD dwFileAttributes, SHFILEINFOW *psfi, UINT cbFileInfo, UINT uFlags);

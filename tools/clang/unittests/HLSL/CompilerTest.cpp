///////////////////////////////////////////////////////////////////////////////
//                                                                           //
// CompilerTest.cpp                                                          //
// Copyright (C) Microsoft Corporation. All rights reserved.                 //
// This file is distributed under the University of Illinois Open Source     //
// License. See LICENSE.TXT for details.                                     //
//                                                                           //
// Provides tests for the compiler API.                                      //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////

#ifndef UNICODE
#define UNICODE
#endif

#include <memory>
#include <vector>
#include <string>
#include <map>
#include <set>
#include <cassert>
#include <sstream>
#include <algorithm>
#include <cfloat>
#include "dxc/DxilContainer/DxilContainer.h"
#include "dxc/Support/WinIncludes.h"
#include "dxc/dxcapi.h"
#include "dxc/dxcpix.h"
#ifdef _WIN32
#include <atlfile.h>
#include "dia2.h"
#endif

#include "dxc/Test/HLSLTestData.h"
#include "dxc/Test/HlslTestUtils.h"
#include "dxc/Test/DxcTestUtils.h"

#include "llvm/Support/raw_os_ostream.h"
#include "dxc/Support/Global.h"
#include "dxc/Support/dxcapi.use.h"
#include "dxc/Support/microcom.h"
#include "dxc/Support/HLSLOptions.h"
#include "dxc/Support/Unicode.h"

#include <fstream>
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/MSFileSystem.h"
#include "llvm/Support/Path.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/StringSwitch.h"

using namespace std;
using namespace hlsl_test;

class TestIncludeHandler : public IDxcIncludeHandler {
  DXC_MICROCOM_REF_FIELD(m_dwRef)
public:
  DXC_MICROCOM_ADDREF_RELEASE_IMPL(m_dwRef)
  dxc::DxcDllSupport &m_dllSupport;
  HRESULT m_defaultErrorCode = E_FAIL;
  TestIncludeHandler(dxc::DxcDllSupport &dllSupport) : m_dwRef(0), m_dllSupport(dllSupport), callIndex(0) { }
  HRESULT STDMETHODCALLTYPE QueryInterface(REFIID iid, void** ppvObject) override {
    return DoBasicQueryInterface<IDxcIncludeHandler>(this,  iid, ppvObject);
  }

  struct LoadSourceCallInfo {
    std::wstring Filename;     // Filename as written in #include statement
    LoadSourceCallInfo(LPCWSTR pFilename) :
      Filename(pFilename) { }
  };
  std::vector<LoadSourceCallInfo> CallInfos;
  std::wstring GetAllFileNames() const {
    std::wstringstream s;
    for (size_t i = 0; i < CallInfos.size(); ++i) {
      s << CallInfos[i].Filename << ';';
    }
    return s.str();
  }
  struct LoadSourceCallResult {
    HRESULT hr;
    std::string source;
    UINT32 codePage;
    LoadSourceCallResult() : hr(E_FAIL), codePage(0) { }
    LoadSourceCallResult(const char *pSource, UINT32 codePage = CP_UTF8) : hr(S_OK), source(pSource), codePage(codePage) { }
  };
  std::vector<LoadSourceCallResult> CallResults;
  size_t callIndex;

  HRESULT STDMETHODCALLTYPE LoadSource(
    _In_ LPCWSTR pFilename,                   // Filename as written in #include statement
    _COM_Outptr_ IDxcBlob **ppIncludeSource   // Resultant source object for included file
    ) override {
    CallInfos.push_back(LoadSourceCallInfo(pFilename));

    *ppIncludeSource = nullptr;
    if (callIndex >= CallResults.size()) {
      return m_defaultErrorCode;
    }
    if (FAILED(CallResults[callIndex].hr)) {
      return CallResults[callIndex++].hr;
    }
    MultiByteStringToBlob(m_dllSupport, CallResults[callIndex].source,
                          CallResults[callIndex].codePage, ppIncludeSource);
    return CallResults[callIndex++].hr;
  }
};

#ifdef _WIN32
class CompilerTest {
#else
class CompilerTest : public ::testing::Test {
#endif
public:
  BEGIN_TEST_CLASS(CompilerTest)
    TEST_CLASS_PROPERTY(L"Parallel", L"true")
    TEST_METHOD_PROPERTY(L"Priority", L"0")
  END_TEST_CLASS()

  TEST_CLASS_SETUP(InitSupport);

  TEST_METHOD(CompileWhenDefinesThenApplied)
  TEST_METHOD(CompileWhenDefinesManyThenApplied)
  TEST_METHOD(CompileWhenEmptyThenFails)
  TEST_METHOD(CompileWhenIncorrectThenFails)
  TEST_METHOD(CompileWhenWorksThenDisassembleWorks)
  TEST_METHOD(CompileWhenDebugWorksThenStripDebug)
  TEST_METHOD(CompileWhenWorksThenAddRemovePrivate)
  TEST_METHOD(CompileThenAddCustomDebugName)
  TEST_METHOD(CompileThenTestPdbUtils)
  TEST_METHOD(CompileThenTestPdbUtilsStripped)
  TEST_METHOD(CompileWithRootSignatureThenStripRootSignature)

  TEST_METHOD(CompileWhenIncludeThenLoadInvoked)
  TEST_METHOD(CompileWhenIncludeThenLoadUsed)
  TEST_METHOD(CompileWhenIncludeAbsoluteThenLoadAbsolute)
  TEST_METHOD(CompileWhenIncludeLocalThenLoadRelative)
  TEST_METHOD(CompileWhenIncludeSystemThenLoadNotRelative)
  TEST_METHOD(CompileWhenIncludeSystemMissingThenLoadAttempt)
  TEST_METHOD(CompileWhenIncludeFlagsThenIncludeUsed)
  TEST_METHOD(CompileWhenIncludeMissingThenFail)
  TEST_METHOD(CompileWhenIncludeHasPathThenOK)
  TEST_METHOD(CompileWhenIncludeEmptyThenOK)

  TEST_METHOD(CompileWhenODumpThenPassConfig)
  TEST_METHOD(CompileWhenODumpThenOptimizerMatch)
  TEST_METHOD(CompileWhenVdThenProducesDxilContainer)

#if _ITERATOR_DEBUG_LEVEL==0 
  // CompileWhenNoMemThenOOM can properly detect leaks only when debug iterators are disabled
  BEGIN_TEST_METHOD(CompileWhenNoMemThenOOM)
    // Disabled because there are problems where we try to allocate memory in destructors,
    // which causes more bad_alloc() throws while unwinding bad_alloc(), which asserts
    // If only failing one allocation, there are allocations where failing them is lost,
    // such as in ~raw_string_ostream(), where it flushes, then eats bad_alloc(), if thrown.
    TEST_METHOD_PROPERTY(L"Ignore", L"true")
  END_TEST_METHOD()
#endif
  TEST_METHOD(CompileWhenShaderModelMismatchAttributeThenFail)
  TEST_METHOD(CompileBadHlslThenFail)
  TEST_METHOD(CompileLegacyShaderModelThenFail)
  TEST_METHOD(CompileWhenRecursiveAlbeitStaticTermThenFail)

  TEST_METHOD(CompileWhenRecursiveThenFail)

  TEST_METHOD(CompileHlsl2015ThenFail)
  TEST_METHOD(CompileHlsl2016ThenOK)
  TEST_METHOD(CompileHlsl2017ThenOK)
  TEST_METHOD(CompileHlsl2018ThenOK)
  TEST_METHOD(CompileHlsl2019ThenFail)

  TEST_METHOD(CodeGenFloatingPointEnvironment)
  TEST_METHOD(CodeGenInclude)
  TEST_METHOD(CodeGenLibCsEntry)
  TEST_METHOD(CodeGenLibCsEntry2)
  TEST_METHOD(CodeGenLibCsEntry3)
  TEST_METHOD(CodeGenLibEntries)
  TEST_METHOD(CodeGenLibEntries2)
  TEST_METHOD(CodeGenLibNoAlias)
  TEST_METHOD(CodeGenLibResource)
  TEST_METHOD(CodeGenLibUnusedFunc)

  TEST_METHOD(CodeGenRootSigProfile)
  TEST_METHOD(CodeGenRootSigProfile2)
  TEST_METHOD(CodeGenRootSigProfile5)
  TEST_METHOD(CodeGenWaveSize)
  TEST_METHOD(PreprocessWhenValidThenOK)
  TEST_METHOD(LibGVStore)
  TEST_METHOD(PreprocessWhenExpandTokenPastingOperandThenAccept)
  TEST_METHOD(PreprocessWithDebugOptsThenOk)
  TEST_METHOD(WhenSigMismatchPCFunctionThenFail)
  TEST_METHOD(CompileOtherModesWithDebugOptsThenOk)

  TEST_METHOD(BatchSamples)
  TEST_METHOD(BatchD3DReflect)
  TEST_METHOD(BatchDxil)
  TEST_METHOD(BatchHLSL)
  TEST_METHOD(BatchInfra)
  TEST_METHOD(BatchPasses)
  TEST_METHOD(BatchShaderTargets)
  TEST_METHOD(BatchValidation)

  TEST_METHOD(SubobjectCodeGenErrors)
  BEGIN_TEST_METHOD(ManualFileCheckTest)
    TEST_METHOD_PROPERTY(L"Ignore", L"true")
  END_TEST_METHOD()

  // Batch directories
  BEGIN_TEST_METHOD(CodeGenHashStability)
      TEST_METHOD_PROPERTY(L"Priority", L"2")
  END_TEST_METHOD()

  dxc::DxcDllSupport m_dllSupport;
  VersionSupportInfo m_ver;

  void CreateBlobPinned(_In_bytecount_(size) LPCVOID data, SIZE_T size,
                        UINT32 codePage, _Outptr_ IDxcBlobEncoding **ppBlob) {
    CComPtr<IDxcLibrary> library;
    IFT(m_dllSupport.CreateInstance(CLSID_DxcLibrary, &library));
    IFT(library->CreateBlobWithEncodingFromPinned(data, size, codePage,
                                                  ppBlob));
  }

  void CreateBlobFromFile(LPCWSTR name, _Outptr_ IDxcBlobEncoding **ppBlob) {
    CComPtr<IDxcLibrary> library;
    IFT(m_dllSupport.CreateInstance(CLSID_DxcLibrary, &library));
    const std::wstring path = hlsl_test::GetPathToHlslDataFile(name);
    IFT(library->CreateBlobFromFile(path.c_str(), nullptr, ppBlob));
  }

  void CreateBlobFromText(_In_z_ const char *pText,
                          _Outptr_ IDxcBlobEncoding **ppBlob) {
    CreateBlobPinned(pText, strlen(pText) + 1, CP_UTF8, ppBlob);
  }

  HRESULT CreateCompiler(IDxcCompiler **ppResult) {
    return m_dllSupport.CreateInstance(CLSID_DxcCompiler, ppResult);
  }
 
  void TestPdbUtils(bool bSlim, bool bLegacy, bool bStrip);

#ifdef _WIN32 // No ContainerBuilder support yet
  HRESULT CreateContainerBuilder(IDxcContainerBuilder **ppResult) {
    return m_dllSupport.CreateInstance(CLSID_DxcContainerBuilder, ppResult);
  }
#endif

  template <typename T, typename TDefault, typename TIface>
  void WriteIfValue(TIface *pSymbol, std::wstringstream &o,
                    TDefault defaultValue, LPCWSTR valueLabel,
                    HRESULT (__stdcall TIface::*pFn)(T *)) {
    T value;
    HRESULT hr = (pSymbol->*(pFn))(&value);
    if (SUCCEEDED(hr) && value != defaultValue) {
      o << L", " << valueLabel << L": " << value;
    }
  }

  std::string GetOption(std::string &cmd, char *opt) {
    std::string option = cmd.substr(cmd.find(opt));
    option = option.substr(option.find_first_of(' '));
    option = option.substr(option.find_first_not_of(' '));
    return option.substr(0, option.find_first_of(' '));
  }

  void CodeGenTest(std::wstring name) {
    CComPtr<IDxcCompiler> pCompiler;
    CComPtr<IDxcOperationResult> pResult;
    CComPtr<IDxcBlobEncoding> pSource;

    name.insert(0, L"..\\CodeGenHLSL\\");

    VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
    CreateBlobFromFile(name.c_str(), &pSource);

    std::string cmdLine = GetFirstLine(name.c_str());

    llvm::StringRef argsRef = cmdLine;
    llvm::SmallVector<llvm::StringRef, 8> splitArgs;
    argsRef.split(splitArgs, " ");
    hlsl::options::MainArgs argStrings(splitArgs);
    std::string errorString;
    llvm::raw_string_ostream errorStream(errorString);
    hlsl::options::DxcOpts opts;
    IFT(ReadDxcOpts(hlsl::options::getHlslOptTable(), /*flagsToInclude*/ 0,
                    argStrings, opts, errorStream));
    std::wstring entry =
        Unicode::UTF8ToUTF16StringOrThrow(opts.EntryPoint.str().c_str());
    std::wstring profile =
        Unicode::UTF8ToUTF16StringOrThrow(opts.TargetProfile.str().c_str());

    std::vector<std::wstring> argLists;
    CopyArgsToWStrings(opts.Args, hlsl::options::CoreOption, argLists);

    std::vector<LPCWSTR> args;
    args.reserve(argLists.size());
    for (const std::wstring &a : argLists)
      args.push_back(a.data());

    VERIFY_SUCCEEDED(pCompiler->Compile(
        pSource, name.c_str(), entry.c_str(), profile.c_str(), args.data(), args.size(),
        opts.Defines.data(), opts.Defines.size(), nullptr, &pResult));
    VERIFY_IS_NOT_NULL(pResult, L"Failed to compile - pResult NULL");
    HRESULT result;
    VERIFY_SUCCEEDED(pResult->GetStatus(&result));
    if (FAILED(result)) {
      CComPtr<IDxcBlobEncoding> pErr;
      IFT(pResult->GetErrorBuffer(&pErr));
      std::string errString(BlobToUtf8(pErr));
      CA2W errStringW(errString.c_str(), CP_UTF8);
      WEX::Logging::Log::Comment(L"Failed to compile - errors follow");
      WEX::Logging::Log::Comment(errStringW);
    }
    VERIFY_SUCCEEDED(result);

    CComPtr<IDxcBlob> pProgram;
    VERIFY_SUCCEEDED(pResult->GetResult(&pProgram));
    if (opts.IsRootSignatureProfile())
      return;

    CComPtr<IDxcBlobEncoding> pDisassembleBlob;
    VERIFY_SUCCEEDED(pCompiler->Disassemble(pProgram, &pDisassembleBlob));

    std::string disassembleString(BlobToUtf8(pDisassembleBlob));
    VERIFY_ARE_NOT_EQUAL(0U, disassembleString.size());
  }
  
  void CodeGenTestHashFullPath(LPCWSTR fullPath) {
    FileRunTestResult t = FileRunTestResult::RunHashTestFromFileCommands(fullPath);
    if (t.RunResult != 0) {
      CA2W commentWide(t.ErrorMessage.c_str(), CP_UTF8);
      WEX::Logging::Log::Comment(commentWide);
      WEX::Logging::Log::Error(L"Run result is not zero");
    }
  }

  void CodeGenTestHash(LPCWSTR name, bool implicitDir) {
    std::wstring path = name;
    if (implicitDir) {
      path.insert(0, L"..\\CodeGenHLSL\\");
      path = hlsl_test::GetPathToHlslDataFile(path.c_str());
    }
    CodeGenTestHashFullPath(path.c_str());
  }

  void CodeGenTestCheckBatchHash(std::wstring suitePath, bool implicitDir = true) {
    using namespace llvm;
    using namespace WEX::TestExecution;

    if (implicitDir) suitePath.insert(0, L"..\\HLSLFileCheck\\");

    ::llvm::sys::fs::MSFileSystem *msfPtr;
    VERIFY_SUCCEEDED(CreateMSFileSystemForDisk(&msfPtr));
    std::unique_ptr<::llvm::sys::fs::MSFileSystem> msf(msfPtr);
    ::llvm::sys::fs::AutoPerThreadSystem pts(msf.get());
    IFTLLVM(pts.error_code());

    CW2A pUtf8Filename(suitePath.c_str());
    if (!llvm::sys::path::is_absolute(pUtf8Filename.m_psz)) {
      suitePath = hlsl_test::GetPathToHlslDataFile(suitePath.c_str());
    }

    CW2A utf8SuitePath(suitePath.c_str());

    unsigned numTestsRun = 0;

    std::error_code EC;
    llvm::SmallString<128> DirNative;
    llvm::sys::path::native(utf8SuitePath.m_psz, DirNative);
    for (llvm::sys::fs::recursive_directory_iterator Dir(DirNative, EC), DirEnd;
         Dir != DirEnd && !EC; Dir.increment(EC)) {
      // Check whether this entry has an extension typically associated with
      // headers.
      if (!llvm::StringSwitch<bool>(llvm::sys::path::extension(Dir->path()))
          .Cases(".hlsl", ".ll", true).Default(false))
        continue;
      StringRef filename = Dir->path();
      std::string filetag = Dir->path();
      filetag += "<HASH>";

      CA2W wRelTag(filetag.data());
      CA2W wRelPath(filename.data());

      WEX::Logging::Log::StartGroup(wRelTag);
      CodeGenTestHash(wRelPath, /*implicitDir*/ false);
      WEX::Logging::Log::EndGroup(wRelTag);

      numTestsRun++;
    }

    VERIFY_IS_GREATER_THAN(numTestsRun, (unsigned)0, L"No test files found in batch directory.");
  }

  void CodeGenTestCheckFullPath(LPCWSTR fullPath, LPCWSTR dumpPath = nullptr) {
    // Create file system if needed
    llvm::sys::fs::MSFileSystem *msfPtr = llvm::sys::fs::GetCurrentThreadFileSystem();
    std::unique_ptr<llvm::sys::fs::MSFileSystem> msf;
    if (!msfPtr) {
      VERIFY_SUCCEEDED(CreateMSFileSystemForDisk(&msfPtr));
      msf.reset(msfPtr);
    }
    llvm::sys::fs::AutoPerThreadSystem pts(msfPtr);
    IFTLLVM(pts.error_code());

    FileRunTestResult t = FileRunTestResult::RunFromFileCommands(fullPath,
      /*pPluginToolsPaths*/nullptr, dumpPath);
    if (t.RunResult != 0) {
      CA2W commentWide(t.ErrorMessage.c_str(), CP_UTF8);
      WEX::Logging::Log::Comment(commentWide);
      WEX::Logging::Log::Error(L"Run result is not zero");
    }
  }

  void CodeGenTestCheck(LPCWSTR name, bool implicitDir = true, LPCWSTR dumpPath = nullptr) {
    std::wstring path = name;
    std::wstring dumpStr;
    if (implicitDir) {
      path.insert(0, L"..\\CodeGenHLSL\\");
      path = hlsl_test::GetPathToHlslDataFile(path.c_str());
      if (!dumpPath) {
        dumpStr = hlsl_test::GetPathToHlslDataFile(path.c_str(), FILECHECKDUMPDIRPARAM);
        dumpPath = dumpStr.empty() ? nullptr : dumpStr.c_str();
      }
    }
    CodeGenTestCheckFullPath(path.c_str(), dumpPath);
  }

  void CodeGenTestCheckBatchDir(std::wstring suitePath, bool implicitDir = true) {
    using namespace llvm;
    using namespace WEX::TestExecution;

    if (implicitDir) suitePath.insert(0, L"..\\HLSLFileCheck\\");

    ::llvm::sys::fs::MSFileSystem *msfPtr;
    VERIFY_SUCCEEDED(CreateMSFileSystemForDisk(&msfPtr));
    std::unique_ptr<::llvm::sys::fs::MSFileSystem> msf(msfPtr);
    ::llvm::sys::fs::AutoPerThreadSystem pts(msf.get());
    IFTLLVM(pts.error_code());

    std::wstring dumpPath;
    CW2A pUtf8Filename(suitePath.c_str());
    if (!llvm::sys::path::is_absolute(pUtf8Filename.m_psz)) {
      dumpPath = hlsl_test::GetPathToHlslDataFile(suitePath.c_str(), FILECHECKDUMPDIRPARAM);
      suitePath = hlsl_test::GetPathToHlslDataFile(suitePath.c_str());
    }

    CW2A utf8SuitePath(suitePath.c_str());

    unsigned numTestsRun = 0;

    std::error_code EC;
    llvm::SmallString<128> DirNative;
    llvm::sys::path::native(utf8SuitePath.m_psz, DirNative);
    for (llvm::sys::fs::recursive_directory_iterator Dir(DirNative, EC), DirEnd;
         Dir != DirEnd && !EC; Dir.increment(EC)) {
      // Check whether this entry has an extension typically associated with
      // headers.
      if (!llvm::StringSwitch<bool>(llvm::sys::path::extension(Dir->path()))
          .Cases(".hlsl", ".ll", true).Default(false))
        continue;
      StringRef filename = Dir->path();
      CA2W wRelPath(filename.data());
      std::wstring dumpStr;
      if (!dumpPath.empty() && suitePath.compare(0, suitePath.size(), wRelPath.m_psz, suitePath.size()) == 0) {
        dumpStr = dumpPath + (wRelPath.m_psz + suitePath.size());
      }

      WEX::Logging::Log::StartGroup(wRelPath);
      CodeGenTestCheck(wRelPath, /*implicitDir*/ false,
        dumpStr.empty() ? nullptr : dumpStr.c_str());
      WEX::Logging::Log::EndGroup(wRelPath);

      numTestsRun++;
    }

    VERIFY_IS_GREATER_THAN(numTestsRun, (unsigned)0, L"No test files found in batch directory.");
  }

  std::string VerifyCompileFailed(LPCSTR pText, LPCWSTR pTargetProfile, LPCSTR pErrorMsg) {
    return VerifyCompileFailed(pText, pTargetProfile, pErrorMsg, L"main");
  }

  std::string VerifyCompileFailed(LPCSTR pText, LPCWSTR pTargetProfile, LPCSTR pErrorMsg, LPCWSTR pEntryPoint) {
    CComPtr<IDxcCompiler> pCompiler;
    CComPtr<IDxcOperationResult> pResult;
    CComPtr<IDxcBlobEncoding> pSource;
    CComPtr<IDxcBlobEncoding> pErrors;

    VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
    CreateBlobFromText(pText, &pSource);

    VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", pEntryPoint,
      pTargetProfile, nullptr, 0, nullptr, 0, nullptr, &pResult));

    HRESULT status;
    VERIFY_SUCCEEDED(pResult->GetStatus(&status));
    VERIFY_FAILED(status);
    VERIFY_SUCCEEDED(pResult->GetErrorBuffer(&pErrors));
    if (pErrorMsg && *pErrorMsg) {
      CheckOperationResultMsgs(pResult, &pErrorMsg, 1, false, false);
    }
    return BlobToUtf8(pErrors);
  }

  void VerifyOperationSucceeded(IDxcOperationResult *pResult) {
    HRESULT result;
    VERIFY_SUCCEEDED(pResult->GetStatus(&result));
    if (FAILED(result)) {
      CComPtr<IDxcBlobEncoding> pErrors;
      VERIFY_SUCCEEDED(pResult->GetErrorBuffer(&pErrors));
      CA2W errorsWide(BlobToUtf8(pErrors).c_str(), CP_UTF8);
      WEX::Logging::Log::Comment(errorsWide);
    }
    VERIFY_SUCCEEDED(result);
  }

  std::string VerifyOperationFailed(IDxcOperationResult *pResult) {
    HRESULT result;
    VERIFY_SUCCEEDED(pResult->GetStatus(&result));
    VERIFY_FAILED(result);
    CComPtr<IDxcBlobEncoding> pErrors;
    VERIFY_SUCCEEDED(pResult->GetErrorBuffer(&pErrors));
    return BlobToUtf8(pErrors);
  }

#ifdef _WIN32 // - exclude dia stuff
  HRESULT CreateDiaSourceForCompile(const char *hlsl, IDiaDataSource **ppDiaSource)
  {
    if (!ppDiaSource)
      return E_POINTER;

    CComPtr<IDxcCompiler> pCompiler;
    CComPtr<IDxcOperationResult> pResult;
    CComPtr<IDxcBlobEncoding> pSource;
    CComPtr<IDxcBlob> pProgram;

    VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
    CreateBlobFromText(hlsl, &pSource);
    LPCWSTR args[] = { L"/Zi", L"/Qembed_debug" };
    VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
      L"ps_6_0", args, _countof(args), nullptr, 0, nullptr, &pResult));
    VERIFY_SUCCEEDED(pResult->GetResult(&pProgram));

    // Disassemble the compiled (stripped) program.
    {
      CComPtr<IDxcBlobEncoding> pDisassembly;
      VERIFY_SUCCEEDED(pCompiler->Disassemble(pProgram, &pDisassembly));
      std::string disText = BlobToUtf8(pDisassembly);
      CA2W disTextW(disText.c_str(), CP_UTF8);
      //WEX::Logging::Log::Comment(disTextW);
    }

    // CONSIDER: have the dia data source look for the part if passed a whole container.
    CComPtr<IDiaDataSource> pDiaSource;
    CComPtr<IStream> pProgramStream;
    CComPtr<IDxcLibrary> pLib;
    VERIFY_SUCCEEDED(m_dllSupport.CreateInstance(CLSID_DxcLibrary, &pLib));
    const hlsl::DxilContainerHeader *pContainer = hlsl::IsDxilContainerLike(
        pProgram->GetBufferPointer(), pProgram->GetBufferSize());
    VERIFY_IS_NOT_NULL(pContainer);
    hlsl::DxilPartIterator partIter =
        std::find_if(hlsl::begin(pContainer), hlsl::end(pContainer),
                     hlsl::DxilPartIsType(hlsl::DFCC_ShaderDebugInfoDXIL));
    const hlsl::DxilProgramHeader *pProgramHeader =
        (const hlsl::DxilProgramHeader *)hlsl::GetDxilPartData(*partIter);
    uint32_t bitcodeLength;
    const char *pBitcode;
    CComPtr<IDxcBlob> pProgramPdb;
    hlsl::GetDxilProgramBitcode(pProgramHeader, &pBitcode, &bitcodeLength);
    VERIFY_SUCCEEDED(pLib->CreateBlobFromBlob(
        pProgram, pBitcode - (char *)pProgram->GetBufferPointer(), bitcodeLength,
        &pProgramPdb));

    // Disassemble the program with debug information.
    {
      CComPtr<IDxcBlobEncoding> pDbgDisassembly;
      VERIFY_SUCCEEDED(pCompiler->Disassemble(pProgramPdb, &pDbgDisassembly));
      std::string disText = BlobToUtf8(pDbgDisassembly);
      CA2W disTextW(disText.c_str(), CP_UTF8);
      //WEX::Logging::Log::Comment(disTextW);
    }

    // Create a short text dump of debug information.
    VERIFY_SUCCEEDED(pLib->CreateStreamFromBlobReadOnly(pProgramPdb, &pProgramStream));
    VERIFY_SUCCEEDED(m_dllSupport.CreateInstance(CLSID_DxcDiaDataSource, &pDiaSource));
    VERIFY_SUCCEEDED(pDiaSource->loadDataFromIStream(pProgramStream));
    *ppDiaSource = pDiaSource.Detach();
    return S_OK;
  }
#endif // _WIN32 - exclude dia stuff
};

// Useful for debugging.
#if SUPPORT_FXC_PDB
#include <d3dcompiler.h>
#pragma comment(lib, "d3dcompiler.lib")
HRESULT GetBlobPdb(IDxcBlob *pBlob, IDxcBlob **ppDebugInfo) {
  return D3DGetBlobPart(pBlob->GetBufferPointer(), pBlob->GetBufferSize(),
    D3D_BLOB_PDB, 0, (ID3DBlob **)ppDebugInfo);
}

std::string FourCCStr(uint32_t val) {
  std::stringstream o;
  char c[5];
  c[0] = val & 0xFF;
  c[1] = (val & 0xFF00) >> 8;
  c[2] = (val & 0xFF0000) >> 16;
  c[3] = (val & 0xFF000000) >> 24;
  c[4] = '\0';
  o << c << " (" << std::hex << val << std::dec << ")";
  return o.str();
}
std::string DumpParts(IDxcBlob *pBlob) {
  std::stringstream o;

  hlsl::DxilContainerHeader *pContainer = (hlsl::DxilContainerHeader *)pBlob->GetBufferPointer();
  o << "Container:" << std::endl
    << " Size: " << pContainer->ContainerSizeInBytes << std::endl
    << " FourCC: " << FourCCStr(pContainer->HeaderFourCC) << std::endl
    << " Part count: " << pContainer->PartCount << std::endl;
  for (uint32_t i = 0; i < pContainer->PartCount; ++i) {
    hlsl::DxilPartHeader *pPart = hlsl::GetDxilContainerPart(pContainer, i);
    o << "Part " << i << std::endl
      << " FourCC: " << FourCCStr(pPart->PartFourCC) << std::endl
      << " Size: " << pPart->PartSize << std::endl;
  }
  return o.str();
}

HRESULT CreateDiaSourceFromDxbcBlob(IDxcLibrary *pLib, IDxcBlob *pDxbcBlob,
                                    IDiaDataSource **ppDiaSource) {
  HRESULT hr = S_OK;
  CComPtr<IDxcBlob> pdbBlob;
  CComPtr<IStream> pPdbStream;
  CComPtr<IDiaDataSource> pDiaSource;
  IFR(GetBlobPdb(pDxbcBlob, &pdbBlob));
  IFR(pLib->CreateStreamFromBlobReadOnly(pdbBlob, &pPdbStream));
  IFR(CoCreateInstance(CLSID_DiaSource, NULL, CLSCTX_INPROC_SERVER,
                       __uuidof(IDiaDataSource), (void **)&pDiaSource));
  IFR(pDiaSource->loadDataFromIStream(pPdbStream));
  *ppDiaSource = pDiaSource.Detach();
  return hr;
}
#endif

bool CompilerTest::InitSupport() {
  if (!m_dllSupport.IsEnabled()) {
    VERIFY_SUCCEEDED(m_dllSupport.Initialize());
    m_ver.Initialize(m_dllSupport);
  }
  return true;
}

TEST_F(CompilerTest, CompileWhenDefinesThenApplied) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;
  DxcDefine defines[] = {{L"F4", L"float4"}};

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText("F4 main() : SV_Target { return 0; }", &pSource);

  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
                                      L"ps_6_0", nullptr, 0, defines,
                                      _countof(defines), nullptr, &pResult));
}

TEST_F(CompilerTest, CompileWhenDefinesManyThenApplied) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;
  LPCWSTR args[] = {L"/DVAL1=1",  L"/DVAL2=2",  L"/DVAL3=3",  L"/DVAL4=2",
                    L"/DVAL5=4",  L"/DNVAL1",   L"/DNVAL2",   L"/DNVAL3",
                    L"/DNVAL4",   L"/DNVAL5",   L"/DCVAL1=1", L"/DCVAL2=2",
                    L"/DCVAL3=3", L"/DCVAL4=2", L"/DCVAL5=4", L"/DCVALNONE="};

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText("float4 main() : SV_Target {\r\n"
                     "#ifndef VAL1\r\n"
                     "#error VAL1 not defined\r\n"
                     "#endif\r\n"
                     "#ifndef NVAL5\r\n"
                     "#error NVAL5 not defined\r\n"
                     "#endif\r\n"
                     "#ifndef CVALNONE\r\n"
                     "#error CVALNONE not defined\r\n"
                     "#endif\r\n"
                     "return 0; }",
                     &pSource);
  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
                                      L"ps_6_0", args, _countof(args), nullptr,
                                      0, nullptr, &pResult));
  HRESULT compileStatus;
  VERIFY_SUCCEEDED(pResult->GetStatus(&compileStatus));
  if (FAILED(compileStatus)) {
    CComPtr<IDxcBlobEncoding> pErrors;
    VERIFY_SUCCEEDED(pResult->GetErrorBuffer(&pErrors));
    OutputDebugStringA((LPCSTR)pErrors->GetBufferPointer());
  }
  VERIFY_SUCCEEDED(compileStatus);
}

TEST_F(CompilerTest, CompileWhenEmptyThenFails) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;
  CComPtr<IDxcBlobEncoding> pSourceBad;
  LPCWSTR pProfile = L"ps_6_0";
  LPCWSTR pEntryPoint = L"main";

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText("float4 main() : SV_Target { return 0; }", &pSource);
  CreateBlobFromText("float4 main() : SV_Target { return undef; }", &pSourceBad);

  // correct version
  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", pEntryPoint,
                                      pProfile, nullptr, 0, nullptr, 0, nullptr,
                                      &pResult));
  pResult.Release();

  // correct version with compilation errors
  VERIFY_SUCCEEDED(pCompiler->Compile(pSourceBad, L"source.hlsl", pEntryPoint,
                                      pProfile, nullptr, 0, nullptr, 0, nullptr,
                                      &pResult));
  pResult.Release();

  // null source
  VERIFY_FAILED(pCompiler->Compile(nullptr, L"source.hlsl", pEntryPoint, pProfile,
                                   nullptr, 0, nullptr, 0, nullptr, &pResult));

  // null profile
  VERIFY_FAILED(pCompiler->Compile(pSourceBad, L"source.hlsl", pEntryPoint,
                                   nullptr, nullptr, 0, nullptr, 0, nullptr,
                                   &pResult));

  // null source name succeeds
  VERIFY_SUCCEEDED(pCompiler->Compile(pSourceBad, nullptr, pEntryPoint, pProfile,
                                   nullptr, 0, nullptr, 0, nullptr, &pResult));
  pResult.Release();

  // empty source name (as opposed to null) also suceeds
  VERIFY_SUCCEEDED(pCompiler->Compile(pSourceBad, L"", pEntryPoint, pProfile,
                                      nullptr, 0, nullptr, 0, nullptr,
                                      &pResult));
  pResult.Release();

  // null result
  VERIFY_FAILED(pCompiler->Compile(pSource, L"source.hlsl", pEntryPoint,
                                   pProfile, nullptr, 0, nullptr, 0, nullptr,
                                   nullptr));
}

TEST_F(CompilerTest, CompileWhenIncorrectThenFails) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText("float4_undefined main() : SV_Target { return 0; }",
                     &pSource);

  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main", L"ps_6_0",
                                      nullptr, 0, nullptr, 0, nullptr,
                                      &pResult));
  HRESULT result;
  VERIFY_SUCCEEDED(pResult->GetStatus(&result));
  VERIFY_FAILED(result);

  CComPtr<IDxcBlobEncoding> pErrorBuffer;
  VERIFY_SUCCEEDED(pResult->GetErrorBuffer(&pErrorBuffer));
  std::string errorString(BlobToUtf8(pErrorBuffer));
  VERIFY_ARE_NOT_EQUAL(0U, errorString.size());
  // Useful for examining actual error message:
  // CA2W errorStringW(errorString.c_str(), CP_UTF8);
  // WEX::Logging::Log::Comment(errorStringW.m_psz);
}

TEST_F(CompilerTest, CompileWhenWorksThenDisassembleWorks) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText("float4 main() : SV_Target { return 0; }", &pSource);

  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
                                      L"ps_6_0", nullptr, 0, nullptr, 0,
                                      nullptr, &pResult));
  HRESULT result;
  VERIFY_SUCCEEDED(pResult->GetStatus(&result));
  VERIFY_SUCCEEDED(result);

  CComPtr<IDxcBlob> pProgram;
  VERIFY_SUCCEEDED(pResult->GetResult(&pProgram));

  CComPtr<IDxcBlobEncoding> pDisassembleBlob;
  VERIFY_SUCCEEDED(pCompiler->Disassemble(pProgram, &pDisassembleBlob));

  std::string disassembleString(BlobToUtf8(pDisassembleBlob));
  VERIFY_ARE_NOT_EQUAL(0U, disassembleString.size());
  // Useful for examining disassembly:
  // CA2W disassembleStringW(disassembleString.c_str(), CP_UTF8);
  // WEX::Logging::Log::Comment(disassembleStringW.m_psz);
}

#ifdef _WIN32 // Container builder unsupported

TEST_F(CompilerTest, CompileWhenDebugWorksThenStripDebug) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;
  CComPtr<IDxcBlob> pProgram;

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText("float4 main(float4 pos : SV_Position) : SV_Target {\r\n"
                     "  float4 local = abs(pos);\r\n"
                     "  return local;\r\n"
                     "}",
                     &pSource);
  LPCWSTR args[] = {L"/Zi", L"/Qembed_debug"};

  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
                                      L"ps_6_0", args, _countof(args), nullptr,
                                      0, nullptr, &pResult));
  VERIFY_SUCCEEDED(pResult->GetResult(&pProgram));
  // Check if it contains debug blob
  hlsl::DxilContainerHeader *pHeader = 
      hlsl::IsDxilContainerLike(pProgram->GetBufferPointer(), pProgram->GetBufferSize());
  VERIFY_SUCCEEDED(hlsl::IsValidDxilContainer(pHeader, pProgram->GetBufferSize()));
  hlsl::DxilPartHeader *pPartHeader = hlsl::GetDxilPartByType(
      pHeader, hlsl::DxilFourCC::DFCC_ShaderDebugInfoDXIL);
  VERIFY_IS_NOT_NULL(pPartHeader);
  // Check debug info part does not exist after strip debug info

  CComPtr<IDxcBlob> pNewProgram;
  CComPtr<IDxcContainerBuilder> pBuilder;
  VERIFY_SUCCEEDED(CreateContainerBuilder(&pBuilder));
  VERIFY_SUCCEEDED(pBuilder->Load(pProgram));
  VERIFY_SUCCEEDED(pBuilder->RemovePart(hlsl::DxilFourCC::DFCC_ShaderDebugInfoDXIL));
  pResult.Release();
  VERIFY_SUCCEEDED(pBuilder->SerializeContainer(&pResult));
  VERIFY_SUCCEEDED(pResult->GetResult(&pNewProgram));
  pHeader = hlsl::IsDxilContainerLike(pNewProgram->GetBufferPointer(), pNewProgram->GetBufferSize());
  VERIFY_SUCCEEDED(hlsl::IsValidDxilContainer(pHeader, pNewProgram->GetBufferSize()));
  pPartHeader = hlsl::GetDxilPartByType(
      pHeader, hlsl::DxilFourCC::DFCC_ShaderDebugInfoDXIL);
  VERIFY_IS_NULL(pPartHeader);
}

TEST_F(CompilerTest, CompileWhenWorksThenAddRemovePrivate) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;
  CComPtr<IDxcBlob> pProgram;

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText("float4 main() : SV_Target {\r\n"
    "  return 0;\r\n"
    "}",
    &pSource);
  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
    L"ps_6_0", nullptr, 0, nullptr, 0,
    nullptr, &pResult));
  VERIFY_SUCCEEDED(pResult->GetResult(&pProgram));
  // Append private data blob
  CComPtr<IDxcContainerBuilder> pBuilder;
  VERIFY_SUCCEEDED(CreateContainerBuilder(&pBuilder));

  std::string privateTxt("private data");
  CComPtr<IDxcBlobEncoding> pPrivate;
  CreateBlobFromText(privateTxt.c_str(), &pPrivate);
  VERIFY_SUCCEEDED(pBuilder->Load(pProgram));
  VERIFY_SUCCEEDED(pBuilder->AddPart(hlsl::DxilFourCC::DFCC_PrivateData, pPrivate));
  pResult.Release();
  VERIFY_SUCCEEDED(pBuilder->SerializeContainer(&pResult));

  CComPtr<IDxcBlob> pNewProgram;
  VERIFY_SUCCEEDED(pResult->GetResult(&pNewProgram));
  hlsl::DxilContainerHeader *pContainerHeader = hlsl::IsDxilContainerLike(pNewProgram->GetBufferPointer(), pNewProgram->GetBufferSize());
  VERIFY_SUCCEEDED(hlsl::IsValidDxilContainer(pContainerHeader, pNewProgram->GetBufferSize()));
  hlsl::DxilPartHeader *pPartHeader = hlsl::GetDxilPartByType(
    pContainerHeader, hlsl::DxilFourCC::DFCC_PrivateData);
  VERIFY_IS_NOT_NULL(pPartHeader);
  // compare data
  std::string privatePart((const char *)(pPartHeader + 1), privateTxt.size());
  VERIFY_IS_TRUE(strcmp(privatePart.c_str(), privateTxt.c_str()) == 0);

  // Remove private data blob
  pBuilder.Release();
  VERIFY_SUCCEEDED(CreateContainerBuilder(&pBuilder));
  VERIFY_SUCCEEDED(pBuilder->Load(pNewProgram));
  VERIFY_SUCCEEDED(pBuilder->RemovePart(hlsl::DxilFourCC::DFCC_PrivateData));
  pResult.Release();
  VERIFY_SUCCEEDED(pBuilder->SerializeContainer(&pResult));

  pNewProgram.Release();
  VERIFY_SUCCEEDED(pResult->GetResult(&pNewProgram));
  pContainerHeader = hlsl::IsDxilContainerLike(pNewProgram->GetBufferPointer(), pNewProgram->GetBufferSize());
  VERIFY_SUCCEEDED(hlsl::IsValidDxilContainer(pContainerHeader, pNewProgram->GetBufferSize()));
  pPartHeader = hlsl::GetDxilPartByType(
    pContainerHeader, hlsl::DxilFourCC::DFCC_PrivateData);
  VERIFY_IS_NULL(pPartHeader);
}

TEST_F(CompilerTest, CompileThenAddCustomDebugName) {
  // container builders prior to 1.3 did not support adding debug name parts
  if (m_ver.SkipDxilVersion(1, 3)) return;
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;
  CComPtr<IDxcBlob> pProgram;

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText("float4 main() : SV_Target {\r\n"
    "  return 0;\r\n"
    "}",
    &pSource);

  LPCWSTR args[] = { L"/Zi", L"/Qembed_debug", L"/Zss" };

  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
    L"ps_6_0", args, _countof(args), nullptr, 0,
    nullptr, &pResult));
  VERIFY_SUCCEEDED(pResult->GetResult(&pProgram));
  // Append private data blob
  CComPtr<IDxcContainerBuilder> pBuilder;
  VERIFY_SUCCEEDED(CreateContainerBuilder(&pBuilder));

  const char pNewName[] = "MyOwnUniqueName.lld";
  //include null terminator:
  size_t nameBlobPartSize = sizeof(hlsl::DxilShaderDebugName) + _countof(pNewName);
  // round up to four-byte size:
  size_t allocatedSize = (nameBlobPartSize + 3) & ~3;
  auto pNameBlobContent = reinterpret_cast<hlsl::DxilShaderDebugName*>(malloc(allocatedSize));
  ZeroMemory(pNameBlobContent, allocatedSize); //just to make sure trailing nulls are nulls.
  pNameBlobContent->Flags = 0;
  pNameBlobContent->NameLength = _countof(pNewName) - 1; //this is not supposed to include null terminator
  memcpy(pNameBlobContent + 1, pNewName, _countof(pNewName));

  CComPtr<IDxcBlobEncoding> pDebugName;

  CreateBlobPinned(pNameBlobContent, allocatedSize, CP_UTF8, &pDebugName);


  VERIFY_SUCCEEDED(pBuilder->Load(pProgram));
  // should fail since it already exists:
  VERIFY_FAILED(pBuilder->AddPart(hlsl::DxilFourCC::DFCC_ShaderDebugName, pDebugName));
  VERIFY_SUCCEEDED(pBuilder->RemovePart(hlsl::DxilFourCC::DFCC_ShaderDebugName));
  VERIFY_SUCCEEDED(pBuilder->AddPart(hlsl::DxilFourCC::DFCC_ShaderDebugName, pDebugName));
  pResult.Release();
  VERIFY_SUCCEEDED(pBuilder->SerializeContainer(&pResult));

  CComPtr<IDxcBlob> pNewProgram;
  VERIFY_SUCCEEDED(pResult->GetResult(&pNewProgram));
  hlsl::DxilContainerHeader *pContainerHeader = hlsl::IsDxilContainerLike(pNewProgram->GetBufferPointer(), pNewProgram->GetBufferSize());
  VERIFY_SUCCEEDED(hlsl::IsValidDxilContainer(pContainerHeader, pNewProgram->GetBufferSize()));
  hlsl::DxilPartHeader *pPartHeader = hlsl::GetDxilPartByType(
    pContainerHeader, hlsl::DxilFourCC::DFCC_ShaderDebugName);
  VERIFY_IS_NOT_NULL(pPartHeader);
  // compare data
  VERIFY_IS_TRUE(memcmp(pPartHeader + 1, pNameBlobContent, allocatedSize) == 0);

  free(pNameBlobContent);

  // Remove private data blob
  pBuilder.Release();
  VERIFY_SUCCEEDED(CreateContainerBuilder(&pBuilder));
  VERIFY_SUCCEEDED(pBuilder->Load(pNewProgram));
  VERIFY_SUCCEEDED(pBuilder->RemovePart(hlsl::DxilFourCC::DFCC_ShaderDebugName));
  pResult.Release();
  VERIFY_SUCCEEDED(pBuilder->SerializeContainer(&pResult));

  pNewProgram.Release();
  VERIFY_SUCCEEDED(pResult->GetResult(&pNewProgram));
  pContainerHeader = hlsl::IsDxilContainerLike(pNewProgram->GetBufferPointer(), pNewProgram->GetBufferSize());
  VERIFY_SUCCEEDED(hlsl::IsValidDxilContainer(pContainerHeader, pNewProgram->GetBufferSize()));
  pPartHeader = hlsl::GetDxilPartByType(
    pContainerHeader, hlsl::DxilFourCC::DFCC_ShaderDebugName);
  VERIFY_IS_NULL(pPartHeader);
}

static void VerifyPdbUtil(
    IDxcBlob *pBlob, IDxcPdbUtils *pPdbUtils,
    const WCHAR *pMainFileName,
    llvm::ArrayRef<const WCHAR *> ExpectedArgs,
    llvm::ArrayRef<const WCHAR *> ExpectedFlags,
    llvm::ArrayRef<const WCHAR *> ExpectedDefines,
    IDxcCompiler *pCompiler,
    bool HasVersion,
    bool IsFullPDB,
    bool HasHashAndPdbName,
    const std::string &MainSource,
    const std::string &IncludedFile)
{
  VERIFY_SUCCEEDED(pPdbUtils->Load(pBlob));

  // Compiler version comparison
  if (!HasVersion) {
    CComPtr<IDxcVersionInfo> pVersion;
    VERIFY_FAILED(pPdbUtils->GetVersionInfo(&pVersion));
  }
  else {
    CComPtr<IDxcVersionInfo> pVersion;
    VERIFY_SUCCEEDED(pPdbUtils->GetVersionInfo(&pVersion));

    CComPtr<IDxcVersionInfo2> pVersion2;
    VERIFY_IS_NOT_NULL(pVersion);
    VERIFY_SUCCEEDED(pVersion.QueryInterface(&pVersion2));

    CComPtr<IDxcVersionInfo> pCompilerVersion;
    pCompiler->QueryInterface(&pCompilerVersion);

    if (pCompilerVersion) {
      UINT32 uCompilerMajor = 0;
      UINT32 uCompilerMinor = 0;
      UINT32 uCompilerFlags = 0;
      VERIFY_SUCCEEDED(pCompilerVersion->GetVersion(&uCompilerMajor, &uCompilerMinor));
      VERIFY_SUCCEEDED(pCompilerVersion->GetFlags(&uCompilerFlags));

      UINT32 uMajor = 0;
      UINT32 uMinor = 0;
      UINT32 uFlags = 0;
      VERIFY_SUCCEEDED(pVersion->GetVersion(&uMajor, &uMinor));
      VERIFY_SUCCEEDED(pVersion->GetFlags(&uFlags));

      VERIFY_ARE_EQUAL(uMajor, uCompilerMajor);
      VERIFY_ARE_EQUAL(uMinor, uCompilerMinor);
      VERIFY_ARE_EQUAL(uFlags, uCompilerFlags);

      CComPtr<IDxcVersionInfo2> pCompilerVersion2;
      if (SUCCEEDED(pCompiler->QueryInterface(&pCompilerVersion2))) {
        UINT32 uCompilerCommitCount = 0;
        CComHeapPtr<char> CompilerCommitVersionHash;
        VERIFY_SUCCEEDED(pCompilerVersion2->GetCommitInfo(&uCompilerCommitCount, &CompilerCommitVersionHash));

        UINT32 uCommitCount = 0;
        CComHeapPtr<char> CommitVersionHash;
        VERIFY_SUCCEEDED(pVersion2->GetCommitInfo(&uCommitCount, &CommitVersionHash));

        VERIFY_IS_TRUE(0 == strcmp(CommitVersionHash, CompilerCommitVersionHash));
        VERIFY_ARE_EQUAL(uCommitCount, uCompilerCommitCount);
      }
    }
  }

  // Target profile
  {
    CComBSTR str;
    VERIFY_SUCCEEDED(pPdbUtils->GetTargetProfile(&str));
    VERIFY_ARE_EQUAL(str, L"ps_6_0");
  }

  // Entry point
  {
    CComBSTR str;
    VERIFY_SUCCEEDED(pPdbUtils->GetEntryPoint(&str));
    VERIFY_ARE_EQUAL(str, L"PSMain");
  }

  // PDB file path
  if (HasHashAndPdbName) {
    CComBSTR pName;
    VERIFY_SUCCEEDED(pPdbUtils->GetName(&pName));
    std::wstring suffix = L".pdb";
    VERIFY_IS_TRUE(pName.Length() >= suffix.size());
    VERIFY_IS_TRUE(
      0 == std::memcmp(suffix.c_str(), &pName[pName.Length() - suffix.size()], suffix.size()));
  }

  // Main file name
  {
    CComBSTR pMainFileName;
    VERIFY_SUCCEEDED(pPdbUtils->GetMainFileName(&pMainFileName));
    VERIFY_ARE_EQUAL(pMainFileName, pMainFileName);
  }

  // There is hash and hash is not empty
  if (HasHashAndPdbName) {
    CComPtr<IDxcBlob> pHash;
    VERIFY_SUCCEEDED(pPdbUtils->GetHash(&pHash));
    hlsl::DxilShaderHash EmptyHash = {};
    VERIFY_ARE_EQUAL(pHash->GetBufferSize(), sizeof(EmptyHash));
    VERIFY_IS_FALSE(0 == std::memcmp(pHash->GetBufferPointer(), &EmptyHash, sizeof(EmptyHash)));
  }

  // Source files
  {
    UINT32 uSourceCount = 0;
    VERIFY_SUCCEEDED(pPdbUtils->GetSourceCount(&uSourceCount));
    for (UINT32 i = 0; i < uSourceCount; i++) {
      CComBSTR pFileName;
      CComPtr<IDxcBlobEncoding> pFileContent;
      VERIFY_SUCCEEDED(pPdbUtils->GetSourceName(i, &pFileName));
      VERIFY_SUCCEEDED(pPdbUtils->GetSource(i, &pFileContent));
      if (0 == wcscmp(pFileName, pMainFileName)) {
        VERIFY_IS_TRUE(pFileContent->GetBufferSize() == MainSource.size());
        VERIFY_IS_TRUE(0 == std::memcmp(pFileContent->GetBufferPointer(), MainSource.data(), MainSource.size()));
      }
      else {
        VERIFY_IS_TRUE(0 == std::memcmp(pFileContent->GetBufferPointer(), IncludedFile.data(), IncludedFile.size()));
      }
    }
  }

  // Defines
  {
    UINT32 uDefineCount = 0;
    std::map<std::wstring, int> tally;
    VERIFY_SUCCEEDED(pPdbUtils->GetDefineCount(&uDefineCount));
    VERIFY_IS_TRUE(uDefineCount == 2);
    for (UINT32 i = 0; i < uDefineCount; i++) {
      CComBSTR def;
      VERIFY_SUCCEEDED(pPdbUtils->GetDefine(i, &def));
      tally[std::wstring(def)]++;
    }
    auto Expected = ExpectedDefines;
    for (int i = 0; i < Expected.size(); i++) {
      auto it = tally.find(Expected[i]);
      VERIFY_IS_TRUE(it != tally.end() && it->second == 1);
      tally.erase(it);
    }
    VERIFY_IS_TRUE(tally.size() == 0);
  }

  // Flags
  {
    UINT32 uCount = 0;
    std::map<std::wstring, int> tally;
    VERIFY_SUCCEEDED(pPdbUtils->GetFlagCount(&uCount));
    VERIFY_IS_TRUE(uCount == ExpectedFlags.size());
    for (UINT32 i = 0; i < uCount; i++) {
      CComBSTR def;
      VERIFY_SUCCEEDED(pPdbUtils->GetFlag(i, &def));
      tally[std::wstring(def)]++;
    }

    auto Expected = ExpectedFlags;
    for (int i = 0; i < Expected.size(); i++) {
      auto it = tally.find(Expected[i]);
      VERIFY_IS_TRUE(it != tally.end() && it->second == 1);
      tally.erase(it);
    }
    VERIFY_IS_TRUE(tally.size() == 0);
  }

  // Args
  {
    UINT32 uCount = 0;
    std::map<std::wstring, int> tally;
    VERIFY_SUCCEEDED(pPdbUtils->GetArgCount(&uCount));
    for (UINT32 i = 0; i < uCount; i++) {
      CComBSTR def;
      VERIFY_SUCCEEDED(pPdbUtils->GetArg(i, &def));
      tally[std::wstring(def)]++;
    }

    auto Expected = ExpectedArgs;
    for (int i = 0; i < Expected.size(); i++) {
      auto it = tally.find(Expected[i]);
      VERIFY_IS_TRUE(it != tally.end() && it->second == 1);
    }
  }

  // Make the pix debug info
  if (IsFullPDB) {
    VERIFY_IS_TRUE(pPdbUtils->IsFullPDB());
    CComPtr<IDxcBlob> pPDBBlob;
    VERIFY_SUCCEEDED(pPdbUtils->GetFullPDB(&pPDBBlob));

    CComPtr<IDxcPixDxilDebugInfoFactory> pFactory;
    VERIFY_SUCCEEDED(pPdbUtils->QueryInterface(&pFactory));
    CComPtr<IDxcPixCompilationInfo> pCompInfo;
    VERIFY_ARE_EQUAL(E_NOTIMPL, pFactory->NewDxcPixCompilationInfo(&pCompInfo));
    CComPtr<IDxcPixDxilDebugInfo> pDebugInfo;
    VERIFY_SUCCEEDED(pFactory->NewDxcPixDxilDebugInfo(&pDebugInfo));
    VERIFY_ARE_NOT_EQUAL(pDebugInfo, nullptr);
  }
  else {
    VERIFY_IS_FALSE(pPdbUtils->IsFullPDB());
    CComPtr<IDxcBlob> pFullPdb;
    VERIFY_SUCCEEDED(pPdbUtils->GetFullPDB(&pFullPdb));

    auto ReplaceDebugFlag = [](const std::vector<const WCHAR *> &List) -> std::vector<const WCHAR *> {
      std::vector<const WCHAR *> ret;
      for (unsigned i = 0; i < List.size(); i++) {
        if (!wcscmp(List[i], L"/Qslim_debug") || !wcscmp(List[i], L"-Qslim_debug"))
          ret.push_back(L"-Qfull_debug");
        else
          ret.push_back(List[i]);
      }
      return ret;
    };

    std::vector<const WCHAR *> NewExpectedFlags = ReplaceDebugFlag(ExpectedFlags);
    std::vector<const WCHAR *> NewExpectedArgs  = ReplaceDebugFlag(ExpectedArgs);

    VerifyPdbUtil(pFullPdb, pPdbUtils,
      pMainFileName,
      NewExpectedArgs, NewExpectedFlags, ExpectedDefines,
      pCompiler, HasVersion, /*IsFullPDB*/true,
      HasHashAndPdbName, MainSource, IncludedFile);
  }
}

#ifdef _WIN32

TEST_F(CompilerTest, CompileThenTestPdbUtilsStripped) {
  CComPtr<TestIncludeHandler> pInclude;
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcBlobEncoding> pSource;
  CComPtr<IDxcOperationResult> pOperationResult;

  std::string main_source = "#include \"helper.h\"\r\n"
    "float4 PSMain() : SV_Target { return ZERO; }";
  std::string included_File = "#define ZERO 0";

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText(main_source.c_str(), &pSource);

  pInclude = new TestIncludeHandler(m_dllSupport);
  pInclude->CallResults.emplace_back(included_File.c_str());

  const WCHAR *pArgs[] = { L"/Zi", L"/Od", L"-flegacy-macro-expansion", L"-Qstrip_debug", L"/DTHIS_IS_A_DEFINE=HELLO" };
  const DxcDefine pDefines[] = { L"THIS_IS_ANOTHER_DEFINE", L"1" };

  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"PSMain",
    L"ps_6_0", pArgs, _countof(pArgs), pDefines, _countof(pDefines), pInclude, &pOperationResult));

  CComPtr<IDxcBlob> pCompiledBlob;
  VERIFY_SUCCEEDED(pOperationResult->GetResult(&pCompiledBlob));

  CComPtr<IDxcPdbUtils> pPdbUtils;
  VERIFY_SUCCEEDED(m_dllSupport.CreateInstance(CLSID_DxcPdbUtils, &pPdbUtils));

  VERIFY_SUCCEEDED(pPdbUtils->Load(pCompiledBlob));

  // PDB file path
  {
    CComBSTR pName;
    VERIFY_SUCCEEDED(pPdbUtils->GetName(&pName));
    std::wstring suffix = L".pdb";
    VERIFY_IS_TRUE(pName.Length() >= suffix.size());
    VERIFY_IS_TRUE(
      0 == std::memcmp(suffix.c_str(), &pName[pName.Length() - suffix.size()], suffix.size()));
  }

  // There is hash and hash is not empty
  {
    CComPtr<IDxcBlob> pHash;
    VERIFY_SUCCEEDED(pPdbUtils->GetHash(&pHash));
    hlsl::DxilShaderHash EmptyHash = {};
    VERIFY_ARE_EQUAL(pHash->GetBufferSize(), sizeof(EmptyHash));
    VERIFY_IS_FALSE(0 == std::memcmp(pHash->GetBufferPointer(), &EmptyHash, sizeof(EmptyHash)));
  }

  {
    VERIFY_IS_FALSE(pPdbUtils->IsFullPDB());
    UINT32 uSourceCount = 0;
    VERIFY_SUCCEEDED(pPdbUtils->GetSourceCount(&uSourceCount));
    VERIFY_ARE_EQUAL(uSourceCount, 0);
  }
}

void CompilerTest::TestPdbUtils(bool bSlim, bool bLegacy, bool bStrip) {
  CComPtr<TestIncludeHandler> pInclude;
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcBlobEncoding> pSource;
  CComPtr<IDxcOperationResult> pOperationResult;

  std::string main_source = "#include \"helper.h\"\r\n"
    "float4 PSMain() : SV_Target { return ZERO; }";
  std::string included_File = "#define ZERO 0";

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText(main_source.c_str(), &pSource);

  pInclude = new TestIncludeHandler(m_dllSupport);
  pInclude->CallResults.emplace_back(included_File.c_str());

  std::vector<const WCHAR *> args;
  std::vector<const WCHAR *> expectedArgs;
  std::vector<const WCHAR *> expectedFlags;
  std::vector<const WCHAR *> expectedDefines;

  auto AddArg = [&args, &expectedFlags, &expectedArgs](const WCHAR *arg, bool isDefine) {
    args.push_back(arg);
    expectedArgs.push_back(arg);
    if (!isDefine)
      expectedFlags.push_back(arg);
  };

  AddArg(L"/Zi", false);
  AddArg(L"/Od", false);
  AddArg(L"-flegacy-macro-expansion", false);

  if (bStrip) {
    AddArg(L"-Qstrip_debug", false);
  }
  else {
    AddArg(L"-Qembed_debug", false);
  }

  if (bLegacy) {
    AddArg(L"/Qlegacy_debug", false);
  }
  if (bSlim) {
    AddArg(L"/Qslim_debug", false);
  }
  AddArg(L"/DTHIS_IS_A_DEFINE=HELLO", true);
  const DxcDefine pDefines[] = { L"THIS_IS_ANOTHER_DEFINE", L"1" };
  expectedDefines.push_back(L"THIS_IS_ANOTHER_DEFINE=1");
  expectedDefines.push_back(L"THIS_IS_A_DEFINE=HELLO");

  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"PSMain",
    L"ps_6_0", args.data(), args.size(), pDefines, _countof(pDefines), pInclude, &pOperationResult));

  HRESULT CompileStatus = S_OK;
  VERIFY_SUCCEEDED(pOperationResult->GetStatus(&CompileStatus));
  VERIFY_SUCCEEDED(CompileStatus);

  CComPtr<IDxcBlob> pCompiledBlob;
  VERIFY_SUCCEEDED(pOperationResult->GetResult(&pCompiledBlob));

  CComPtr<IDxcResult> pResult;
  VERIFY_SUCCEEDED(pOperationResult.QueryInterface(&pResult));

  CComPtr<IDxcBlob> pPdbBlob;
  VERIFY_SUCCEEDED(pResult->GetOutput(DXC_OUT_PDB, IID_PPV_ARGS(&pPdbBlob), nullptr));

  CComPtr<IDxcPdbUtils> pPdbUtils;
  VERIFY_SUCCEEDED(m_dllSupport.CreateInstance(CLSID_DxcPdbUtils, &pPdbUtils));

  CComPtr<IDxcBlob> pProgramHeaderBlob;
  if (bLegacy) {
    CComPtr<IDxcContainerReflection> pRef;
    VERIFY_SUCCEEDED(m_dllSupport.CreateInstance(CLSID_DxcContainerReflection, &pRef));
    VERIFY_SUCCEEDED(pRef->Load(pPdbBlob));
    UINT32 uIndex = 0;
    VERIFY_SUCCEEDED(pRef->FindFirstPartKind(hlsl::DFCC_ShaderDebugInfoDXIL, &uIndex));
    VERIFY_SUCCEEDED(pRef->GetPartContent(uIndex, &pProgramHeaderBlob));

    VerifyPdbUtil(pProgramHeaderBlob, pPdbUtils,
      L"source.hlsl",
      expectedArgs, expectedFlags, expectedDefines,
      pCompiler,
      /*HasVersion*/ false,
      /*IsFullPDB*/  true,
      /*hasHasAndPDBName*/false,
      main_source, included_File);
  }

  if (!bStrip) {
    VerifyPdbUtil(pCompiledBlob, pPdbUtils,
      L"source.hlsl",
      expectedArgs, expectedFlags, expectedDefines,
      pCompiler,
      /*HasVersion*/ true,
      /*IsFullPDB*/ !bSlim,
      /*hasHasAndPDBName*/true,
      main_source, included_File);
  }

  VerifyPdbUtil(pPdbBlob, pPdbUtils,
    L"source.hlsl",
    expectedArgs, expectedFlags, expectedDefines,
    pCompiler,
    /*HasVersion*/ true,
    /*IsFullPDB*/ !bSlim,
    /*hasHasAndPDBName*/true,
    main_source, included_File);
}

TEST_F(CompilerTest, CompileThenTestPdbUtils) {
  TestPdbUtils(/*bSlim*/false, /*Legacy*/true,  /*strip*/false);  // Legacy PDB, where source info is embedded in the module
  TestPdbUtils(/*bSlim*/false, /*Legacy*/false, /*strip*/false);  // Full PDB, where source info is stored in a DXIL part and debug module is present
  TestPdbUtils(/*bSlim*/true,  /*Legacy*/false, /*strip*/false);  // Slim PDB, where source info is stored in a DXIL part and debug module is NOT present

  TestPdbUtils(/*bSlim*/false, /*Legacy*/true,  /*strip*/true);  // Legacy PDB, where source info is embedded in the module
  TestPdbUtils(/*bSlim*/false, /*Legacy*/false, /*strip*/true);  // Full PDB, where source info is stored in a DXIL part and debug module is present
  TestPdbUtils(/*bSlim*/true,  /*Legacy*/false, /*strip*/true);  // Slim PDB, where source info is stored in a DXIL part and debug module is NOT present
}
#endif

TEST_F(CompilerTest, CompileWithRootSignatureThenStripRootSignature) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;
  CComPtr<IDxcBlob> pProgram;
  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText("[RootSignature(\"\")] \r\n"
                     "float4 main(float a : A) : SV_Target {\r\n"
                     "  return a;\r\n"
                     "}",
                     &pSource);
  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
                                      L"ps_6_0", nullptr, 0, nullptr,
                                      0, nullptr, &pResult));
  VERIFY_IS_NOT_NULL(pResult);
  HRESULT status;
  VERIFY_SUCCEEDED(pResult->GetStatus(&status));
  VERIFY_SUCCEEDED(status);
  VERIFY_SUCCEEDED(pResult->GetResult(&pProgram));
  VERIFY_IS_NOT_NULL(pProgram);
  hlsl::DxilContainerHeader *pContainerHeader = hlsl::IsDxilContainerLike(pProgram->GetBufferPointer(), pProgram->GetBufferSize());
  VERIFY_SUCCEEDED(hlsl::IsValidDxilContainer(pContainerHeader, pProgram->GetBufferSize()));
  hlsl::DxilPartHeader *pPartHeader = hlsl::GetDxilPartByType(
      pContainerHeader, hlsl::DxilFourCC::DFCC_RootSignature);
  VERIFY_IS_NOT_NULL(pPartHeader);
  pResult.Release();
  
  // Remove root signature
  CComPtr<IDxcBlob> pProgramRootSigRemoved;
  CComPtr<IDxcContainerBuilder> pBuilder;
  VERIFY_SUCCEEDED(CreateContainerBuilder(&pBuilder));
  VERIFY_SUCCEEDED(pBuilder->Load(pProgram));
  VERIFY_SUCCEEDED(pBuilder->RemovePart(hlsl::DxilFourCC::DFCC_RootSignature));
  VERIFY_SUCCEEDED(pBuilder->SerializeContainer(&pResult));
  VERIFY_SUCCEEDED(pResult->GetResult(&pProgramRootSigRemoved));
  pContainerHeader = hlsl::IsDxilContainerLike(pProgramRootSigRemoved->GetBufferPointer(), pProgramRootSigRemoved->GetBufferSize());
  VERIFY_SUCCEEDED(hlsl::IsValidDxilContainer(pContainerHeader, pProgramRootSigRemoved->GetBufferSize()));
  hlsl::DxilPartHeader *pPartHeaderShouldBeNull = hlsl::GetDxilPartByType(pContainerHeader,
                                        hlsl::DxilFourCC::DFCC_RootSignature);
  VERIFY_IS_NULL(pPartHeaderShouldBeNull);
  pBuilder.Release();
  pResult.Release();

  // Add root signature back
  CComPtr<IDxcBlobEncoding> pRootSignatureBlob;
  CComPtr<IDxcLibrary> pLibrary;
  CComPtr<IDxcBlob> pProgramRootSigAdded;
  VERIFY_SUCCEEDED(m_dllSupport.CreateInstance(CLSID_DxcLibrary, &pLibrary));
  VERIFY_SUCCEEDED(pLibrary->CreateBlobWithEncodingFromPinned(
    hlsl::GetDxilPartData(pPartHeader), pPartHeader->PartSize, 0, &pRootSignatureBlob));
  VERIFY_SUCCEEDED(CreateContainerBuilder(&pBuilder));
  VERIFY_SUCCEEDED(pBuilder->Load(pProgramRootSigRemoved));
  pBuilder->AddPart(hlsl::DxilFourCC::DFCC_RootSignature, pRootSignatureBlob);
  pBuilder->SerializeContainer(&pResult);
  VERIFY_SUCCEEDED(pResult->GetResult(&pProgramRootSigAdded));
  pContainerHeader = hlsl::IsDxilContainerLike(pProgramRootSigAdded->GetBufferPointer(), pProgramRootSigAdded->GetBufferSize());
  VERIFY_SUCCEEDED(hlsl::IsValidDxilContainer(pContainerHeader, pProgramRootSigAdded->GetBufferSize()));
  pPartHeader = hlsl::GetDxilPartByType(pContainerHeader,
                                        hlsl::DxilFourCC::DFCC_RootSignature);
  VERIFY_IS_NOT_NULL(pPartHeader);
}
#endif // Container builder unsupported

TEST_F(CompilerTest, CompileWhenIncludeThenLoadInvoked) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;
  CComPtr<TestIncludeHandler> pInclude;

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText(
    "#include \"helper.h\"\r\n"
    "float4 main() : SV_Target { return 0; }", &pSource);

  pInclude = new TestIncludeHandler(m_dllSupport);
  pInclude->CallResults.emplace_back("");

  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
    L"ps_6_0", nullptr, 0, nullptr, 0, pInclude, &pResult));
  VerifyOperationSucceeded(pResult);
  VERIFY_ARE_EQUAL_WSTR(L"./helper.h;", pInclude->GetAllFileNames().c_str());
}

TEST_F(CompilerTest, CompileWhenIncludeThenLoadUsed) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;
  CComPtr<TestIncludeHandler> pInclude;

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText(
    "#include \"helper.h\"\r\n"
    "float4 main() : SV_Target { return ZERO; }", &pSource);

  pInclude = new TestIncludeHandler(m_dllSupport);
  pInclude->CallResults.emplace_back("#define ZERO 0");

  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
    L"ps_6_0", nullptr, 0, nullptr, 0, pInclude, &pResult));
  VerifyOperationSucceeded(pResult);
  VERIFY_ARE_EQUAL_WSTR(L"./helper.h;", pInclude->GetAllFileNames().c_str());
}

TEST_F(CompilerTest, CompileWhenIncludeAbsoluteThenLoadAbsolute) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;
  CComPtr<TestIncludeHandler> pInclude;

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
#ifdef _WIN32 // OS-specific root
  CreateBlobFromText(
    "#include \"C:\\helper.h\"\r\n"
    "float4 main() : SV_Target { return ZERO; }", &pSource);
#else
  CreateBlobFromText(
    "#include \"/helper.h\"\n"
    "float4 main() : SV_Target { return ZERO; }", &pSource);
#endif


  pInclude = new TestIncludeHandler(m_dllSupport);
  pInclude->CallResults.emplace_back("#define ZERO 0");

  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
    L"ps_6_0", nullptr, 0, nullptr, 0, pInclude, &pResult));
  VerifyOperationSucceeded(pResult);
#ifdef _WIN32 // OS-specific root
  VERIFY_ARE_EQUAL_WSTR(L"C:\\helper.h;", pInclude->GetAllFileNames().c_str());
#else
  VERIFY_ARE_EQUAL_WSTR(L"/helper.h;", pInclude->GetAllFileNames().c_str());
#endif
}

TEST_F(CompilerTest, CompileWhenIncludeLocalThenLoadRelative) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;
  CComPtr<TestIncludeHandler> pInclude;

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText(
    "#include \"..\\helper.h\"\r\n"
    "float4 main() : SV_Target { return ZERO; }", &pSource);

  pInclude = new TestIncludeHandler(m_dllSupport);
  pInclude->CallResults.emplace_back("#define ZERO 0");

  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
    L"ps_6_0", nullptr, 0, nullptr, 0, pInclude, &pResult));
  VerifyOperationSucceeded(pResult);
#ifdef _WIN32 // OS-specific directory dividers
  VERIFY_ARE_EQUAL_WSTR(L"./..\\helper.h;", pInclude->GetAllFileNames().c_str());
#else
  VERIFY_ARE_EQUAL_WSTR(L"./../helper.h;", pInclude->GetAllFileNames().c_str());
#endif
}

TEST_F(CompilerTest, CompileWhenIncludeSystemThenLoadNotRelative) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;
  CComPtr<TestIncludeHandler> pInclude;

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText(
    "#include \"subdir/other/file.h\"\r\n"
    "float4 main() : SV_Target { return ZERO; }", &pSource);

  LPCWSTR args[] = {
    L"-Ifoo"
  };
  pInclude = new TestIncludeHandler(m_dllSupport);
  pInclude->CallResults.emplace_back("#include <helper.h>");
  pInclude->CallResults.emplace_back("#define ZERO 0");

  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
    L"ps_6_0", args, _countof(args), nullptr, 0, pInclude, &pResult));
  VerifyOperationSucceeded(pResult);
#ifdef _WIN32 // OS-specific directory dividers
  VERIFY_ARE_EQUAL_WSTR(L"./subdir/other/file.h;./foo\\helper.h;", pInclude->GetAllFileNames().c_str());
#else
  VERIFY_ARE_EQUAL_WSTR(L"./subdir/other/file.h;./foo/helper.h;", pInclude->GetAllFileNames().c_str());
#endif
}

TEST_F(CompilerTest, CompileWhenIncludeSystemMissingThenLoadAttempt) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;
  CComPtr<TestIncludeHandler> pInclude;

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText(
    "#include \"subdir/other/file.h\"\r\n"
    "float4 main() : SV_Target { return ZERO; }", &pSource);

  pInclude = new TestIncludeHandler(m_dllSupport);
  pInclude->CallResults.emplace_back("#include <helper.h>");
  pInclude->CallResults.emplace_back("#define ZERO 0");

  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
    L"ps_6_0", nullptr, 0, nullptr, 0, pInclude, &pResult));
  std::string failLog(VerifyOperationFailed(pResult));
  VERIFY_ARE_NOT_EQUAL(std::string::npos, failLog.find("<angled>")); // error message should prompt to use <angled> rather than "quotes"
  VERIFY_ARE_EQUAL_WSTR(L"./subdir/other/file.h;./subdir/other/helper.h;", pInclude->GetAllFileNames().c_str());
}

TEST_F(CompilerTest, CompileWhenIncludeFlagsThenIncludeUsed) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;
  CComPtr<TestIncludeHandler> pInclude;

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText(
    "#include <helper.h>\r\n"
    "float4 main() : SV_Target { return ZERO; }", &pSource);

  pInclude = new TestIncludeHandler(m_dllSupport);
  pInclude->CallResults.emplace_back("#define ZERO 0");

#ifdef _WIN32  // OS-specific root
  LPCWSTR args[] = { L"-I\\\\server\\share" };
#else
  LPCWSTR args[] = { L"-I/server/share" };
#endif
  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
    L"ps_6_0", args, _countof(args), nullptr, 0, pInclude, &pResult));
  VerifyOperationSucceeded(pResult);
#ifdef _WIN32  // OS-specific root
  VERIFY_ARE_EQUAL_WSTR(L"\\\\server\\share\\helper.h;", pInclude->GetAllFileNames().c_str());
#else
  VERIFY_ARE_EQUAL_WSTR(L"/server/share/helper.h;", pInclude->GetAllFileNames().c_str());
#endif
}

TEST_F(CompilerTest, CompileWhenIncludeMissingThenFail) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;
  CComPtr<TestIncludeHandler> pInclude;

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText(
    "#include \"file.h\"\r\n"
    "float4 main() : SV_Target { return 0; }", &pSource);

  pInclude = new TestIncludeHandler(m_dllSupport);

  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
    L"ps_6_0", nullptr, 0, nullptr, 0, pInclude, &pResult));
  HRESULT hr;
  VERIFY_SUCCEEDED(pResult->GetStatus(&hr));
  VERIFY_FAILED(hr);
}

TEST_F(CompilerTest, CompileWhenIncludeHasPathThenOK) {
  CComPtr<IDxcCompiler> pCompiler;
  LPCWSTR Source = L"c:\\temp\\OddIncludes\\main.hlsl";
  LPCWSTR Args[] = { L"/I", L"c:\\temp" };
  LPCWSTR ArgsUp[] = { L"/I", L"c:\\Temp" };
  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  bool useUpValues[] = { false, true };
  for (bool useUp : useUpValues) {
    CComPtr<IDxcOperationResult> pResult;
    CComPtr<IDxcBlobEncoding> pSource;
#if TEST_ON_DISK
    CComPtr<IDxcLibrary> pLibrary;
    VERIFY_SUCCEEDED(m_dllSupport.CreateInstance(CLSID_DxcLibrary, &pLibrary));
    VERIFY_SUCCEEDED(pLibrary->CreateIncludeHandler(&pInclude));
    VERIFY_SUCCEEDED(pLibrary->CreateBlobFromFile(Source, nullptr, &pSource));
#else
    CComPtr<TestIncludeHandler> pInclude;
    pInclude = new TestIncludeHandler(m_dllSupport);
    pInclude->CallResults.emplace_back("// Empty");
    CreateBlobFromText("#include \"include.hlsl\"\r\n"
                       "float4 main() : SV_Target { return 0; }",
                       &pSource);
#endif

    VERIFY_SUCCEEDED(pCompiler->Compile(pSource, Source, L"main",
      L"ps_6_0", useUp ? ArgsUp : Args, _countof(Args), nullptr, 0, pInclude, &pResult));
    HRESULT hr;
    VERIFY_SUCCEEDED(pResult->GetStatus(&hr));
    VERIFY_SUCCEEDED(hr);
 }
}

TEST_F(CompilerTest, CompileWhenIncludeEmptyThenOK) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;
  CComPtr<TestIncludeHandler> pInclude;

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText("#include \"empty.h\"\r\n"
                     "float4 main() : SV_Target { return 0; }",
                     &pSource);

  pInclude = new TestIncludeHandler(m_dllSupport);
  pInclude->CallResults.emplace_back("", CP_ACP); // An empty file would get detected as ACP code page

  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
                                      L"ps_6_0", nullptr, 0, nullptr, 0,
                                      pInclude, &pResult));
  VerifyOperationSucceeded(pResult);
  VERIFY_ARE_EQUAL_WSTR(L"./empty.h;", pInclude->GetAllFileNames().c_str());
}

static const char EmptyCompute[] = "[numthreads(8,8,1)] void main() { }";

TEST_F(CompilerTest, CompileWhenODumpThenPassConfig) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText(EmptyCompute, &pSource);

  LPCWSTR Args[] = { L"/Odump" };

  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
    L"cs_6_0", Args, _countof(Args), nullptr, 0, nullptr, &pResult));
  VerifyOperationSucceeded(pResult);
  CComPtr<IDxcBlob> pResultBlob;
  VERIFY_SUCCEEDED(pResult->GetResult(&pResultBlob));
  wstring passes = BlobToUtf16(pResultBlob);
  VERIFY_ARE_NOT_EQUAL(wstring::npos, passes.find(L"inline"));
}

TEST_F(CompilerTest, CompileWhenVdThenProducesDxilContainer) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText(EmptyCompute, &pSource);

  LPCWSTR Args[] = { L"/Vd" };

  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
    L"cs_6_0", Args, _countof(Args), nullptr, 0, nullptr, &pResult));
  VerifyOperationSucceeded(pResult);
  CComPtr<IDxcBlob> pResultBlob;
  VERIFY_SUCCEEDED(pResult->GetResult(&pResultBlob));
  VERIFY_IS_TRUE(hlsl::IsValidDxilContainer(reinterpret_cast<hlsl::DxilContainerHeader *>(pResultBlob->GetBufferPointer()), pResultBlob->GetBufferSize()));
}

TEST_F(CompilerTest, CompileWhenODumpThenOptimizerMatch) {
  LPCWSTR OptLevels[] = { L"/Od", L"/O1", L"/O2" };
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOptimizer> pOptimizer;
  CComPtr<IDxcAssembler> pAssembler;
  CComPtr<IDxcValidator> pValidator;
  VERIFY_SUCCEEDED(m_dllSupport.CreateInstance(CLSID_DxcAssembler, &pAssembler));
  VERIFY_SUCCEEDED(m_dllSupport.CreateInstance(CLSID_DxcCompiler, &pCompiler));
  VERIFY_SUCCEEDED(m_dllSupport.CreateInstance(CLSID_DxcOptimizer, &pOptimizer));
  VERIFY_SUCCEEDED(m_dllSupport.CreateInstance(CLSID_DxcValidator, &pValidator));
  for (LPCWSTR OptLevel : OptLevels) {
    CComPtr<IDxcOperationResult> pResult;
    CComPtr<IDxcBlobEncoding> pSource;
    CComPtr<IDxcBlob> pHighLevelBlob;
    CComPtr<IDxcBlob> pOptimizedModule;
    CComPtr<IDxcBlob> pAssembledBlob;

    // Could use EmptyCompute and cs_6_0, but there is an issue where properties
    // don't round-trip properly at high-level, so validation fails because
    // dimensions are set to zero. Workaround by using pixel shader instead.
    LPCWSTR Target = L"ps_6_0";
    CreateBlobFromText("float4 main() : SV_Target { return 0; }", &pSource);

    LPCWSTR Args[2] = { OptLevel, L"/Odump" };

    // Get the passes for this optimization level.
    VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
      Target, Args, _countof(Args), nullptr, 0, nullptr, &pResult));
    VerifyOperationSucceeded(pResult);
    CComPtr<IDxcBlob> pResultBlob;
    VERIFY_SUCCEEDED(pResult->GetResult(&pResultBlob));
    wstring passes = BlobToUtf16(pResultBlob);

    // Get wchar_t version and prepend hlsl-hlensure, to do a split high-level/opt compilation pass.
    std::vector<LPCWSTR> Options;
    SplitPassList(const_cast<LPWSTR>(passes.data()), Options);

    // Now compile directly.
    pResult.Release();
    VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
      Target, Args, 1, nullptr, 0, nullptr, &pResult));
    VerifyOperationSucceeded(pResult);

    // Now compile via a high-level compile followed by the optimization passes.
    pResult.Release();
    Args[_countof(Args)-1] = L"/fcgl";
    VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
      Target, Args, _countof(Args), nullptr, 0, nullptr, &pResult));
    VerifyOperationSucceeded(pResult);
    VERIFY_SUCCEEDED(pResult->GetResult(&pHighLevelBlob));
    VERIFY_SUCCEEDED(pOptimizer->RunOptimizer(pHighLevelBlob, Options.data(),
                                              Options.size(), &pOptimizedModule,
                                              nullptr));

    string text = DisassembleProgram(m_dllSupport, pOptimizedModule);
    WEX::Logging::Log::Comment(L"Final program:");
    WEX::Logging::Log::Comment(CA2W(text.c_str()));

    // At the very least, the module should be valid.
    pResult.Release();
    VERIFY_SUCCEEDED(pAssembler->AssembleToContainer(pOptimizedModule, &pResult));
    VerifyOperationSucceeded(pResult);
    VERIFY_SUCCEEDED(pResult->GetResult(&pAssembledBlob));
    pResult.Release();
    VERIFY_SUCCEEDED(pValidator->Validate(pAssembledBlob, DxcValidatorFlags_Default, &pResult));
    VerifyOperationSucceeded(pResult);
  }
}

static const UINT CaptureStacks = 0; // Set to 1 to enable captures
static const UINT StackFrameCount = 12;

struct InstrumentedHeapMalloc : public IMalloc {
private:
  HANDLE m_Handle;        // Heap handle.
  ULONG m_RefCount = 0;   // Reference count. Used for reference leaks, not for lifetime.
  ULONG m_AllocCount = 0; // Total # of alloc and realloc requests.
  ULONG m_AllocSize = 0;  // Total # of alloc and realloc bytes.
  ULONG m_Size = 0;       // Current # of alloc'ed bytes.
  ULONG m_FailAlloc = 0;  // If nonzero, the alloc/realloc call to fail.
  // Each allocation also tracks the following information:
  // - allocation callstack
  // - deallocation callstack
  // - prior/next blocks in a list of allocated blocks
  LIST_ENTRY AllocList;
  struct PtrData {
    LIST_ENTRY Entry;
    LPVOID AllocFrames[CaptureStacks ? StackFrameCount * CaptureStacks : 1];
    LPVOID FreeFrames[CaptureStacks ? StackFrameCount * CaptureStacks : 1];
    UINT64 AllocAtCount;
    DWORD AllocFrameCount;
    DWORD FreeFrameCount;
    SIZE_T Size;
    PtrData *Self;
  };
  PtrData *DataFromPtr(void *p) {
    if (p == nullptr) return nullptr;
    PtrData *R = ((PtrData *)p) - 1;
    if (R != R->Self) {
      VERIFY_FAIL(); // p is invalid or underrun
    }
    return R;
  }
public:
  InstrumentedHeapMalloc() : m_Handle(nullptr) {
    ResetCounts();
  }
  ~InstrumentedHeapMalloc() {
    if (m_Handle)
      HeapDestroy(m_Handle);
  }
  void ResetHeap() {
    if (m_Handle) {
      HeapDestroy(m_Handle);
      m_Handle = nullptr;
    }
    m_Handle = HeapCreate(HEAP_NO_SERIALIZE, 0, 0);
  }
  ULONG GetRefCount() const { return m_RefCount; }
  ULONG GetAllocCount() const { return m_AllocCount; }
  ULONG GetAllocSize() const { return m_AllocSize; }
  ULONG GetSize() const { return m_Size; }

  void ResetCounts() {
    m_RefCount = m_AllocCount = m_AllocSize = m_Size = 0;
    AllocList.Blink = AllocList.Flink = &AllocList;
  }
  void SetFailAlloc(ULONG index) {
    m_FailAlloc = index;
  }

  ULONG STDMETHODCALLTYPE AddRef() {
    return ++m_RefCount;
  }
  ULONG STDMETHODCALLTYPE Release() {
    if (m_RefCount == 0) VERIFY_FAIL();
    return --m_RefCount;
  }
  STDMETHODIMP QueryInterface(REFIID iid, void** ppvObject) {
    return DoBasicQueryInterface<IMalloc>(this, iid, ppvObject);
  }
  virtual void *STDMETHODCALLTYPE Alloc(_In_ SIZE_T cb) {
    ++m_AllocCount;
    if (m_FailAlloc && m_AllocCount >= m_FailAlloc) {
      return nullptr; // breakpoint for i failure - m_FailAlloc == 1+VAL
    }
    m_AllocSize += cb;
    m_Size += cb;
    PtrData *P = (PtrData *)HeapAlloc(m_Handle, HEAP_ZERO_MEMORY, sizeof(PtrData) + cb);
    P->Entry.Flink = AllocList.Flink;
    P->Entry.Blink = &AllocList;
    AllocList.Flink->Blink = &(P->Entry);
    AllocList.Flink = &(P->Entry);
    // breakpoint for i failure on NN alloc - m_FailAlloc == 1+VAL && m_AllocCount == NN
    // breakpoint for happy path for NN alloc - m_AllocCount == NN
    P->AllocAtCount = m_AllocCount;
    if (CaptureStacks)
      P->AllocFrameCount = CaptureStackBackTrace(1, StackFrameCount, P->AllocFrames, nullptr);
    P->Size = cb;
    P->Self = P;
    return P + 1;
  }

  virtual void *STDMETHODCALLTYPE Realloc(_In_opt_ void *pv, _In_ SIZE_T cb) {
    SIZE_T priorSize = pv == nullptr ? (SIZE_T)0 : GetSize(pv);
    void *R = Alloc(cb);
    if (!R)
      return nullptr;
    SIZE_T copySize = std::min(cb, priorSize);
    memcpy(R, pv, copySize);
    Free(pv);
    return R;
  }

  virtual void STDMETHODCALLTYPE Free(_In_opt_ void *pv) {
    if (!pv)
      return;
    PtrData *P = DataFromPtr(pv);
    if (P->FreeFrameCount)
      VERIFY_FAIL(); // double-free detected
    m_Size -= P->Size;
    P->Entry.Flink->Blink = P->Entry.Blink;
    P->Entry.Blink->Flink = P->Entry.Flink;
    if (CaptureStacks)
      P->FreeFrameCount =
          CaptureStackBackTrace(1, StackFrameCount, P->FreeFrames, nullptr);
  }

  virtual SIZE_T STDMETHODCALLTYPE GetSize(
    /* [annotation][in] */
    _In_opt_ _Post_writable_byte_size_(return)  void *pv)
  {
    if (pv == nullptr) return 0;
    return DataFromPtr(pv)->Size;
  }

  virtual int STDMETHODCALLTYPE DidAlloc(
      _In_opt_ void *pv) {
    return -1; // don't know
  }

  virtual void STDMETHODCALLTYPE HeapMinimize(void) {}

  void DumpLeaks() {
    PtrData *ptr = (PtrData*)AllocList.Flink;;
    PtrData *end = (PtrData*)AllocList.Blink;;

    WEX::Logging::Log::Comment(FormatToWString(L"Leaks total size: %d", (signed int)m_Size).data());
    while (ptr != end) {
      WEX::Logging::Log::Comment(FormatToWString(L"Memory leak at 0x0%X, size %d, alloc# %d", ptr + 1, ptr->Size, ptr->AllocAtCount).data());
      ptr = (PtrData*)ptr->Entry.Flink;
    }
  }
};

#if _ITERATOR_DEBUG_LEVEL==0
// CompileWhenNoMemThenOOM can properly detect leaks only when debug iterators are disabled
TEST_F(CompilerTest, CompileWhenNoMemThenOOM) {
  WEX::TestExecution::SetVerifyOutput verifySettings(WEX::TestExecution::VerifyOutputSettings::LogOnlyFailures);

  CComPtr<IDxcBlobEncoding> pSource;
  CreateBlobFromText(EmptyCompute, &pSource);

  InstrumentedHeapMalloc InstrMalloc;
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  ULONG allocCount = 0;
  ULONG allocSize = 0;
  ULONG initialRefCount;

  InstrMalloc.ResetHeap();

  VERIFY_IS_TRUE(m_dllSupport.HasCreateWithMalloc());

  // Verify a simple object creation.
  initialRefCount = InstrMalloc.GetRefCount();
  VERIFY_SUCCEEDED(m_dllSupport.CreateInstance2(&InstrMalloc, CLSID_DxcCompiler, &pCompiler));
  pCompiler.Release();
  VERIFY_IS_TRUE(0 == InstrMalloc.GetSize());
  VERIFY_ARE_EQUAL(initialRefCount, InstrMalloc.GetRefCount());
  InstrMalloc.ResetCounts();
  InstrMalloc.ResetHeap();

  // First time, run to completion and capture stats.
  initialRefCount = InstrMalloc.GetRefCount();
  VERIFY_SUCCEEDED(m_dllSupport.CreateInstance2(&InstrMalloc, CLSID_DxcCompiler, &pCompiler));
  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
    L"cs_6_0", nullptr, 0, nullptr, 0, nullptr, &pResult));
  allocCount = InstrMalloc.GetAllocCount();
  allocSize = InstrMalloc.GetAllocSize();

  HRESULT hrWithMemory;
  VERIFY_SUCCEEDED(pResult->GetStatus(&hrWithMemory));
  VERIFY_SUCCEEDED(hrWithMemory);

  pCompiler.Release();
  pResult.Release();

  VERIFY_IS_TRUE(allocSize > allocCount);

  // Ensure that after all resources are released, there are no outstanding
  // allocations or references.
  //
  // First leak is in ((InstrumentedHeapMalloc::PtrData *)InstrMalloc.AllocList.Flink)
  if (InstrMalloc.GetSize() != 0) {
    WEX::Logging::Log::Comment(L"Memory leak(s) detected");
    InstrMalloc.DumpLeaks();
    VERIFY_IS_TRUE(0 == InstrMalloc.GetSize());
  }

  VERIFY_ARE_EQUAL(initialRefCount, InstrMalloc.GetRefCount());

  // In Debug, without /D_ITERATOR_DEBUG_LEVEL=0, debug iterators will be used;
  // this causes a problem where std::string is specified as noexcept, and yet
  // a sentinel is allocated that may fail and throw.
  if (m_ver.SkipOutOfMemoryTest()) return;

  // Now, fail each allocation and make sure we get an error.
  for (ULONG i = 0; i <= allocCount; ++i) {
    // LogCommentFmt(L"alloc fail %u", i);
    bool isLast = i == allocCount;
    InstrMalloc.ResetCounts();
    InstrMalloc.ResetHeap();
    InstrMalloc.SetFailAlloc(i + 1);
    HRESULT hrOp = m_dllSupport.CreateInstance2(&InstrMalloc, CLSID_DxcCompiler, &pCompiler);
    if (SUCCEEDED(hrOp)) {
      hrOp = pCompiler->Compile(pSource, L"source.hlsl", L"main", L"cs_6_0",
                                nullptr, 0, nullptr, 0, nullptr, &pResult);
      if (SUCCEEDED(hrOp)) {
        pResult->GetStatus(&hrOp);
      }
    }
    if (FAILED(hrOp)) {
      // This is true in *almost* every case. When the OOM happens during stream
      // handling, there is no specific error set; by the time it's detected,
      // it propagates as E_FAIL.
      //VERIFY_ARE_EQUAL(hrOp, E_OUTOFMEMORY);
      VERIFY_IS_TRUE(hrOp == E_OUTOFMEMORY || hrOp == E_FAIL);
    }
    if (isLast)
      VERIFY_SUCCEEDED(hrOp);
    else
      VERIFY_FAILED(hrOp);
    pCompiler.Release();
    pResult.Release();
    
    if (InstrMalloc.GetSize() != 0) {
      WEX::Logging::Log::Comment(FormatToWString(L"Memory leak(s) detected, allocCount = %d", i).data()); 
      InstrMalloc.DumpLeaks();
      VERIFY_IS_TRUE(0 == InstrMalloc.GetSize());
    }
    VERIFY_ARE_EQUAL(initialRefCount, InstrMalloc.GetRefCount());
  }
}
#endif

TEST_F(CompilerTest, CompileWhenShaderModelMismatchAttributeThenFail) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText(EmptyCompute, &pSource);

  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
    L"ps_6_0", nullptr, 0, nullptr, 0, nullptr, &pResult));
  std::string failLog(VerifyOperationFailed(pResult));
  VERIFY_ARE_NOT_EQUAL(string::npos, failLog.find("attribute numthreads only valid for CS"));
}

TEST_F(CompilerTest, CompileBadHlslThenFail) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText(
    "bad hlsl", &pSource);

  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
    L"ps_6_0", nullptr, 0, nullptr, 0, nullptr, &pResult));

  HRESULT status;
  VERIFY_SUCCEEDED(pResult->GetStatus(&status));
  VERIFY_FAILED(status);
}

TEST_F(CompilerTest, CompileLegacyShaderModelThenFail) {
  VerifyCompileFailed(
    "float4 main(float4 pos : SV_Position) : SV_Target { return pos; }", L"ps_5_1", nullptr);
}

TEST_F(CompilerTest, CompileWhenRecursiveAlbeitStaticTermThenFail) {
  // This shader will compile under fxc because if execution is
  // simulated statically, it does terminate. dxc changes this behavior
  // to avoid imposing the requirement on the compiler.
  const char ShaderText[] =
    "static int i = 10;\r\n"
    "float4 f(); // Forward declaration\r\n"
    "float4 g() { if (i > 10) { i--; return f(); } else return 0; } // Recursive call to 'f'\r\n"
    "float4 f() { return g(); } // First call to 'g'\r\n"
    "float4 VS() : SV_Position{\r\n"
    "  return f(); // First call to 'f'\r\n"
    "}\r\n";
  VerifyCompileFailed(ShaderText, L"vs_6_0", "recursive functions not allowed", L"VS");
}

TEST_F(CompilerTest, CompileWhenRecursiveThenFail) {
  const char ShaderTextSimple[] =
    "float4 f(); // Forward declaration\r\n"
    "float4 g() { return f(); } // Recursive call to 'f'\r\n"
    "float4 f() { return g(); } // First call to 'g'\r\n"
    "float4 main() : SV_Position{\r\n"
    "  return f(); // First call to 'f'\r\n"
    "}\r\n";
  VerifyCompileFailed(ShaderTextSimple, L"vs_6_0", "recursive functions not allowed");

  const char ShaderTextIndirect[] =
    "float4 f(); // Forward declaration\r\n"
    "float4 g() { return f(); } // Recursive call to 'f'\r\n"
    "float4 f() { return g(); } // First call to 'g'\r\n"
    "float4 main() : SV_Position{\r\n"
    "  return f(); // First call to 'f'\r\n"
    "}\r\n";
  VerifyCompileFailed(ShaderTextIndirect, L"vs_6_0", "recursive functions not allowed");

  const char ShaderTextSelf[] =
    "float4 main() : SV_Position{\r\n"
    "  return main();\r\n"
    "}\r\n";
  VerifyCompileFailed(ShaderTextSelf, L"vs_6_0", "recursive functions not allowed");

  const char ShaderTextMissing[] =
    "float4 mainz() : SV_Position{\r\n"
    "  return 1;\r\n"
    "}\r\n";
  VerifyCompileFailed(ShaderTextMissing, L"vs_6_0", "missing entry point definition");
}

TEST_F(CompilerTest, CompileHlsl2015ThenFail) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;
  CComPtr<IDxcBlobEncoding> pErrors;

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText("float4 main(float4 pos : SV_Position) : SV_Target { return pos; }", &pSource);

  LPCWSTR args[2] = { L"-HV", L"2015" };

  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
    L"ps_6_0", args, 2, nullptr, 0, nullptr, &pResult));

  HRESULT status;
  VERIFY_SUCCEEDED(pResult->GetStatus(&status));
  VERIFY_ARE_EQUAL(status, E_INVALIDARG);
  VERIFY_SUCCEEDED(pResult->GetErrorBuffer(&pErrors));
  LPCSTR pErrorMsg = "HLSL Version 2015 is only supported for language services";
  CheckOperationResultMsgs(pResult, &pErrorMsg, 1, false, false);
}

TEST_F(CompilerTest, CompileHlsl2016ThenOK) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;
  CComPtr<IDxcBlobEncoding> pErrors;

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText("float4 main(float4 pos : SV_Position) : SV_Target { return pos; }", &pSource);

  LPCWSTR args[2] = { L"-HV", L"2016" };

  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
    L"ps_6_0", args, 2, nullptr, 0, nullptr, &pResult));

  HRESULT status;
  VERIFY_SUCCEEDED(pResult->GetStatus(&status));
  VERIFY_SUCCEEDED(status);
}

TEST_F(CompilerTest, CompileHlsl2017ThenOK) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;
  CComPtr<IDxcBlobEncoding> pErrors;

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText("float4 main(float4 pos : SV_Position) : SV_Target { return pos; }", &pSource);

  LPCWSTR args[2] = { L"-HV", L"2017" };

  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
    L"ps_6_0", args, 2, nullptr, 0, nullptr, &pResult));

  HRESULT status;
  VERIFY_SUCCEEDED(pResult->GetStatus(&status));
  VERIFY_SUCCEEDED(status);
}

TEST_F(CompilerTest, CompileHlsl2018ThenOK) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;
  CComPtr<IDxcBlobEncoding> pErrors;

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText("float4 main(float4 pos : SV_Position) : SV_Target { return pos; }", &pSource);

  LPCWSTR args[2] = { L"-HV", L"2018" };

  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
    L"ps_6_0", args, 2, nullptr, 0, nullptr, &pResult));

  HRESULT status;
  VERIFY_SUCCEEDED(pResult->GetStatus(&status));
  VERIFY_SUCCEEDED(status);
}

TEST_F(CompilerTest, CompileHlsl2019ThenFail) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;
  CComPtr<IDxcBlobEncoding> pErrors;

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText("float4 main(float4 pos : SV_Position) : SV_Target { return pos; }", &pSource);

  LPCWSTR args[2] = { L"-HV", L"2019" };

  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
    L"ps_6_0", args, 2, nullptr, 0, nullptr, &pResult));

  HRESULT status;
  VERIFY_SUCCEEDED(pResult->GetStatus(&status));
  VERIFY_ARE_EQUAL(status, E_INVALIDARG);
  VERIFY_SUCCEEDED(pResult->GetErrorBuffer(&pErrors));
  LPCSTR pErrorMsg = "Unknown HLSL version";
  CheckOperationResultMsgs(pResult, &pErrorMsg, 1, false, false);
}

#ifdef _WIN32

#pragma fenv_access(on)
#pragma optimize("", off)
#pragma warning(disable : 4723)

// Define test state as something weird that we can verify was restored
static const unsigned int fpTestState =
    (_MCW_EM & (~_EM_ZERODIVIDE)) |   // throw on div by zero
    _DN_FLUSH_OPERANDS_SAVE_RESULTS | // denorm flush operands & save results
    _RC_UP;                           // round up
static const unsigned int fpTestMask = _MCW_EM | _MCW_DN | _MCW_RC;

struct FPTestScope
{
  // _controlfp_s is non-standard and <cfenv> doesn't have a function to enable exceptions
  unsigned int fpSavedState;
  FPTestScope() {
    VERIFY_IS_TRUE(_controlfp_s(&fpSavedState, 0, 0) == 0);
    unsigned int newValue;
    VERIFY_IS_TRUE(_controlfp_s(&newValue, fpTestState, fpTestMask) == 0);
  }
  ~FPTestScope() {
    unsigned int newValue;
    errno_t error = _controlfp_s(&newValue, fpSavedState, fpTestMask);
    DXASSERT_LOCALVAR(error, error == 0, "Failed to restore floating-point environment.");
  }
};

void VerifyDivByZeroThrows() {
  bool bCaughtExpectedException = false;
  __try {
    float one = 1.0;
    float zero = 0.0;
    float val = one / zero;
    (void)val;
  } __except(EXCEPTION_EXECUTE_HANDLER) {
    bCaughtExpectedException = true;
  }
  VERIFY_IS_TRUE(bCaughtExpectedException);
}

TEST_F(CompilerTest, CodeGenFloatingPointEnvironment) {
  unsigned int fpOriginal;
  VERIFY_IS_TRUE(_controlfp_s(&fpOriginal, 0, 0) == 0);

  {
    FPTestScope fpTestScope;
    // Get state before/after compilation, making sure it's our test state,
    // and that it is restored after the compile.
    unsigned int fpBeforeCompile;
    VERIFY_IS_TRUE(_controlfp_s(&fpBeforeCompile, 0, 0) == 0);
    VERIFY_ARE_EQUAL((fpBeforeCompile & fpTestMask), fpTestState);

    CodeGenTestCheck(L"fpexcept.hlsl");

    // Verify excpetion environment was restored
    unsigned int fpAfterCompile;
    VERIFY_IS_TRUE(_controlfp_s(&fpAfterCompile, 0, 0) == 0);
    VERIFY_ARE_EQUAL((fpBeforeCompile & fpTestMask), (fpAfterCompile & fpTestMask));

    // Make sure round up is set
    VERIFY_ARE_EQUAL(rint(12.25), 13);

    // Make sure we actually enabled div-by-zero exception
    VerifyDivByZeroThrows();
  }

  // Verify original state has been restored
  unsigned int fpLocal;
  VERIFY_IS_TRUE(_controlfp_s(&fpLocal, 0, 0) == 0);
  VERIFY_ARE_EQUAL(fpLocal, fpOriginal);
}

#pragma optimize("", on)

#else   // _WIN32

// Only implemented on Win32
TEST_F(CompilerTest, CodeGenFloatingPointEnvironment) {
  VERIFY_IS_TRUE(true);
}

#endif  // _WIN32

TEST_F(CompilerTest, CodeGenInclude) {
  CodeGenTestCheck(L"Include.hlsl");
}

TEST_F(CompilerTest, CodeGenLibCsEntry) {
  CodeGenTestCheck(L"lib_cs_entry.hlsl");
}

TEST_F(CompilerTest, CodeGenLibCsEntry2) {
  CodeGenTestCheck(L"lib_cs_entry2.hlsl");
}

TEST_F(CompilerTest, CodeGenLibCsEntry3) {
  CodeGenTestCheck(L"lib_cs_entry3.hlsl");
}

TEST_F(CompilerTest, CodeGenLibEntries) {
  CodeGenTestCheck(L"lib_entries.hlsl");
}

TEST_F(CompilerTest, CodeGenLibEntries2) {
  CodeGenTestCheck(L"lib_entries2.hlsl");
}

TEST_F(CompilerTest, CodeGenLibNoAlias) {
  CodeGenTestCheck(L"lib_no_alias.hlsl");
}

TEST_F(CompilerTest, CodeGenLibResource) {
  CodeGenTestCheck(L"lib_resource.hlsl");
}

TEST_F(CompilerTest, CodeGenLibUnusedFunc) {
  CodeGenTestCheck(L"lib_unused_func.hlsl");
}

TEST_F(CompilerTest, CodeGenRootSigProfile) {
  if (m_ver.SkipDxilVersion(1, 5)) return;
  CodeGenTest(L"rootSigProfile.hlsl");
}

TEST_F(CompilerTest, CodeGenRootSigProfile2) {
  if (m_ver.SkipDxilVersion(1, 5)) return;
  // TODO: Verify the result when reflect the structures.
  CodeGenTest(L"rootSigProfile2.hlsl");
}

TEST_F(CompilerTest, CodeGenRootSigProfile5) {
  if (m_ver.SkipDxilVersion(1, 5)) return;
  CodeGenTest(L"rootSigProfile5.hlsl");
}

TEST_F(CompilerTest, CodeGenWaveSize) {
  CodeGenTestCheck(L"attributes_wavesize.hlsl");
}

TEST_F(CompilerTest, LibGVStore) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;
  CComPtr<IDxcContainerReflection> pReflection;
  CComPtr<IDxcAssembler> pAssembler;

  VERIFY_SUCCEEDED(this->m_dllSupport.CreateInstance(CLSID_DxcContainerReflection, &pReflection));
  VERIFY_SUCCEEDED(this->m_dllSupport.CreateInstance(CLSID_DxcAssembler, &pAssembler));
  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText(
    R"(
      struct T {
      RWByteAddressBuffer outputBuffer;
      RWByteAddressBuffer outputBuffer2;
      };

      struct D {
        float4 a;
        int4 b;
      };

      struct T2 {
         RWStructuredBuffer<D> uav;
      };

      T2 resStruct(T t, uint2 id);

      RWByteAddressBuffer outputBuffer;
      RWByteAddressBuffer outputBuffer2;

      [numthreads(8, 8, 1)]
      void main( uint2 id : SV_DispatchThreadID )
      {
          T t = {outputBuffer,outputBuffer2};
          T2 t2 = resStruct(t, id);
          uint counter = t2.uav.IncrementCounter();
          t2.uav[counter].b.xy = id;
      }
    )", &pSource);

  const WCHAR *pArgs[] = {
    L"/Zi",
  };
  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"file.hlsl", L"", L"lib_6_x",
                                         pArgs, _countof(pArgs), nullptr, 0, nullptr,
                                         &pResult));

  CComPtr<IDxcBlob> pShader;
  VERIFY_SUCCEEDED(pResult->GetResult(&pShader));
  VERIFY_SUCCEEDED(pReflection->Load(pShader));

  UINT32 index = 0;
  VERIFY_SUCCEEDED(pReflection->FindFirstPartKind(hlsl::DFCC_DXIL, &index));

  CComPtr<IDxcBlob> pBitcode;
  VERIFY_SUCCEEDED(pReflection->GetPartContent(index, &pBitcode));

  const char *bitcode = hlsl::GetDxilBitcodeData((hlsl::DxilProgramHeader *)pBitcode->GetBufferPointer());
  unsigned bitcode_size = hlsl::GetDxilBitcodeSize((hlsl::DxilProgramHeader *)pBitcode->GetBufferPointer());

  CComPtr<IDxcBlobEncoding> pBitcodeBlob;
  CreateBlobPinned(bitcode, bitcode_size, CP_UTF8, &pBitcodeBlob);

  CComPtr<IDxcBlob> pReassembled;
  CComPtr<IDxcOperationResult> pReassembleResult;
  VERIFY_SUCCEEDED(pAssembler->AssembleToContainer(pBitcodeBlob, &pReassembleResult));
  VERIFY_SUCCEEDED(pReassembleResult->GetResult(&pReassembled));

  CComPtr<IDxcBlobEncoding> pTextBlob;
  VERIFY_SUCCEEDED(pCompiler->Disassemble(pReassembled, &pTextBlob));

  std::wstring Text = BlobToUtf16(pTextBlob);
  VERIFY_ARE_NOT_EQUAL(std::wstring::npos, Text.find(L"store"));
}

TEST_F(CompilerTest, PreprocessWhenValidThenOK) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;
  DxcDefine defines[2];
  defines[0].Name = L"MYDEF";
  defines[0].Value = L"int";
  defines[1].Name = L"MYOTHERDEF";
  defines[1].Value = L"123";
  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText(
    "// First line\r\n"
    "MYDEF g_int = MYOTHERDEF;\r\n"
    "#define FOO BAR\r\n"
    "int FOO;", &pSource);
  VERIFY_SUCCEEDED(pCompiler->Preprocess(pSource, L"file.hlsl", nullptr, 0,
                                         defines, _countof(defines), nullptr,
                                         &pResult));
  HRESULT hrOp;
  VERIFY_SUCCEEDED(pResult->GetStatus(&hrOp));
  VERIFY_SUCCEEDED(hrOp);

  CComPtr<IDxcBlob> pOutText;
  VERIFY_SUCCEEDED(pResult->GetResult(&pOutText));
  std::string text(BlobToUtf8(pOutText));
  VERIFY_ARE_EQUAL_STR(
    "#line 1 \"file.hlsl\"\n"
    "\n"
    "int g_int = 123;\n"
    "\n"
    "int BAR;\n", text.c_str());
}

TEST_F(CompilerTest, PreprocessWhenExpandTokenPastingOperandThenAccept) {
  // Tests that we can turn on fxc's behavior (pre-expanding operands before
  // performing token-pasting) using -flegacy-macro-expansion

  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;

  LPCWSTR expandOption = L"-flegacy-macro-expansion";

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));

  CreateBlobFromText(R"(
#define SET_INDEX0                10
#define BINDING_INDEX0            5

#define SET(INDEX)                SET_INDEX##INDEX
#define BINDING(INDEX)            BINDING_INDEX##INDEX

#define SET_BIND(NAME,SET,BIND)   resource_set_##SET##_bind_##BIND##_##NAME

#define RESOURCE(NAME,INDEX)      SET_BIND(NAME, SET(INDEX), BINDING(INDEX))

    Texture2D<float4> resource_set_10_bind_5_tex;

  float4 main() : SV_Target{
    return RESOURCE(tex, 0)[uint2(1, 2)];
  }
)",
                     &pSource);
  VERIFY_SUCCEEDED(pCompiler->Preprocess(pSource, L"file.hlsl", &expandOption,
                                         1, nullptr, 0, nullptr, &pResult));
  HRESULT hrOp;
  VERIFY_SUCCEEDED(pResult->GetStatus(&hrOp));
  VERIFY_SUCCEEDED(hrOp);

  CComPtr<IDxcBlob> pOutText;
  VERIFY_SUCCEEDED(pResult->GetResult(&pOutText));
  std::string text(BlobToUtf8(pOutText));
  VERIFY_ARE_EQUAL_STR(R"(#line 1 "file.hlsl"
#line 12 "file.hlsl"
    Texture2D<float4> resource_set_10_bind_5_tex;

  float4 main() : SV_Target{
    return resource_set_10_bind_5_tex[uint2(1, 2)];
  }
)",
                       text.c_str());
}

TEST_F(CompilerTest, PreprocessWithDebugOptsThenOk) {
  // Make sure debug options, such as -Zi and -Fd,
  // are simply ignored when preprocessing

  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;
  DxcDefine defines[2];
  defines[0].Name = L"MYDEF";
  defines[0].Value = L"int";
  defines[1].Name = L"MYOTHERDEF";
  defines[1].Value = L"123";
  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText(
    "// First line\r\n"
    "MYDEF g_int = MYOTHERDEF;\r\n"
    "#define FOO BAR\r\n"
    "int FOO;", &pSource);

  LPCWSTR extraOptions[] = {L"-Zi", L"-Fd", L"file.pdb", L"-Qembed_debug"};

  VERIFY_SUCCEEDED(pCompiler->Preprocess(pSource, L"file.hlsl",
    extraOptions, _countof(extraOptions),
    defines, _countof(defines), nullptr,
    &pResult));
  HRESULT hrOp;
  VERIFY_SUCCEEDED(pResult->GetStatus(&hrOp));
  VERIFY_SUCCEEDED(hrOp);

  CComPtr<IDxcBlob> pOutText;
  VERIFY_SUCCEEDED(pResult->GetResult(&pOutText));
  std::string text(BlobToUtf8(pOutText));
  VERIFY_ARE_EQUAL_STR(
    "#line 1 \"file.hlsl\"\n"
    "\n"
    "int g_int = 123;\n"
    "\n"
    "int BAR;\n", text.c_str());
}

TEST_F(CompilerTest, CompileOtherModesWithDebugOptsThenOk) {
  // Make sure debug options, such as -Zi and -Fd,
  // are simply ignored when compiling in modes:
  // /Odump -ast-dump -fcgl -rootsig_1_0

  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcBlobEncoding> pSource;
  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText(
    "#define RS \"CBV(b0)\"\n"
    "[RootSignature(RS)]\n"
    "float main(float i : IN) : OUT { return i * 2.0F; }",
    &pSource);

  auto testWithOpts = [&](LPCWSTR entry, LPCWSTR target, llvm::ArrayRef<LPCWSTR> mainOpts) -> HRESULT {
    std::vector<LPCWSTR> opts(mainOpts);
    opts.insert(opts.end(), {L"-Zi", L"-Fd", L"file.pdb"});
    CComPtr<IDxcOperationResult> pResult;
    VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"file.hlsl",
      entry, target, opts.data(), opts.size(),
      nullptr, 0, nullptr, &pResult));
    HRESULT hrOp;
    VERIFY_SUCCEEDED(pResult->GetStatus(&hrOp));
    return hrOp;
  };
  VERIFY_SUCCEEDED(testWithOpts(L"main", L"vs_6_0", {L"/Odump"}));
  VERIFY_SUCCEEDED(testWithOpts(L"main", L"vs_6_0", {L"-ast-dump"}));
  VERIFY_SUCCEEDED(testWithOpts(L"main", L"vs_6_0", {L"-fcgl"}));
  VERIFY_SUCCEEDED(testWithOpts(L"RS", L"rootsig_1_0", {}));
}

TEST_F(CompilerTest, WhenSigMismatchPCFunctionThenFail) {
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;

  VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));
  CreateBlobFromText(
    "struct PSSceneIn \n\
    { \n\
      float4 pos  : SV_Position; \n\
      float2 tex  : TEXCOORD0; \n\
      float3 norm : NORMAL; \n\
    }; \n"
    "struct HSPerPatchData {  \n\
      float edges[ 3 ] : SV_TessFactor; \n\
      float inside : SV_InsideTessFactor; \n\
      float foo : FOO; \n\
    }; \n"
    "HSPerPatchData HSPerPatchFunc( InputPatch< PSSceneIn, 3 > points, \n\
      OutputPatch<PSSceneIn, 3> outpoints) { \n\
      HSPerPatchData d = (HSPerPatchData)0; \n\
      d.edges[ 0 ] = points[0].tex.x + outpoints[0].tex.x; \n\
      d.edges[ 1 ] = 1; \n\
      d.edges[ 2 ] = 1; \n\
      d.inside = 1; \n\
      return d; \n\
    } \n"
    "[domain(\"tri\")] \n\
    [partitioning(\"fractional_odd\")] \n\
    [outputtopology(\"triangle_cw\")] \n\
    [patchconstantfunc(\"HSPerPatchFunc\")] \n\
    [outputcontrolpoints(3)] \n"
    "void main(const uint id : SV_OutputControlPointID, \n\
               const InputPatch< PSSceneIn, 3 > points ) { \n\
    } \n"
    , &pSource);

  VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"main",
    L"hs_6_0", nullptr, 0, nullptr, 0, nullptr, &pResult));
  std::string failLog(VerifyOperationFailed(pResult));
  VERIFY_ARE_NOT_EQUAL(string::npos, failLog.find(
    "Signature element SV_Position, referred to by patch constant function, is not found in corresponding hull shader output."));
}

TEST_F(CompilerTest, SubobjectCodeGenErrors) {
  struct SubobjectErrorTestCase {
    const char *shaderText;
    const char *expectedError;
  };
  SubobjectErrorTestCase testCases[] = {
    { "GlobalRootSignature grs;",           "1:1: error: subobject needs to be initialized" },
    { "StateObjectConfig soc;",             "1:1: error: subobject needs to be initialized" },
    { "LocalRootSignature lrs;",            "1:1: error: subobject needs to be initialized" },
    { "SubobjectToExportsAssociation sea;", "1:1: error: subobject needs to be initialized" },
    { "RaytracingShaderConfig rsc;",        "1:1: error: subobject needs to be initialized" },
    { "RaytracingPipelineConfig rpc;",      "1:1: error: subobject needs to be initialized" },
    { "RaytracingPipelineConfig1 rpc1;",    "1:1: error: subobject needs to be initialized" },
    { "TriangleHitGroup hitGt;",            "1:1: error: subobject needs to be initialized" },
    { "ProceduralPrimitiveHitGroup hitGt;", "1:1: error: subobject needs to be initialized" },
    { "GlobalRootSignature grs2 = {\"\"};", "1:29: error: empty string not expected here" },
    { "LocalRootSignature lrs2 = {\"\"};",  "1:28: error: empty string not expected here" },
    { "SubobjectToExportsAssociation sea2 = { \"\", \"x\" };", "1:40: error: empty string not expected here" },
    { "string s; SubobjectToExportsAssociation sea4 = { \"x\", s };", "1:55: error: cannot convert to constant string" },
    { "extern int v; RaytracingPipelineConfig rpc2 = { v + 16 };", "1:49: error: cannot convert to constant unsigned int" },
    { "string s; TriangleHitGroup trHitGt2_8 = { s, \"foo\" };", "1:43: error: cannot convert to constant string" },
    { "string s; ProceduralPrimitiveHitGroup ppHitGt2_8 = { s, \"\", s };", "1:54: error: cannot convert to constant string" },
    { "ProceduralPrimitiveHitGroup ppHitGt2_9 = { \"a\", \"b\", \"\"};", "1:54: error: empty string not expected here" }
  };

  for (unsigned i = 0; i < _countof(testCases); i++) {
    CComPtr<IDxcCompiler> pCompiler;
    CComPtr<IDxcOperationResult> pResult;
    CComPtr<IDxcBlobEncoding> pSource;
    VERIFY_SUCCEEDED(CreateCompiler(&pCompiler));

    CreateBlobFromText(testCases[i].shaderText, &pSource);
    VERIFY_SUCCEEDED(pCompiler->Compile(pSource, L"source.hlsl", L"", L"lib_6_4", nullptr, 0, nullptr, 0, nullptr, &pResult));
    std::string failLog(VerifyOperationFailed(pResult));
    VERIFY_ARE_NOT_EQUAL(string::npos, failLog.find(testCases[i].expectedError));
  }
}

#ifdef _WIN32
TEST_F(CompilerTest, ManualFileCheckTest) {
#else
TEST_F(CompilerTest, DISABLED_ManualFileCheckTest) {
#endif
  using namespace llvm;
  using namespace WEX::TestExecution;

  WEX::Common::String value;
  VERIFY_SUCCEEDED(RuntimeParameters::TryGetValue(L"InputPath", value));

  std::wstring path = value;
  if (!llvm::sys::path::is_absolute(CW2A(path.c_str()).m_psz)) {
    path = hlsl_test::GetPathToHlslDataFile(path.c_str());
  }

  bool isDirectory;
  {
    // Temporarily setup the filesystem for testing whether the path is a directory.
    // If it is, CodeGenTestCheckBatchDir will create its own instance.
    llvm::sys::fs::MSFileSystem *msfPtr;
    VERIFY_SUCCEEDED(CreateMSFileSystemForDisk(&msfPtr));
    std::unique_ptr<llvm::sys::fs::MSFileSystem> msf(msfPtr);
    llvm::sys::fs::AutoPerThreadSystem pts(msf.get());
    IFTLLVM(pts.error_code());
    isDirectory = llvm::sys::fs::is_directory(CW2A(path.c_str()).m_psz);
  }

  if (isDirectory) {
    CodeGenTestCheckBatchDir(path, /*implicitDir*/ false);
  } else {
    CodeGenTestCheck(path.c_str(), /*implicitDir*/ false);
  }
}


TEST_F(CompilerTest, CodeGenHashStability) {
  CodeGenTestCheckBatchHash(L"");
}

TEST_F(CompilerTest, BatchD3DReflect) {
  CodeGenTestCheckBatchDir(L"d3dreflect");
}

TEST_F(CompilerTest, BatchDxil) {
  CodeGenTestCheckBatchDir(L"dxil");
}

TEST_F(CompilerTest, BatchHLSL) {
  CodeGenTestCheckBatchDir(L"hlsl");
}

TEST_F(CompilerTest, BatchInfra) {
  CodeGenTestCheckBatchDir(L"infra");
}

TEST_F(CompilerTest, BatchPasses) {
  CodeGenTestCheckBatchDir(L"passes");
}

TEST_F(CompilerTest, BatchShaderTargets) {
  CodeGenTestCheckBatchDir(L"shader_targets");
}

TEST_F(CompilerTest, BatchValidation) {
  CodeGenTestCheckBatchDir(L"validation");
}

TEST_F(CompilerTest, BatchSamples) {
  CodeGenTestCheckBatchDir(L"samples");
}

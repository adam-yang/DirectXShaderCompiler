///////////////////////////////////////////////////////////////////////////////
//                                                                           //
// FileCheckerTest.cpp                                                       //
// Copyright (C) Microsoft Corporation. All rights reserved.                 //
// This file is distributed under the University of Illinois Open Source     //
// License. See LICENSE.TXT for details.                                     //
//                                                                           //
// Provides tests that are based on FileChecker.                             //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////

#ifndef UNICODE
#define UNICODE
#endif

#include <memory>
#include <vector>
#include <string>
#include <cassert>
#include <algorithm>
#include "dxc/Support/WinIncludes.h"
#include "dxc/dxcapi.h"
#ifdef _WIN32
#include <atlfile.h>
#endif

#include "HLSLTestData.h"
#include "HlslTestUtils.h"
#include "DxcTestUtils.h"

#include "llvm/Support/raw_os_ostream.h"
#include "llvm/Support/MD5.h"
#include "dxc/Support/Global.h"
#include "dxc/Support/dxcapi.use.h"
#include "dxc/Support/HLSLOptions.h"
#include "dxc/Support/Unicode.h"
#include "dxc/DxilContainer/DxilContainer.h"
#include "D3DReflectionDumper.h"

#include "d3d12shader.h"

using namespace std;
using namespace hlsl_test;

static constexpr char whitespaceChars[] = " \t\r\n";

static std::string strltrim(const std::string &value) {
  size_t first = value.find_first_not_of(whitespaceChars);
  return first == string::npos ? value : value.substr(first);
}

static std::string strrtrim(const std::string &value) {
  size_t last = value.find_last_not_of(whitespaceChars);
  return last == string::npos ? value : value.substr(0, last + 1);
}

static std::string strtrim(const std::string &value) {
  return strltrim(strrtrim(value));
}

static bool strstartswith(const std::string& value, const char* pattern) {
  for (size_t i = 0; ; ++i) {
    if (pattern[i] == '\0') return true;
    if (i == value.size() || value[i] != pattern[i]) return false;
  }
}

static std::vector<std::string> strtok(const std::string &value, const char *delimiters = whitespaceChars) {
  size_t searchOffset = 0;
  std::vector<std::string> tokens;
  while (searchOffset != value.size()) {
    size_t tokenStartIndex = value.find_first_not_of(delimiters, searchOffset);
    if (tokenStartIndex == std::string::npos) break;
    size_t tokenEndIndex = value.find_first_of(delimiters, tokenStartIndex);
    if (tokenEndIndex == std::string::npos) tokenEndIndex = value.size();
    tokens.emplace_back(value.substr(tokenStartIndex, tokenEndIndex - tokenStartIndex));
    searchOffset = tokenEndIndex;
  }
  return tokens;
}

FileRunCommandPart::FileRunCommandPart(const std::string &command, const std::string &arguments, LPCWSTR commandFileName) :
  Command(command), Arguments(arguments), CommandFileName(commandFileName) { }

void FileRunCommandPart::RunHashTests(dxc::DxcDllSupport &DllSupport) {
  if (0 == _stricmp(Command.c_str(), "%dxc")) {
    RunDxcHashTest(DllSupport);
  }
  else {
    RunResult = 0;
  }
}

void FileRunCommandPart::Run(dxc::DxcDllSupport &DllSupport, const FileRunCommandPart *Prior) {
  bool isFileCheck =
    0 == _stricmp(Command.c_str(), "FileCheck") ||
    0 == _stricmp(Command.c_str(), "%FileCheck");
  bool isXFail = 0 == _stricmp(Command.c_str(), "xfail");

  // For now, propagate errors.
  if (Prior && Prior->RunResult && !isFileCheck && !isXFail) {
    StdErr = Prior->StdErr;
    RunResult = Prior->RunResult;
    return;
  }

  // We would add support for 'not' and 'llc' here.
  if (isFileCheck) {
    RunFileChecker(Prior);
  }
  else if (isXFail) {
    RunXFail(Prior);
  }
  else if (0 == _stricmp(Command.c_str(), "tee")) {
    RunTee(Prior);
  }
  else if (0 == _stricmp(Command.c_str(), "%dxc")) {
    RunDxc(DllSupport, Prior);
  }
  else if (0 == _stricmp(Command.c_str(), "%dxv")) {
    RunDxv(DllSupport, Prior);
  }
  else if (0 == _stricmp(Command.c_str(), "%opt")) {
    RunOpt(DllSupport, Prior);
  }
  else if (0 == _stricmp(Command.c_str(), "%D3DReflect")) {
    RunD3DReflect(DllSupport, Prior);
  }
  else {
    RunResult = 1;
    StdErr = "Unrecognized command ";
    StdErr += Command;
  }
}

void FileRunCommandPart::RunFileChecker(const FileRunCommandPart *Prior) {
  if (!Prior) {
    StdErr = "Prior command required to generate stdin";
    RunResult = 1;
    return;
  }

  FileCheckForTest t;
  t.CheckFilename = CW2A(CommandFileName, CP_UTF8);
  if (Prior->RunResult)
    t.InputForStdin = Prior->StdErr;
  else
    t.InputForStdin = Prior->StdOut;

  // Parse command arguments
  static constexpr char checkPrefixStr[] = "-check-prefix=";
  bool hasInputFilename = false;
  for (const std::string& arg : strtok(Arguments)) {
    if (arg == "%s") hasInputFilename = true;
    else if (arg == "-input=stderr") t.InputForStdin = Prior->StdErr;
    else if (strstartswith(arg, checkPrefixStr))
      t.CheckPrefixes.emplace_back(arg.substr(sizeof(checkPrefixStr) - 1));
    else {
      StdErr = "Invalid argument";
      RunResult = 1;
      return;
    }
  }
  if (!hasInputFilename) {
    StdErr = "Missing input filename";
    RunResult = 1;
    return;
  }

  // Run
  RunResult = t.Run();

  StdOut = t.test_outs;
  StdErr = t.test_errs;
  // Capture the input as well.
  if (RunResult != 0 && Prior != nullptr) {
    StdErr += "\n<full input to FileCheck>\n";
    StdErr += t.InputForStdin;
  }
}

void FileRunCommandPart::ReadOptsForDxc(hlsl::options::MainArgs &argStrings,
                                        hlsl::options::DxcOpts &Opts) {
  std::string args(strtrim(Arguments));
  const char *inputPos = strstr(args.c_str(), "%s");
  if (inputPos == nullptr) {
    StdErr = "Only supported pattern includes input file as argument";
    RunResult = 1;
    return;
  }
  args.erase(inputPos - args.c_str(), strlen("%s"));

  llvm::StringRef argsRef = args;
  llvm::SmallVector<llvm::StringRef, 8> splitArgs;
  argsRef.split(splitArgs, " ");
  argStrings = hlsl::options::MainArgs(splitArgs);
  std::string errorString;
  llvm::raw_string_ostream errorStream(errorString);
  RunResult = ReadDxcOpts(hlsl::options::getHlslOptTable(), /*flagsToInclude*/ 0,
                          argStrings, Opts, errorStream);
  errorStream.flush();
  if (RunResult) {
    StdErr = errorString;
  }
}

static HRESULT ReAssembleTo(dxc::DxcDllSupport &DllSupport, void *bitcode, UINT32 size, IDxcBlob **pBlob) {
  CComPtr<IDxcAssembler> pAssembler;
  CComPtr<IDxcLibrary> pLibrary;
  IFT(DllSupport.CreateInstance(CLSID_DxcLibrary, &pLibrary));
  IFT(DllSupport.CreateInstance(CLSID_DxcAssembler, &pAssembler));

  CComPtr<IDxcBlobEncoding> pInBlob;

  IFR(pLibrary->CreateBlobWithEncodingFromPinned(bitcode, size, 0, &pInBlob));
  
  CComPtr<IDxcOperationResult> pResult;
  pAssembler->AssembleToContainer(pInBlob, &pResult);

  HRESULT Result = 0;
  IFR(pResult->GetStatus(&Result));
  IFR(Result);

  IFR(pResult->GetResult(pBlob));

  return S_OK;
}

static HRESULT GetDxilBitcode(dxc::DxcDllSupport &DllSupport, IDxcBlob *pCompiledBlob, IDxcBlob **pBitcodeBlob) {
  CComPtr<IDxcContainerReflection> pReflection;
  CComPtr<IDxcLibrary> pLibrary;
  IFR(DllSupport.CreateInstance(CLSID_DxcContainerReflection, &pReflection));
  IFT(DllSupport.CreateInstance(CLSID_DxcLibrary, &pLibrary));

  IFR(pReflection->Load(pCompiledBlob));

  UINT32 uIndex = 0;
  IFR(pReflection->FindFirstPartKind(hlsl::DFCC_DXIL, &uIndex));
  CComPtr<IDxcBlob> pPart;
  IFR(pReflection->GetPartContent(uIndex, &pPart));

  auto header = (hlsl::DxilProgramHeader*)pPart->GetBufferPointer();
  void *bitcode = (char *)&header->BitcodeHeader + header->BitcodeHeader.BitcodeOffset;
  UINT32 bitcode_size = header->BitcodeHeader.BitcodeSize;

  CComPtr<IDxcBlobEncoding> pBlob;
  IFR(pLibrary->CreateBlobWithEncodingFromPinned(bitcode, bitcode_size, 0, &pBlob));
  *pBitcodeBlob = pBlob.Detach();

  return S_OK;
}

static HRESULT CompileForHash(hlsl::options::DxcOpts &opts, LPCWSTR CommandFileName, dxc::DxcDllSupport &DllSupport, std::vector<LPCWSTR> &flags, llvm::SmallString<32> &Hash, std::string &Disasm) {
  CComPtr<IDxcLibrary> pLibrary;
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;
  CComPtr<IDxcBlobEncoding> pDisassembly;
  CComPtr<IDxcBlob> pCompiledBlob;
  CComPtr<IDxcIncludeHandler> pIncludeHandler;


  std::wstring entry =
      Unicode::UTF8ToUTF16StringOrThrow(opts.EntryPoint.str().c_str());
  std::wstring profile =
      Unicode::UTF8ToUTF16StringOrThrow(opts.TargetProfile.str().c_str());

  IFT(DllSupport.CreateInstance(CLSID_DxcLibrary, &pLibrary));
  IFT(pLibrary->CreateBlobFromFile(CommandFileName, nullptr, &pSource));
  IFT(pLibrary->CreateIncludeHandler(&pIncludeHandler));
  IFT(DllSupport.CreateInstance(CLSID_DxcCompiler, &pCompiler));
  IFR(pCompiler->Compile(pSource, CommandFileName, entry.c_str(), profile.c_str(),
                          flags.data(), flags.size(), nullptr, 0, pIncludeHandler, &pResult));

  HRESULT resultStatus = 0;
  IFT(pResult->GetStatus(&resultStatus));
  if (SUCCEEDED(resultStatus)) {

    IFT(pResult->GetResult(&pCompiledBlob));

    CComPtr<IDxcContainerReflection> pReflection;
    IFT(DllSupport.CreateInstance(CLSID_DxcContainerReflection, &pReflection));

    // If failed to load here, it's likely some non-compile operation thing. Just fail the hash generation.
    if (FAILED(pReflection->Load(pCompiledBlob)))
      return E_FAIL;

    CComPtr<IDxcBlob> pBitcodeBlob;
    IFT(GetDxilBitcode(DllSupport, pCompiledBlob, &pBitcodeBlob));

    CComPtr<IDxcBlob> pReassembledBlob;
    IFT(ReAssembleTo(DllSupport, pBitcodeBlob->GetBufferPointer(), pBitcodeBlob->GetBufferSize(), &pReassembledBlob));

    CComPtr<IDxcBlobEncoding> pDisassembly;
    IFT(pCompiler->Disassemble(pReassembledBlob, &pDisassembly));
    Disasm = BlobToUtf8(pDisassembly);

    llvm::ArrayRef<uint8_t> Data((uint8_t *)Disasm.data(), Disasm.size());
    llvm::MD5 md5;
    llvm::MD5::MD5Result md5Result;
    md5.update(Data);
    md5.final(md5Result);
    md5.stringifyResult(md5Result, Hash);

    return 0;
  }
  else {
    CComPtr<IDxcBlobEncoding> pErrors;
    IFT(pResult->GetErrorBuffer(&pErrors));
    const char *errors = (char *)pErrors->GetBufferPointer();
    (void)errors;
    return resultStatus;
  }
}

void FileRunCommandPart::RunDxcHashTest(dxc::DxcDllSupport &DllSupport) {
  hlsl::options::MainArgs args;
  hlsl::options::DxcOpts opts;
  ReadOptsForDxc(args, opts);

  std::vector<std::wstring> argWStrings;
  CopyArgsToWStrings(opts.Args, hlsl::options::CoreOption, argWStrings);

  // Create the two versions of the flags
  std::vector<LPCWSTR> normal_flags;
  std::vector<LPCWSTR> dbg_flags;
  for (const std::wstring &a : argWStrings) {
    if (a.find(L"ast-dump") != std::wstring::npos) continue;
    if (a.find(L"Zi") == std::wstring::npos || a.find(L"Fd") == std::wstring::npos) {
      normal_flags.push_back(a.data());
    }
    dbg_flags.push_back(a.data());
  }
  dbg_flags.push_back(L"/Zi");

  // Add the flags to strip value names and unused GV's.
  //normal_flags.push_back(L"-Qstrip_reflect");
  //dbg_flags.push_back(L"-Qstrip_reflect");

  llvm::SmallString<32> Hash0;
  llvm::SmallString<32> Hash1;
  std::string Disasm0;
  std::string Disasm1;

  HRESULT normalStatus = CompileForHash(opts, CommandFileName, DllSupport, normal_flags, Hash0, Disasm0);
  // If the normal compilation fails, just skip this test. It's likely that this was meant to test for failures.
  if (FAILED(normalStatus)) {
    RunResult = 0;
    return;
  }

  HRESULT augmentedStatus = CompileForHash(opts, CommandFileName, DllSupport, dbg_flags, Hash1, Disasm1);
  if (FAILED(augmentedStatus)) {
    RunResult = -1;
    return;
  }

  if (Hash0 != Hash1) {
    StdErr = "Hash does not match!!!\n";
    StdErr += Disasm0;
    StdErr += Disasm1;
    RunResult = -1;
  }
  else {
    RunResult = 0;
  }
}

void FileRunCommandPart::RunDxc(dxc::DxcDllSupport &DllSupport, const FileRunCommandPart *Prior) {
  // Support piping stdin from prior if needed.
  UNREFERENCED_PARAMETER(Prior);
  hlsl::options::MainArgs args;
  hlsl::options::DxcOpts opts;
  ReadOptsForDxc(args, opts);

  std::wstring entry =
      Unicode::UTF8ToUTF16StringOrThrow(opts.EntryPoint.str().c_str());
  std::wstring profile =
      Unicode::UTF8ToUTF16StringOrThrow(opts.TargetProfile.str().c_str());
  std::vector<LPCWSTR> flags;
  if (opts.CodeGenHighLevel) {
    flags.push_back(L"-fcgl");
  }

  std::vector<std::wstring> argWStrings;
  CopyArgsToWStrings(opts.Args, hlsl::options::CoreOption, argWStrings);
  for (const std::wstring &a : argWStrings)
    flags.push_back(a.data());

  CComPtr<IDxcLibrary> pLibrary;
  CComPtr<IDxcCompiler> pCompiler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<IDxcBlobEncoding> pSource;
  CComPtr<IDxcBlobEncoding> pDisassembly;
  CComPtr<IDxcBlob> pCompiledBlob;
  CComPtr<IDxcIncludeHandler> pIncludeHandler;

  HRESULT resultStatus;

  if (RunResult)  // opt parsing already failed
    return;

  IFT(DllSupport.CreateInstance(CLSID_DxcLibrary, &pLibrary));
  IFT(pLibrary->CreateBlobFromFile(CommandFileName, nullptr, &pSource));
  IFT(pLibrary->CreateIncludeHandler(&pIncludeHandler));
  IFT(DllSupport.CreateInstance(CLSID_DxcCompiler, &pCompiler));
  IFT(pCompiler->Compile(pSource, CommandFileName, entry.c_str(), profile.c_str(),
                          flags.data(), flags.size(), nullptr, 0, pIncludeHandler, &pResult));
  IFT(pResult->GetStatus(&resultStatus));
  if (SUCCEEDED(resultStatus)) {
    IFT(pResult->GetResult(&pCompiledBlob));
    if (!opts.AstDump) {
      IFT(pCompiler->Disassemble(pCompiledBlob, &pDisassembly));
      StdOut = BlobToUtf8(pDisassembly);
    } else {
      StdOut = BlobToUtf8(pCompiledBlob);
    }
    CComPtr<IDxcBlobEncoding> pStdErr;
    IFT(pResult->GetErrorBuffer(&pStdErr));
    StdErr = BlobToUtf8(pStdErr);
    RunResult = 0;
  }
  else {
    IFT(pResult->GetErrorBuffer(&pDisassembly));
    StdErr = BlobToUtf8(pDisassembly);
    RunResult = resultStatus;
  }

  OpResult = pResult;
}

void FileRunCommandPart::RunDxv(dxc::DxcDllSupport &DllSupport, const FileRunCommandPart *Prior) {
  std::string args(strtrim(Arguments));
  const char *inputPos = strstr(args.c_str(), "%s");
  if (inputPos == nullptr) {
    StdErr = "Only supported pattern includes input file as argument";
    RunResult = 1;
    return;
  }
  args.erase(inputPos - args.c_str(), strlen("%s"));

  llvm::StringRef argsRef = args;
  llvm::SmallVector<llvm::StringRef, 8> splitArgs;
  argsRef.split(splitArgs, " ");
  IFTMSG(splitArgs.size()==1, "wrong arg num for dxv");
      
  CComPtr<IDxcLibrary> pLibrary;
  CComPtr<IDxcAssembler> pAssembler;
  CComPtr<IDxcValidator> pValidator;
  CComPtr<IDxcOperationResult> pResult;

  CComPtr<IDxcBlobEncoding> pSource;

  CComPtr<IDxcBlob> pContainerBlob;
  HRESULT resultStatus;

  IFT(DllSupport.CreateInstance(CLSID_DxcLibrary, &pLibrary));
  IFT(pLibrary->CreateBlobFromFile(CommandFileName, nullptr, &pSource));
  IFT(DllSupport.CreateInstance(CLSID_DxcAssembler, &pAssembler));
  IFT(pAssembler->AssembleToContainer(pSource, &pResult));
  IFT(pResult->GetStatus(&resultStatus));
  if (FAILED(resultStatus)) {
    CComPtr<IDxcBlobEncoding> pAssembleBlob;
    IFT(pResult->GetErrorBuffer(&pAssembleBlob));
    StdErr = BlobToUtf8(pAssembleBlob);
    RunResult = resultStatus;
    return;
  }
  IFT(pResult->GetResult(&pContainerBlob));

  IFT(DllSupport.CreateInstance(CLSID_DxcValidator, &pValidator));
  CComPtr<IDxcOperationResult> pValidationResult;
  IFT(pValidator->Validate(pContainerBlob, DxcValidatorFlags_InPlaceEdit,
                            &pValidationResult));
  IFT(pValidationResult->GetStatus(&resultStatus));
  if (resultStatus) {
    CComPtr<IDxcBlobEncoding> pValidateBlob;
    IFT(pValidationResult->GetErrorBuffer(&pValidateBlob));
    StdOut = BlobToUtf8(pValidateBlob);
  }
  RunResult = 0;
}

void FileRunCommandPart::RunOpt(dxc::DxcDllSupport &DllSupport, const FileRunCommandPart *Prior) {
  std::string args(strtrim(Arguments));
  const char *inputPos = strstr(args.c_str(), "%s");
  if (inputPos == nullptr && Prior == nullptr) {
    StdErr = "Only supported patterns are input file as argument or prior "
              "command with disassembly";
    RunResult = 1;
    return;
  }

  CComPtr<IDxcLibrary> pLibrary;
  CComPtr<IDxcOptimizer> pOptimizer;
  CComPtr<IDxcBlobEncoding> pSource;
  CComPtr<IDxcBlobEncoding> pOutputText;
  CComPtr<IDxcBlob> pOutputModule;

  IFT(DllSupport.CreateInstance(CLSID_DxcLibrary, &pLibrary));
  IFT(DllSupport.CreateInstance(CLSID_DxcOptimizer, &pOptimizer));

  if (inputPos != nullptr) {
    args.erase(inputPos - args.c_str(), strlen("%s"));
    IFT(pLibrary->CreateBlobFromFile(CommandFileName, nullptr, &pSource));
  }
  else {
    assert(Prior != nullptr && "else early check should have returned");
    CComPtr<IDxcAssembler> pAssembler;
    IFT(DllSupport.CreateInstance(CLSID_DxcAssembler, &pAssembler));
    IFT(pLibrary->CreateBlobWithEncodingFromPinned(
        Prior->StdOut.c_str(), Prior->StdOut.size(), CP_UTF8,
        &pSource));
  }

  args = strtrim(args);
  llvm::StringRef argsRef = args;
  llvm::SmallVector<llvm::StringRef, 8> splitArgs;
  argsRef.split(splitArgs, " ");
  std::vector<LPCWSTR> options;
  std::vector<std::wstring> optionStrings;
  for (llvm::StringRef S : splitArgs) {
    optionStrings.push_back(
        Unicode::UTF8ToUTF16StringOrThrow(strtrim(S.str()).c_str()));
  }

  // Add the options outside the above loop in case the vector is resized.
  for (const std::wstring& str : optionStrings)
    options.push_back(str.c_str());

  IFT(pOptimizer->RunOptimizer(pSource, options.data(), options.size(),
                                &pOutputModule, &pOutputText));
  StdOut = BlobToUtf8(pOutputText);
  RunResult = 0;
}

void FileRunCommandPart::RunD3DReflect(dxc::DxcDllSupport &DllSupport, const FileRunCommandPart *Prior) {
  std::string args(strtrim(Arguments));
  if (args != "%s") {
    StdErr = "Only supported pattern is a plain input file";
    RunResult = 1;
    return;
  }
  if (!Prior) {
    StdErr = "Prior command required to generate stdin";
    RunResult = 1;
    return;
  }

  CComPtr<IDxcLibrary> pLibrary;
  CComPtr<IDxcBlobEncoding> pSource;
  CComPtr<IDxcAssembler> pAssembler;
  CComPtr<IDxcOperationResult> pResult;
  CComPtr<ID3D12ShaderReflection> pShaderReflection;
  CComPtr<ID3D12LibraryReflection> pLibraryReflection;
  CComPtr<IDxcContainerReflection> containerReflection;
  uint32_t partCount;
  CComPtr<IDxcBlob> pContainerBlob;
  HRESULT resultStatus;
  bool blobFound = false;
  std::ostringstream ss;
  D3DReflectionDumper dumper(ss);

  IFT(DllSupport.CreateInstance(CLSID_DxcLibrary, &pLibrary));
  IFT(DllSupport.CreateInstance(CLSID_DxcAssembler, &pAssembler));

  IFT(pLibrary->CreateBlobWithEncodingFromPinned(
      (LPBYTE)Prior->StdOut.c_str(), Prior->StdOut.size(), CP_UTF8,
      &pSource));

  IFT(pAssembler->AssembleToContainer(pSource, &pResult));
  IFT(pResult->GetStatus(&resultStatus));
  if (FAILED(resultStatus)) {
    CComPtr<IDxcBlobEncoding> pAssembleBlob;
    IFT(pResult->GetErrorBuffer(&pAssembleBlob));
    StdErr = BlobToUtf8(pAssembleBlob);
    RunResult = resultStatus;
    return;
  }
  IFT(pResult->GetResult(&pContainerBlob));

  VERIFY_SUCCEEDED(DllSupport.CreateInstance(CLSID_DxcContainerReflection, &containerReflection));
  VERIFY_SUCCEEDED(containerReflection->Load(pContainerBlob));
  VERIFY_SUCCEEDED(containerReflection->GetPartCount(&partCount));

  for (uint32_t i = 0; i < partCount; ++i) {
    uint32_t kind;
    VERIFY_SUCCEEDED(containerReflection->GetPartKind(i, &kind));
    if (kind == (uint32_t)hlsl::DxilFourCC::DFCC_DXIL) {
      blobFound = true;
      CComPtr<IDxcBlob> pPart;
      IFT(containerReflection->GetPartContent(i, &pPart));
      const hlsl::DxilProgramHeader *pProgramHeader =
        reinterpret_cast<const hlsl::DxilProgramHeader*>(pPart->GetBufferPointer());
      VERIFY_IS_TRUE(IsValidDxilProgramHeader(pProgramHeader, (uint32_t)pPart->GetBufferSize()));
      hlsl::DXIL::ShaderKind SK = hlsl::GetVersionShaderType(pProgramHeader->ProgramVersion);
      if (SK == hlsl::DXIL::ShaderKind::Library)
        VERIFY_SUCCEEDED(containerReflection->GetPartReflection(i, IID_PPV_ARGS(&pLibraryReflection)));
      else
        VERIFY_SUCCEEDED(containerReflection->GetPartReflection(i, IID_PPV_ARGS(&pShaderReflection)));
      break;
    }
  }

  if (!blobFound) {
    StdErr = "Unable to find DXIL part";
    RunResult = 1;
    return;
  } else if (pShaderReflection) {
    dumper.Dump(pShaderReflection);
  } else if (pLibraryReflection) {
    dumper.Dump(pLibraryReflection);
  }

  ss.flush();
  StdOut = ss.str();
  RunResult = 0;
}

void FileRunCommandPart::RunTee(const FileRunCommandPart *Prior) {
  if (Prior == nullptr) {
    StdErr = "tee requires a prior command";
    RunResult = 1;
    return;
  }

  // Ignore commands for now - simply log out through test framework.
  {
    CA2W outWide(Prior->StdOut.c_str(), CP_UTF8);
    WEX::Logging::Log::Comment(outWide.m_psz);
  }
  if (!Prior->StdErr.empty()) {
    CA2W errWide(Prior->StdErr.c_str(), CP_UTF8);
    WEX::Logging::Log::Comment(L"<stderr>");
    WEX::Logging::Log::Comment(errWide.m_psz);
  }

  StdErr = Prior->StdErr;
  StdOut = Prior->StdOut;
  RunResult = Prior->RunResult;
}

void FileRunCommandPart::RunXFail(const FileRunCommandPart *Prior) {
  if (Prior == nullptr) {
    StdErr = "XFail requires a prior command";
    RunResult = 1;
    return;
  }

  if (Prior->RunResult == 0) {
    StdErr = "XFail expected a failure from previous command";
    RunResult = 1;
  } else {
    RunResult = 0;
  }
}

class FileRunTestResultImpl : public FileRunTestResult {
  dxc::DxcDllSupport &m_support;

  void RunHashTestFromCommands(LPCSTR commands, LPCWSTR fileName) {
    std::vector<FileRunCommandPart> parts;
    ParseCommandParts(commands, fileName, parts);
    FileRunCommandPart *prior = nullptr;
    for (FileRunCommandPart & part : parts) {
      part.RunHashTests(m_support);
      prior = &part;
      break;
    }
    if (prior != nullptr) {
      this->RunResult = prior->RunResult;
      this->ErrorMessage = prior->StdErr;
    }
    else {
      this->RunResult = 0;
    }
  }

  void RunFileCheckFromCommands(LPCSTR commands, LPCWSTR fileName) {
    std::vector<FileRunCommandPart> parts;
    ParseCommandParts(commands, fileName, parts);
    FileRunCommandPart *prior = nullptr;
    for (FileRunCommandPart & part : parts) {
      part.Run(m_support, prior);
      prior = &part;
    }
    if (prior == nullptr) {
      this->RunResult = 1;
      this->ErrorMessage = "FileCheck found no commands to run";
    }
    else {
      this->RunResult = prior->RunResult;
      this->ErrorMessage = prior->StdErr;
    }
  }

public:
  FileRunTestResultImpl(dxc::DxcDllSupport &support) : m_support(support) {}
  void RunFileCheckFromFileCommands(LPCWSTR fileName) {
    // Assume UTF-8 files.
    std::string commands(GetFirstLine(fileName));
    return RunFileCheckFromCommands(commands.c_str(), fileName);
  }

  void RunHashTestFromFileCommands(LPCWSTR fileName) {
    // Assume UTF-8 files.
    std::string commands(GetFirstLine(fileName));
    return RunHashTestFromCommands(commands.c_str(), fileName);
  }
};

FileRunTestResult FileRunTestResult::RunHashTestFromFileCommands(LPCWSTR fileName) {
  dxc::DxcDllSupport dllSupport;
  IFT(dllSupport.Initialize());
  FileRunTestResultImpl result(dllSupport);
  result.RunHashTestFromFileCommands(fileName);
  return result;
}

FileRunTestResult FileRunTestResult::RunFromFileCommands(LPCWSTR fileName) {
  dxc::DxcDllSupport dllSupport;
  IFT(dllSupport.Initialize());
  FileRunTestResultImpl result(dllSupport);
  result.RunFileCheckFromFileCommands(fileName);
  return result;
}

FileRunTestResult FileRunTestResult::RunFromFileCommands(LPCWSTR fileName, dxc::DxcDllSupport &dllSupport) {
  FileRunTestResultImpl result(dllSupport);
  result.RunFileCheckFromFileCommands(fileName);
  return result;
}

void ParseCommandParts(LPCSTR commands, LPCWSTR fileName,
                       std::vector<FileRunCommandPart> &parts) {
  // Barely enough parsing here.
  commands = strstr(commands, "RUN: ");
  if (!commands) {
    return;
  }
  commands += strlen("RUN: ");

  LPCSTR endCommands = strchr(commands, '\0');
  while (commands != endCommands) {
    LPCSTR nextStart;
    LPCSTR thisEnd = strchr(commands, '|');
    if (!thisEnd) {
      nextStart = thisEnd = endCommands;
    } else {
      nextStart = thisEnd + 2;
    }
    LPCSTR commandEnd = strchr(commands, ' ');
    if (!commandEnd)
      commandEnd = endCommands;
    parts.emplace_back(std::string(commands, commandEnd),
                       std::string(commandEnd, thisEnd), fileName);
    commands = nextStart;
  }
}

void ParseCommandPartsFromFile(LPCWSTR fileName,
                               std::vector<FileRunCommandPart> &parts) {
  // Assume UTF-8 files.
  std::string commands(GetFirstLine(fileName));
  ParseCommandParts(commands.c_str(), fileName, parts);
}

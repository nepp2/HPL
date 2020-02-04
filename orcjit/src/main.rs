
use llvm_sys::target_machine::{
  LLVMTargetRef, LLVMTargetMachineRef, LLVMCreateTargetMachine,
  LLVMGetFirstTarget, LLVMGetDefaultTargetTriple,
};
use llvm_sys::target::LLVMTargetDataRef;
use llvm_sys::orc::{LLVMOrcJITStackRef, LLVMOrcModuleHandle};

struct Jit {
  target_machine : LLVMTargetMachineRef,
  data_layout : LLVMTargetDataRef,
  jit_stack : LLVMOrcJITStackRef,
  module_handle : LLVMOrcModuleHandle,
}

impl Jit {
  fn new() -> Jit {
    let target = LLVMGetFirstTarget();
    let triple = LLVMGetDefaultTargetTriple();
    LLVMCreateTargetMachine(target, triple);
    TM(llvm::EngineBuilder().selectTarget()), DL(TM->createDataLayout());
    ObjectLayer([]() { return std::make_shared<llvm::SectionMemoryManager>(); });
    CompileLayer(ObjectLayer, llvm::orc::SimpleCompiler(*TM));
    llvm::sys::DynamicLibrary::LoadLibraryPermanently(nullptr);
  }
}

// class KaleidoscopeJIT {
//   private:
//     std::unique_ptr<llvm::TargetMachine> TM;
//     const llvm::DataLayout DL;
//     llvm::orc::RTDyldObjectLinkingLayer ObjectLayer;
//     llvm::orc::IRCompileLayer<decltype(ObjectLayer), llvm::orc::SimpleCompiler> CompileLayer;
  
//   public:
//     using ModuleHandle = decltype(CompileLayer)::ModuleHandleT;
  
//     KaleidoscopeJIT()
//         : TM(llvm::EngineBuilder().selectTarget()), DL(TM->createDataLayout()),
//           ObjectLayer([]() { return std::make_shared<llvm::SectionMemoryManager>(); }),
//           CompileLayer(ObjectLayer, llvm::orc::SimpleCompiler(*TM)) {
//       llvm::sys::DynamicLibrary::LoadLibraryPermanently(nullptr);
//     }
  
//     llvm::TargetMachine& getTargetMachine() { return *TM; }
  
//     ModuleHandle addModule(std::unique_ptr<llvm::Module> M) {
//       // Build our symbol resolver:
//       // Lambda 1: Look back into the JIT itself to find symbols that are part of
//       //           the same "logical dylib".
//       // Lambda 2: Search for external symbols in the host process.
//       auto Resolver = llvm::orc::createLambdaResolver(
//           [&](const std::string &Name) {
//             if (auto Sym = CompileLayer.findSymbol(Name, false))
//               return Sym;
//             return llvm::JITSymbol(nullptr);
//           },
//           [](const std::string &Name) {
//             if (auto SymAddr =       llvm::RTDyldMemoryManager::getSymbolAddressInProcess(Name))
//               return llvm::JITSymbol(SymAddr, llvm::JITSymbolFlags::Exported);
//             return llvm::JITSymbol(nullptr);
//           });
  
//       // Add the set to the JIT with the resolver we created above and a newly
//       // created SectionMemoryManager.
//       return cantFail(CompileLayer.addModule(std::move(M),
//                                              std::move(Resolver)));
//     }
  
//     llvm::JITSymbol findSymbol(const std::string Name) {
//       std::string MangledName;
//       llvm::raw_string_ostream MangledNameStream(MangledName);
//       llvm::Mangler::getNameWithPrefix(MangledNameStream, Name, DL);
//       return CompileLayer.findSymbol(MangledNameStream.str(), true);
//     }
  
//     llvm::JITTargetAddress getSymbolAddress(const std::string Name) {
//       return cantFail(findSymbol(Name).getAddress());
//     }
  
//     void removeModule(ModuleHandle H) {
//       cantFail(CompileLayer.removeModule(H));
//     }
//   };
  
//   static llvm::LLVMContext TheContext;
//   static llvm::IRBuilder<> Builder(TheContext);
//   static std::unique_ptr<llvm::Module> TheModule;
//   static std::map<std::string, llvm::Value*> NamedValues;
//   static std::unique_ptr<llvm::legacy::FunctionPassManager> TheFPM;
//   static std::unique_ptr<KaleidoscopeJIT> TheJIT;
  
//   int main() {
//     llvm::InitializeNativeTarget();
//     llvm::InitializeNativeTargetAsmPrinter();
//     llvm::InitializeNativeTargetAsmParser();
  
//     TheJIT = llvm::make_unique<KaleidoscopeJIT>();
  
//     // Open a new module.
//     TheModule = llvm::make_unique<llvm::Module>("my_jit", TheContext);
//     TheModule->setDataLayout(TheJIT->getTargetMachine().createDataLayout());
  
//     // Create a new pass manager attached to it.
//     TheFPM = llvm::make_unique<llvm::legacy::FunctionPassManager>(TheModule.get());
//     // Do simple "peephole" optimizations and bit-twiddling optzns.
//     TheFPM->add(llvm::createInstructionCombiningPass());
//     // Reassociate expressions.
//     TheFPM->add(llvm::createReassociatePass());
//     // Eliminate Common SubExpressions.
//     TheFPM->add(llvm::createGVNPass());
//     // Simplify the control flow graph (deleting unreachable blocks, etc).
//     TheFPM->add(llvm::createCFGSimplificationPass());
//     TheFPM->doInitialization();
  
//     // Make the function type:  double(double,double) etc.
//     std::vector<llvm::Type*> Doubles(0, llvm::Type::getDoubleTy(TheContext));
//     llvm::FunctionType* FT = llvm::FunctionType::get(llvm::Type::getDoubleTy(TheContext), Doubles, false);
  
//     // Create the function
//     llvm::Function* TheFunction = llvm::Function::Create(FT, llvm::Function::ExternalLinkage, "fun", TheModule.get());
  
//     // Create a new basic block to start insertion into.
//     llvm::BasicBlock* BB = llvm::BasicBlock::Create(TheContext, "entry", TheFunction);
//     Builder.SetInsertPoint(BB);
  
//     // Create two constants
//     auto a = llvm::ConstantFP::get(TheContext, llvm::APFloat(12.0));
//     auto b = llvm::ConstantFP::get(TheContext, llvm::APFloat(5.0));
    
//     // Create the addition of the two constants
//     auto RetVal = Builder.CreateFAdd(a, b, "addtmp");
  
//     // Finish off the function.
//     Builder.CreateRet(RetVal);
  
//     // Validate the generated code, checking for consistency.
//     verifyFunction(*TheFunction);
  
//     // Run the optimizer on the function.
//     TheFPM->run(*TheFunction);
  
//     // JIT the module containing the anonymous expression, keeping a handle so we can free it later.
//     auto H = TheJIT->addModule(std::move(TheModule));
  
//     // Search the JIT for the "fun" symbol.
//     auto ExprSymbol = TheJIT->findSymbol("fun");
//     assert(ExprSymbol && "Function not found");
  
//     // Get the symbol's address and cast it to the right type (takes no
//     // arguments, returns a double) so we can call it as a native function.
//     double (*FP)() = (double (*)())(intptr_t) cantFail(ExprSymbol.getAddress());
//     std::cout << FP() << std::endl;
  
//     // Delete the anonymous expression module from the JIT.
//     TheJIT->removeModule(H);
  
//     return 0;
//   }

fn main(){
  println!("Hello orcjit");
}

#[no_mangle]
static TEST_GLOBAL : i64 = 47;

extern {
  pub fn malloc(size: usize) -> *mut u8;
  pub fn free(ptr: *mut u8);
  pub fn memcpy(dest : *mut u8, src: *const u8, count : usize) -> *mut u8;
}

/// defined for the test suite only
#[no_mangle]
pub extern "C" fn test_add(a : i64, b : i64) -> i64 {
  a + b
}

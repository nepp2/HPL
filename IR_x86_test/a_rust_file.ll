; ModuleID = 'a_rust_file.3a1fbbbh-cgu.0'
source_filename = "a_rust_file.3a1fbbbh-cgu.0"
target datalayout = "e-m:w-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-windows-msvc"

%"core::fmt::Arguments" = type { [0 x i64], { [0 x { [0 x i8]*, i64 }]*, i64 }, [0 x i64], { i64*, i64 }, [0 x i64], { [0 x { i8*, i8* }]*, i64 }, [0 x i64] }

@0 = private unnamed_addr constant <{ [12 x i8] }> <{ [12 x i8] c"Hello world\0A" }>, align 1
@1 = private unnamed_addr constant <{ i8*, [8 x i8] }> <{ i8* getelementptr inbounds (<{ [12 x i8] }>, <{ [12 x i8] }>* @0, i32 0, i32 0, i32 0), [8 x i8] c"\0C\00\00\00\00\00\00\00" }>, align 8
@2 = private unnamed_addr constant <{ [0 x i8] }> zeroinitializer, align 8

; core::fmt::Arguments::new_v1
; Function Attrs: inlinehint uwtable
define internal void @_ZN4core3fmt9Arguments6new_v117hc766c224a8f6dba9E(%"core::fmt::Arguments"* noalias nocapture sret dereferenceable(48), [0 x { [0 x i8]*, i64 }]* noalias nonnull readonly align 8 %pieces.0, i64 %pieces.1, [0 x { i8*, i8* }]* noalias nonnull readonly align 8 %args.0, i64 %args.1) unnamed_addr #0 {
start:
  %_4 = alloca { i64*, i64 }, align 8
  %1 = bitcast { i64*, i64 }* %_4 to {}**
  store {}* null, {}** %1, align 8
  %2 = bitcast %"core::fmt::Arguments"* %0 to { [0 x { [0 x i8]*, i64 }]*, i64 }*
  %3 = getelementptr inbounds { [0 x { [0 x i8]*, i64 }]*, i64 }, { [0 x { [0 x i8]*, i64 }]*, i64 }* %2, i32 0, i32 0
  store [0 x { [0 x i8]*, i64 }]* %pieces.0, [0 x { [0 x i8]*, i64 }]** %3, align 8
  %4 = getelementptr inbounds { [0 x { [0 x i8]*, i64 }]*, i64 }, { [0 x { [0 x i8]*, i64 }]*, i64 }* %2, i32 0, i32 1
  store i64 %pieces.1, i64* %4, align 8
  %5 = getelementptr inbounds %"core::fmt::Arguments", %"core::fmt::Arguments"* %0, i32 0, i32 3
  %6 = getelementptr inbounds { i64*, i64 }, { i64*, i64 }* %_4, i32 0, i32 0
  %7 = load i64*, i64** %6, align 8
  %8 = getelementptr inbounds { i64*, i64 }, { i64*, i64 }* %_4, i32 0, i32 1
  %9 = load i64, i64* %8, align 8
  %10 = getelementptr inbounds { i64*, i64 }, { i64*, i64 }* %5, i32 0, i32 0
  store i64* %7, i64** %10, align 8
  %11 = getelementptr inbounds { i64*, i64 }, { i64*, i64 }* %5, i32 0, i32 1
  store i64 %9, i64* %11, align 8
  %12 = getelementptr inbounds %"core::fmt::Arguments", %"core::fmt::Arguments"* %0, i32 0, i32 5
  %13 = getelementptr inbounds { [0 x { i8*, i8* }]*, i64 }, { [0 x { i8*, i8* }]*, i64 }* %12, i32 0, i32 0
  store [0 x { i8*, i8* }]* %args.0, [0 x { i8*, i8* }]** %13, align 8
  %14 = getelementptr inbounds { [0 x { i8*, i8* }]*, i64 }, { [0 x { i8*, i8* }]*, i64 }* %12, i32 0, i32 1
  store i64 %args.1, i64* %14, align 8
  ret void
}

; a_rust_file::hello_world
; Function Attrs: nounwind uwtable
define void @_ZN11a_rust_file11hello_world17h6fa817792e8f77ffE() unnamed_addr #1 {
start:
  %_2 = alloca %"core::fmt::Arguments", align 8
; call core::fmt::Arguments::new_v1
  call void @_ZN4core3fmt9Arguments6new_v117hc766c224a8f6dba9E(%"core::fmt::Arguments"* noalias nocapture sret dereferenceable(48) %_2, [0 x { [0 x i8]*, i64 }]* noalias nonnull readonly align 8 bitcast (<{ i8*, [8 x i8] }>* @1 to [0 x { [0 x i8]*, i64 }]*), i64 1, [0 x { i8*, i8* }]* noalias nonnull readonly align 8 bitcast (<{ [0 x i8] }>* @2 to [0 x { i8*, i8* }]*), i64 0)
  br label %bb1

bb1:                                              ; preds = %start
; call std::io::stdio::_print
  call void @_ZN3std2io5stdio6_print17haefb24384b3cad8cE(%"core::fmt::Arguments"* noalias nocapture dereferenceable(48) %_2)
  br label %bb2

bb2:                                              ; preds = %bb1
  ret void
}

; a_rust_file::hello_world2
; Function Attrs: nounwind uwtable
define void @_ZN11a_rust_file12hello_world217h26fdc9692a5f7bb9E() unnamed_addr #1 {
start:
  %_2 = alloca %"core::fmt::Arguments", align 8
; call core::fmt::Arguments::new_v1
  call void @_ZN4core3fmt9Arguments6new_v117hc766c224a8f6dba9E(%"core::fmt::Arguments"* noalias nocapture sret dereferenceable(48) %_2, [0 x { [0 x i8]*, i64 }]* noalias nonnull readonly align 8 bitcast (<{ i8*, [8 x i8] }>* @1 to [0 x { [0 x i8]*, i64 }]*), i64 1, [0 x { i8*, i8* }]* noalias nonnull readonly align 8 bitcast (<{ [0 x i8] }>* @2 to [0 x { i8*, i8* }]*), i64 0)
  br label %bb1

bb1:                                              ; preds = %start
; call std::io::stdio::_print
  call void @_ZN3std2io5stdio6_print17haefb24384b3cad8cE(%"core::fmt::Arguments"* noalias nocapture dereferenceable(48) %_2)
  br label %bb2

bb2:                                              ; preds = %bb1
; call a_rust_file::hello_world
  call void @_ZN11a_rust_file11hello_world17h6fa817792e8f77ffE()
  br label %bb3

bb3:                                              ; preds = %bb2
  ret void
}

; std::io::stdio::_print
; Function Attrs: uwtable
declare void @_ZN3std2io5stdio6_print17haefb24384b3cad8cE(%"core::fmt::Arguments"* noalias nocapture dereferenceable(48)) unnamed_addr #2

attributes #0 = { inlinehint uwtable "target-cpu"="x86-64" }
attributes #1 = { nounwind uwtable "target-cpu"="x86-64" }
attributes #2 = { uwtable "target-cpu"="x86-64" }

; ModuleID = 'a_rust_file.3a1fbbbh-cgu.0'
source_filename = "a_rust_file.3a1fbbbh-cgu.0"
target datalayout = "e-m:w-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-windows-msvc"

%"core::fmt::Formatter" = type { [0 x i64], { i64, i64 }, [0 x i64], { i64, i64 }, [0 x i64], { {}*, [3 x i64]* }, [0 x i64], { i64*, i64* }, [0 x i64], { [0 x { i8*, i8* }]*, i64 }, [0 x i32], i32, [0 x i32], i32, [0 x i8], i8, [7 x i8] }
%"core::fmt::Void" = type { [0 x i8], {}, [0 x i8], %"core::marker::PhantomData<*mut core::ops::function::Fn<(), Output=()>>", [0 x i8] }
%"core::marker::PhantomData<*mut core::ops::function::Fn<(), Output=()>>" = type {}
%"core::str::Utf8Error" = type { [0 x i64], i64, [0 x i8], { i8, i8 }, [6 x i8] }
%"core::fmt::Arguments" = type { [0 x i64], { [0 x { [0 x i8]*, i64 }]*, i64 }, [0 x i64], { i64*, i64 }, [0 x i64], { [0 x { i8*, i8* }]*, i64 }, [0 x i64] }
%"core::slice::Repr<u8>" = type { [2 x i64] }
%"core::result::Result<&str, core::str::Utf8Error>" = type { [0 x i64], i64, [2 x i64] }
%"core::result::Result<&str, core::str::Utf8Error>::Ok" = type { [1 x i64], { [0 x i8]*, i64 }, [0 x i64] }
%"core::result::Result<&str, core::str::Utf8Error>::Err" = type { [1 x i64], %"core::str::Utf8Error", [0 x i64] }

@0 = private unnamed_addr constant <{ [0 x i8] }> zeroinitializer, align 1
@1 = private unnamed_addr constant <{ [2 x i8] }> <{ [2 x i8] c": " }>, align 1
@2 = private unnamed_addr constant <{ i8*, [8 x i8], i8*, [8 x i8] }> <{ i8* getelementptr inbounds (<{ [0 x i8] }>, <{ [0 x i8] }>* @0, i32 0, i32 0, i32 0), [8 x i8] zeroinitializer, i8* getelementptr inbounds (<{ [2 x i8] }>, <{ [2 x i8] }>* @1, i32 0, i32 0, i32 0), [8 x i8] c"\02\00\00\00\00\00\00\00" }>, align 8
@3 = private unnamed_addr constant <{ [21 x i8] }> <{ [21 x i8] c"src\5Clibcore\5Cresult.rs" }>, align 1
@4 = private unnamed_addr constant <{ i8*, [16 x i8] }> <{ i8* getelementptr inbounds (<{ [21 x i8] }>, <{ [21 x i8] }>* @3, i32 0, i32 0, i32 0), [16 x i8] c"\15\00\00\00\00\00\00\00\E5\03\00\00\05\00\00\00" }>, align 8
@5 = private unnamed_addr constant <{ [27 x i8] }> <{ [27 x i8] c"wasn't a valid utf8 string!" }>, align 1
@6 = private unnamed_addr constant <{ [1 x i8] }> <{ [1 x i8] c"\0A" }>, align 1
@7 = private unnamed_addr constant <{ i8*, [8 x i8], i8*, [8 x i8] }> <{ i8* getelementptr inbounds (<{ [0 x i8] }>, <{ [0 x i8] }>* @0, i32 0, i32 0, i32 0), [8 x i8] zeroinitializer, i8* getelementptr inbounds (<{ [1 x i8] }>, <{ [1 x i8] }>* @6, i32 0, i32 0, i32 0), [8 x i8] c"\01\00\00\00\00\00\00\00" }>, align 8

; <&T as core::fmt::Display>::fmt
; Function Attrs: uwtable
define zeroext i1 @"_ZN44_$LT$$RF$T$u20$as$u20$core..fmt..Display$GT$3fmt17h53cb8273fc649950E"({ [0 x i8]*, i64 }* noalias readonly align 8 dereferenceable(16) %self, %"core::fmt::Formatter"* align 8 dereferenceable(96) %f) unnamed_addr #0 {
start:
  %0 = getelementptr inbounds { [0 x i8]*, i64 }, { [0 x i8]*, i64 }* %self, i32 0, i32 0
  %1 = load [0 x i8]*, [0 x i8]** %0, align 8, !nonnull !0
  %2 = getelementptr inbounds { [0 x i8]*, i64 }, { [0 x i8]*, i64 }* %self, i32 0, i32 1
  %3 = load i64, i64* %2, align 8
; call <str as core::fmt::Display>::fmt
  %4 = call zeroext i1 @"_ZN42_$LT$str$u20$as$u20$core..fmt..Display$GT$3fmt17h1abc233d12afc37fE"([0 x i8]* noalias nonnull readonly align 1 %1, i64 %3, %"core::fmt::Formatter"* align 8 dereferenceable(96) %f)
  br label %bb1

bb1:                                              ; preds = %start
  ret i1 %4
}

; core::fmt::ArgumentV1::new
; Function Attrs: uwtable
define { i8*, i8* } @_ZN4core3fmt10ArgumentV13new17h5f8e96903532d478E({ [0 x i8]*, i64 }* noalias readonly align 8 dereferenceable(16) %x, i1 ({ [0 x i8]*, i64 }*, %"core::fmt::Formatter"*)* nonnull %f) unnamed_addr #0 {
start:
  %transmute_temp1 = alloca %"core::fmt::Void"*, align 8
  %transmute_temp = alloca i1 (%"core::fmt::Void"*, %"core::fmt::Formatter"*)*, align 8
  %_0 = alloca { i8*, i8* }, align 8
  %0 = bitcast i1 (%"core::fmt::Void"*, %"core::fmt::Formatter"*)** %transmute_temp to i1 ({ [0 x i8]*, i64 }*, %"core::fmt::Formatter"*)**
  store i1 ({ [0 x i8]*, i64 }*, %"core::fmt::Formatter"*)* %f, i1 ({ [0 x i8]*, i64 }*, %"core::fmt::Formatter"*)** %0, align 8
  %1 = load i1 (%"core::fmt::Void"*, %"core::fmt::Formatter"*)*, i1 (%"core::fmt::Void"*, %"core::fmt::Formatter"*)** %transmute_temp, align 8, !nonnull !0
  br label %bb1

bb1:                                              ; preds = %start
  %2 = bitcast %"core::fmt::Void"** %transmute_temp1 to { [0 x i8]*, i64 }**
  store { [0 x i8]*, i64 }* %x, { [0 x i8]*, i64 }** %2, align 8
  %3 = load %"core::fmt::Void"*, %"core::fmt::Void"** %transmute_temp1, align 8, !nonnull !0
  br label %bb2

bb2:                                              ; preds = %bb1
  %4 = bitcast { i8*, i8* }* %_0 to %"core::fmt::Void"**
  store %"core::fmt::Void"* %3, %"core::fmt::Void"** %4, align 8
  %5 = getelementptr inbounds { i8*, i8* }, { i8*, i8* }* %_0, i32 0, i32 1
  %6 = bitcast i8** %5 to i1 (%"core::fmt::Void"*, %"core::fmt::Formatter"*)**
  store i1 (%"core::fmt::Void"*, %"core::fmt::Formatter"*)* %1, i1 (%"core::fmt::Void"*, %"core::fmt::Formatter"*)** %6, align 8
  %7 = getelementptr inbounds { i8*, i8* }, { i8*, i8* }* %_0, i32 0, i32 0
  %8 = load i8*, i8** %7, align 8, !nonnull !0
  %9 = getelementptr inbounds { i8*, i8* }, { i8*, i8* }* %_0, i32 0, i32 1
  %10 = load i8*, i8** %9, align 8, !nonnull !0
  %11 = insertvalue { i8*, i8* } undef, i8* %8, 0
  %12 = insertvalue { i8*, i8* } %11, i8* %10, 1
  ret { i8*, i8* } %12
}

; core::fmt::ArgumentV1::new
; Function Attrs: uwtable
define { i8*, i8* } @_ZN4core3fmt10ArgumentV13new17hdf892351cf4716dbE(%"core::str::Utf8Error"* noalias readonly align 8 dereferenceable(16) %x, i1 (%"core::str::Utf8Error"*, %"core::fmt::Formatter"*)* nonnull %f) unnamed_addr #0 {
start:
  %transmute_temp1 = alloca %"core::fmt::Void"*, align 8
  %transmute_temp = alloca i1 (%"core::fmt::Void"*, %"core::fmt::Formatter"*)*, align 8
  %_0 = alloca { i8*, i8* }, align 8
  %0 = bitcast i1 (%"core::fmt::Void"*, %"core::fmt::Formatter"*)** %transmute_temp to i1 (%"core::str::Utf8Error"*, %"core::fmt::Formatter"*)**
  store i1 (%"core::str::Utf8Error"*, %"core::fmt::Formatter"*)* %f, i1 (%"core::str::Utf8Error"*, %"core::fmt::Formatter"*)** %0, align 8
  %1 = load i1 (%"core::fmt::Void"*, %"core::fmt::Formatter"*)*, i1 (%"core::fmt::Void"*, %"core::fmt::Formatter"*)** %transmute_temp, align 8, !nonnull !0
  br label %bb1

bb1:                                              ; preds = %start
  %2 = bitcast %"core::fmt::Void"** %transmute_temp1 to %"core::str::Utf8Error"**
  store %"core::str::Utf8Error"* %x, %"core::str::Utf8Error"** %2, align 8
  %3 = load %"core::fmt::Void"*, %"core::fmt::Void"** %transmute_temp1, align 8, !nonnull !0
  br label %bb2

bb2:                                              ; preds = %bb1
  %4 = bitcast { i8*, i8* }* %_0 to %"core::fmt::Void"**
  store %"core::fmt::Void"* %3, %"core::fmt::Void"** %4, align 8
  %5 = getelementptr inbounds { i8*, i8* }, { i8*, i8* }* %_0, i32 0, i32 1
  %6 = bitcast i8** %5 to i1 (%"core::fmt::Void"*, %"core::fmt::Formatter"*)**
  store i1 (%"core::fmt::Void"*, %"core::fmt::Formatter"*)* %1, i1 (%"core::fmt::Void"*, %"core::fmt::Formatter"*)** %6, align 8
  %7 = getelementptr inbounds { i8*, i8* }, { i8*, i8* }* %_0, i32 0, i32 0
  %8 = load i8*, i8** %7, align 8, !nonnull !0
  %9 = getelementptr inbounds { i8*, i8* }, { i8*, i8* }* %_0, i32 0, i32 1
  %10 = load i8*, i8** %9, align 8, !nonnull !0
  %11 = insertvalue { i8*, i8* } undef, i8* %8, 0
  %12 = insertvalue { i8*, i8* } %11, i8* %10, 1
  ret { i8*, i8* } %12
}

; core::fmt::Arguments::new_v1
; Function Attrs: inlinehint uwtable
define internal void @_ZN4core3fmt9Arguments6new_v117hc766c224a8f6dba9E(%"core::fmt::Arguments"* noalias nocapture sret dereferenceable(48), [0 x { [0 x i8]*, i64 }]* noalias nonnull readonly align 8 %pieces.0, i64 %pieces.1, [0 x { i8*, i8* }]* noalias nonnull readonly align 8 %args.0, i64 %args.1) unnamed_addr #1 {
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

; core::slice::from_raw_parts
; Function Attrs: inlinehint uwtable
define { [0 x i8]*, i64 } @_ZN4core5slice14from_raw_parts17h6151e38f9ce62d7aE(i8* %data, i64 %len) unnamed_addr #1 {
start:
  %_4 = alloca { i8*, i64 }, align 8
  %_3 = alloca %"core::slice::Repr<u8>", align 8
  %0 = bitcast { i8*, i64 }* %_4 to i8**
  store i8* %data, i8** %0, align 8
  %1 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %_4, i32 0, i32 1
  store i64 %len, i64* %1, align 8
  %2 = bitcast %"core::slice::Repr<u8>"* %_3 to { i8*, i64 }*
  %3 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %_4, i32 0, i32 0
  %4 = load i8*, i8** %3, align 8
  %5 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %_4, i32 0, i32 1
  %6 = load i64, i64* %5, align 8
  %7 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %2, i32 0, i32 0
  store i8* %4, i8** %7, align 8
  %8 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %2, i32 0, i32 1
  store i64 %6, i64* %8, align 8
  %9 = bitcast %"core::slice::Repr<u8>"* %_3 to { [0 x i8]*, i64 }*
  %10 = getelementptr inbounds { [0 x i8]*, i64 }, { [0 x i8]*, i64 }* %9, i32 0, i32 0
  %11 = load [0 x i8]*, [0 x i8]** %10, align 8, !nonnull !0
  %12 = getelementptr inbounds { [0 x i8]*, i64 }, { [0 x i8]*, i64 }* %9, i32 0, i32 1
  %13 = load i64, i64* %12, align 8
  %14 = insertvalue { [0 x i8]*, i64 } undef, [0 x i8]* %11, 0
  %15 = insertvalue { [0 x i8]*, i64 } %14, i64 %13, 1
  ret { [0 x i8]*, i64 } %15
}

; core::result::unwrap_failed
; Function Attrs: cold noinline noreturn uwtable
define void @_ZN4core6result13unwrap_failed17h8cbce668f13a1c16E([0 x i8]* noalias nonnull readonly align 1, i64, %"core::str::Utf8Error"* noalias nocapture dereferenceable(16) %error) unnamed_addr #2 personality i32 (...)* @__CxxFrameHandler3 {
start:
  %_11 = alloca { i64*, i64* }, align 8
  %_10 = alloca [2 x { i8*, i8* }], align 8
  %_3 = alloca %"core::fmt::Arguments", align 8
  %msg = alloca { [0 x i8]*, i64 }, align 8
  %2 = getelementptr inbounds { [0 x i8]*, i64 }, { [0 x i8]*, i64 }* %msg, i32 0, i32 0
  store [0 x i8]* %0, [0 x i8]** %2, align 8
  %3 = getelementptr inbounds { [0 x i8]*, i64 }, { [0 x i8]*, i64 }* %msg, i32 0, i32 1
  store i64 %1, i64* %3, align 8
  %4 = bitcast { i64*, i64* }* %_11 to { [0 x i8]*, i64 }**
  store { [0 x i8]*, i64 }* %msg, { [0 x i8]*, i64 }** %4, align 8
  %5 = getelementptr inbounds { i64*, i64* }, { i64*, i64* }* %_11, i32 0, i32 1
  %6 = bitcast i64** %5 to %"core::str::Utf8Error"**
  store %"core::str::Utf8Error"* %error, %"core::str::Utf8Error"** %6, align 8
  %7 = bitcast { i64*, i64* }* %_11 to { [0 x i8]*, i64 }**
  %8 = load { [0 x i8]*, i64 }*, { [0 x i8]*, i64 }** %7, align 8, !nonnull !0
  %9 = getelementptr inbounds { i64*, i64* }, { i64*, i64* }* %_11, i32 0, i32 1
  %10 = bitcast i64** %9 to %"core::str::Utf8Error"**
  %11 = load %"core::str::Utf8Error"*, %"core::str::Utf8Error"** %10, align 8, !nonnull !0
; invoke core::fmt::ArgumentV1::new
  %12 = invoke { i8*, i8* } @_ZN4core3fmt10ArgumentV13new17h5f8e96903532d478E({ [0 x i8]*, i64 }* noalias readonly align 8 dereferenceable(16) %8, i1 ({ [0 x i8]*, i64 }*, %"core::fmt::Formatter"*)* nonnull @"_ZN44_$LT$$RF$T$u20$as$u20$core..fmt..Display$GT$3fmt17h53cb8273fc649950E")
          to label %bb2 unwind label %funclet_bb3

bb1:                                              ; preds = %bb3
  cleanupret from %cleanuppad unwind to caller

bb2:                                              ; preds = %start
  %13 = extractvalue { i8*, i8* } %12, 0
  %14 = extractvalue { i8*, i8* } %12, 1
; invoke core::fmt::ArgumentV1::new
  %15 = invoke { i8*, i8* } @_ZN4core3fmt10ArgumentV13new17hdf892351cf4716dbE(%"core::str::Utf8Error"* noalias readonly align 8 dereferenceable(16) %11, i1 (%"core::str::Utf8Error"*, %"core::fmt::Formatter"*)* nonnull @"_ZN57_$LT$core..str..Utf8Error$u20$as$u20$core..fmt..Debug$GT$3fmt17h198912a1444b8b49E")
          to label %bb4 unwind label %funclet_bb3

bb3:                                              ; preds = %funclet_bb3
  br label %bb1

bb4:                                              ; preds = %bb2
  %16 = extractvalue { i8*, i8* } %15, 0
  %17 = extractvalue { i8*, i8* } %15, 1
  %18 = bitcast [2 x { i8*, i8* }]* %_10 to { i8*, i8* }*
  %19 = getelementptr inbounds { i8*, i8* }, { i8*, i8* }* %18, i32 0, i32 0
  store i8* %13, i8** %19, align 8
  %20 = getelementptr inbounds { i8*, i8* }, { i8*, i8* }* %18, i32 0, i32 1
  store i8* %14, i8** %20, align 8
  %21 = getelementptr inbounds [2 x { i8*, i8* }], [2 x { i8*, i8* }]* %_10, i32 0, i32 1
  %22 = getelementptr inbounds { i8*, i8* }, { i8*, i8* }* %21, i32 0, i32 0
  store i8* %16, i8** %22, align 8
  %23 = getelementptr inbounds { i8*, i8* }, { i8*, i8* }* %21, i32 0, i32 1
  store i8* %17, i8** %23, align 8
  %24 = bitcast [2 x { i8*, i8* }]* %_10 to [0 x { i8*, i8* }]*
; invoke core::fmt::Arguments::new_v1
  invoke void @_ZN4core3fmt9Arguments6new_v117hc766c224a8f6dba9E(%"core::fmt::Arguments"* noalias nocapture sret dereferenceable(48) %_3, [0 x { [0 x i8]*, i64 }]* noalias nonnull readonly align 8 bitcast (<{ i8*, [8 x i8], i8*, [8 x i8] }>* @2 to [0 x { [0 x i8]*, i64 }]*), i64 2, [0 x { i8*, i8* }]* noalias nonnull readonly align 8 %24, i64 2)
          to label %bb5 unwind label %funclet_bb3

bb5:                                              ; preds = %bb4
; invoke core::panicking::panic_fmt
  invoke void @_ZN4core9panicking9panic_fmt17h1d328484f8b575f2E(%"core::fmt::Arguments"* noalias nocapture dereferenceable(48) %_3, { [0 x i64], { [0 x i8]*, i64 }, [0 x i32], i32, [0 x i32], i32, [0 x i32] }* noalias readonly align 8 dereferenceable(24) bitcast (<{ i8*, [16 x i8] }>* @4 to { [0 x i64], { [0 x i8]*, i64 }, [0 x i32], i32, [0 x i32], i32, [0 x i32] }*))
          to label %unreachable unwind label %funclet_bb3

funclet_bb3:                                      ; preds = %bb5, %bb4, %bb2, %start
  %cleanuppad = cleanuppad within none []
  br label %bb3

unreachable:                                      ; preds = %bb5
  unreachable
}

; core::result::Result<T,E>::expect
; Function Attrs: inlinehint uwtable
define { [0 x i8]*, i64 } @"_ZN4core6result19Result$LT$T$C$E$GT$6expect17hc7852bf9b5dc7d00E"(%"core::result::Result<&str, core::str::Utf8Error>"* noalias nocapture dereferenceable(24) %self, [0 x i8]* noalias nonnull readonly align 1 %msg.0, i64 %msg.1) unnamed_addr #1 personality i32 (...)* @__CxxFrameHandler3 {
start:
  %_7 = alloca %"core::str::Utf8Error", align 8
  %e = alloca %"core::str::Utf8Error", align 8
  %0 = bitcast %"core::result::Result<&str, core::str::Utf8Error>"* %self to i64*
  %1 = load i64, i64* %0, align 8, !range !1
  switch i64 %1, label %bb2 [
    i64 0, label %bb3
    i64 1, label %bb4
  ]

bb1:                                              ; preds = %bb5, %bb6
  cleanupret from %cleanuppad unwind to caller

bb2:                                              ; preds = %start
  unreachable

bb3:                                              ; preds = %start
  %2 = bitcast %"core::result::Result<&str, core::str::Utf8Error>"* %self to %"core::result::Result<&str, core::str::Utf8Error>::Ok"*
  %3 = getelementptr inbounds %"core::result::Result<&str, core::str::Utf8Error>::Ok", %"core::result::Result<&str, core::str::Utf8Error>::Ok"* %2, i32 0, i32 1
  %4 = getelementptr inbounds { [0 x i8]*, i64 }, { [0 x i8]*, i64 }* %3, i32 0, i32 0
  %5 = load [0 x i8]*, [0 x i8]** %4, align 8, !nonnull !0
  %6 = getelementptr inbounds { [0 x i8]*, i64 }, { [0 x i8]*, i64 }* %3, i32 0, i32 1
  %7 = load i64, i64* %6, align 8
  %8 = bitcast %"core::result::Result<&str, core::str::Utf8Error>"* %self to i64*
  %9 = load i64, i64* %8, align 8, !range !1
  %10 = icmp eq i64 %9, 0
  br i1 %10, label %bb7, label %bb8

bb4:                                              ; preds = %start
  %11 = bitcast %"core::result::Result<&str, core::str::Utf8Error>"* %self to %"core::result::Result<&str, core::str::Utf8Error>::Err"*
  %12 = getelementptr inbounds %"core::result::Result<&str, core::str::Utf8Error>::Err", %"core::result::Result<&str, core::str::Utf8Error>::Err"* %11, i32 0, i32 1
  %13 = bitcast %"core::str::Utf8Error"* %e to i8*
  %14 = bitcast %"core::str::Utf8Error"* %12 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %13, i8* align 8 %14, i64 16, i1 false)
  %15 = bitcast %"core::str::Utf8Error"* %_7 to i8*
  %16 = bitcast %"core::str::Utf8Error"* %e to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %15, i8* align 8 %16, i64 16, i1 false)
; invoke core::result::unwrap_failed
  invoke void @_ZN4core6result13unwrap_failed17h8cbce668f13a1c16E([0 x i8]* noalias nonnull readonly align 1 %msg.0, i64 %msg.1, %"core::str::Utf8Error"* noalias nocapture dereferenceable(16) %_7)
          to label %unreachable unwind label %funclet_bb6

bb5:                                              ; preds = %bb6
  br label %bb1

bb6:                                              ; preds = %funclet_bb6
  %17 = bitcast %"core::result::Result<&str, core::str::Utf8Error>"* %self to i64*
  %18 = load i64, i64* %17, align 8, !range !1
  %19 = icmp eq i64 %18, 0
  br i1 %19, label %bb5, label %bb1

bb7:                                              ; preds = %bb8, %bb3
  %20 = insertvalue { [0 x i8]*, i64 } undef, [0 x i8]* %5, 0
  %21 = insertvalue { [0 x i8]*, i64 } %20, i64 %7, 1
  ret { [0 x i8]*, i64 } %21

bb8:                                              ; preds = %bb3
  br label %bb7

funclet_bb6:                                      ; preds = %bb4
  %cleanuppad = cleanuppad within none []
  br label %bb6

unreachable:                                      ; preds = %bb4
  unreachable
}

; a_rust_file::ScriptString::as_str
; Function Attrs: uwtable
define { [0 x i8]*, i64 } @_ZN11a_rust_file12ScriptString6as_str17h6fafcbb615e7c991E({ i8*, i64 }* noalias readonly align 8 dereferenceable(16) %self) unnamed_addr #0 {
start:
  %_8 = alloca %"core::result::Result<&str, core::str::Utf8Error>", align 8
  %0 = bitcast { i8*, i64 }* %self to i8**
  %1 = load i8*, i8** %0, align 8
  %2 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %self, i32 0, i32 1
  %3 = load i64, i64* %2, align 8
; call core::slice::from_raw_parts
  %4 = call { [0 x i8]*, i64 } @_ZN4core5slice14from_raw_parts17h6151e38f9ce62d7aE(i8* %1, i64 %3)
  %5 = extractvalue { [0 x i8]*, i64 } %4, 0
  %6 = extractvalue { [0 x i8]*, i64 } %4, 1
  br label %bb1

bb1:                                              ; preds = %start
; call core::str::from_utf8
  call void @_ZN4core3str9from_utf817h100df2f86bd1431aE(%"core::result::Result<&str, core::str::Utf8Error>"* noalias nocapture sret dereferenceable(24) %_8, [0 x i8]* noalias nonnull readonly align 1 %5, i64 %6)
  br label %bb2

bb2:                                              ; preds = %bb1
; call core::result::Result<T,E>::expect
  %7 = call { [0 x i8]*, i64 } @"_ZN4core6result19Result$LT$T$C$E$GT$6expect17hc7852bf9b5dc7d00E"(%"core::result::Result<&str, core::str::Utf8Error>"* noalias nocapture dereferenceable(24) %_8, [0 x i8]* noalias nonnull readonly align 1 bitcast (<{ [27 x i8] }>* @5 to [0 x i8]*), i64 27)
  %8 = extractvalue { [0 x i8]*, i64 } %7, 0
  %9 = extractvalue { [0 x i8]*, i64 } %7, 1
  br label %bb3

bb3:                                              ; preds = %bb2
  %10 = insertvalue { [0 x i8]*, i64 } undef, [0 x i8]* %8, 0
  %11 = insertvalue { [0 x i8]*, i64 } %10, i64 %9, 1
  ret { [0 x i8]*, i64 } %11
}

; Function Attrs: nounwind uwtable
define void @print({ i8*, i64 }* noalias nocapture dereferenceable(16) %s) unnamed_addr #3 {
start:
  %_13 = alloca { [0 x i8]*, i64 }, align 8
  %_11 = alloca i64*, align 8
  %_10 = alloca [1 x { i8*, i8* }], align 8
  %_3 = alloca %"core::fmt::Arguments", align 8
; call a_rust_file::ScriptString::as_str
  %0 = call { [0 x i8]*, i64 } @_ZN11a_rust_file12ScriptString6as_str17h6fafcbb615e7c991E({ i8*, i64 }* noalias readonly align 8 dereferenceable(16) %s)
  store { [0 x i8]*, i64 } %0, { [0 x i8]*, i64 }* %_13, align 8
  br label %bb1

bb1:                                              ; preds = %start
  %1 = bitcast i64** %_11 to { [0 x i8]*, i64 }**
  store { [0 x i8]*, i64 }* %_13, { [0 x i8]*, i64 }** %1, align 8
  %2 = bitcast i64** %_11 to { [0 x i8]*, i64 }**
  %3 = load { [0 x i8]*, i64 }*, { [0 x i8]*, i64 }** %2, align 8, !nonnull !0
; call core::fmt::ArgumentV1::new
  %4 = call { i8*, i8* } @_ZN4core3fmt10ArgumentV13new17h5f8e96903532d478E({ [0 x i8]*, i64 }* noalias readonly align 8 dereferenceable(16) %3, i1 ({ [0 x i8]*, i64 }*, %"core::fmt::Formatter"*)* nonnull @"_ZN44_$LT$$RF$T$u20$as$u20$core..fmt..Display$GT$3fmt17h53cb8273fc649950E")
  %5 = extractvalue { i8*, i8* } %4, 0
  %6 = extractvalue { i8*, i8* } %4, 1
  br label %bb2

bb2:                                              ; preds = %bb1
  %7 = bitcast [1 x { i8*, i8* }]* %_10 to { i8*, i8* }*
  %8 = getelementptr inbounds { i8*, i8* }, { i8*, i8* }* %7, i32 0, i32 0
  store i8* %5, i8** %8, align 8
  %9 = getelementptr inbounds { i8*, i8* }, { i8*, i8* }* %7, i32 0, i32 1
  store i8* %6, i8** %9, align 8
  %10 = bitcast [1 x { i8*, i8* }]* %_10 to [0 x { i8*, i8* }]*
; call core::fmt::Arguments::new_v1
  call void @_ZN4core3fmt9Arguments6new_v117hc766c224a8f6dba9E(%"core::fmt::Arguments"* noalias nocapture sret dereferenceable(48) %_3, [0 x { [0 x i8]*, i64 }]* noalias nonnull readonly align 8 bitcast (<{ i8*, [8 x i8], i8*, [8 x i8] }>* @7 to [0 x { [0 x i8]*, i64 }]*), i64 2, [0 x { i8*, i8* }]* noalias nonnull readonly align 8 %10, i64 1)
  br label %bb3

bb3:                                              ; preds = %bb2
; call std::io::stdio::_print
  call void @_ZN3std2io5stdio6_print17haefb24384b3cad8cE(%"core::fmt::Arguments"* noalias nocapture dereferenceable(48) %_3)
  br label %bb4

bb4:                                              ; preds = %bb3
  ret void
}

; <str as core::fmt::Display>::fmt
; Function Attrs: uwtable
declare zeroext i1 @"_ZN42_$LT$str$u20$as$u20$core..fmt..Display$GT$3fmt17h1abc233d12afc37fE"([0 x i8]* noalias nonnull readonly align 1, i64, %"core::fmt::Formatter"* align 8 dereferenceable(96)) unnamed_addr #0

declare i32 @__CxxFrameHandler3(...) unnamed_addr #4

; <core::str::Utf8Error as core::fmt::Debug>::fmt
; Function Attrs: uwtable
declare zeroext i1 @"_ZN57_$LT$core..str..Utf8Error$u20$as$u20$core..fmt..Debug$GT$3fmt17h198912a1444b8b49E"(%"core::str::Utf8Error"* noalias readonly align 8 dereferenceable(16), %"core::fmt::Formatter"* align 8 dereferenceable(96)) unnamed_addr #0

; core::panicking::panic_fmt
; Function Attrs: cold noinline noreturn uwtable
declare void @_ZN4core9panicking9panic_fmt17h1d328484f8b575f2E(%"core::fmt::Arguments"* noalias nocapture dereferenceable(48), { [0 x i64], { [0 x i8]*, i64 }, [0 x i32], i32, [0 x i32], i32, [0 x i32] }* noalias readonly align 8 dereferenceable(24)) unnamed_addr #2

; Function Attrs: argmemonly nounwind
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* nocapture writeonly, i8* nocapture readonly, i64, i1) #5

; core::str::from_utf8
; Function Attrs: uwtable
declare void @_ZN4core3str9from_utf817h100df2f86bd1431aE(%"core::result::Result<&str, core::str::Utf8Error>"* noalias nocapture sret dereferenceable(24), [0 x i8]* noalias nonnull readonly align 1, i64) unnamed_addr #0

; std::io::stdio::_print
; Function Attrs: uwtable
declare void @_ZN3std2io5stdio6_print17haefb24384b3cad8cE(%"core::fmt::Arguments"* noalias nocapture dereferenceable(48)) unnamed_addr #0

attributes #0 = { uwtable "target-cpu"="x86-64" }
attributes #1 = { inlinehint uwtable "target-cpu"="x86-64" }
attributes #2 = { cold noinline noreturn uwtable "target-cpu"="x86-64" }
attributes #3 = { nounwind uwtable "target-cpu"="x86-64" }
attributes #4 = { "target-cpu"="x86-64" }
attributes #5 = { argmemonly nounwind }

!0 = !{}
!1 = !{i64 0, i64 2}

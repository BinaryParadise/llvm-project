; NOTE: Assertions have been autogenerated by utils/update_test_checks.py UTC_ARGS: --function-signature --check-attributes --check-globals
; RUN: opt -attributor -enable-new-pm=0 -attributor-manifest-internal  -attributor-max-iterations-verify -attributor-annotate-decl-cs -attributor-max-iterations=1 -S < %s | FileCheck %s --check-prefixes=CHECK,NOT_CGSCC_NPM,NOT_CGSCC_OPM,NOT_TUNIT_NPM,IS__TUNIT____,IS________OPM,IS__TUNIT_OPM
; RUN: opt -aa-pipeline=basic-aa -passes=attributor -attributor-manifest-internal  -attributor-max-iterations-verify -attributor-annotate-decl-cs -attributor-max-iterations=2 -S < %s | FileCheck %s --check-prefixes=CHECK,NOT_CGSCC_OPM,NOT_CGSCC_NPM,NOT_TUNIT_OPM,IS__TUNIT____,IS________NPM,IS__TUNIT_NPM
; RUN: opt -attributor-cgscc -enable-new-pm=0 -attributor-manifest-internal  -attributor-annotate-decl-cs -S < %s | FileCheck %s --check-prefixes=CHECK,NOT_TUNIT_NPM,NOT_TUNIT_OPM,NOT_CGSCC_NPM,IS__CGSCC____,IS________OPM,IS__CGSCC_OPM
; RUN: opt -aa-pipeline=basic-aa -passes=attributor-cgscc -attributor-manifest-internal  -attributor-annotate-decl-cs -S < %s | FileCheck %s --check-prefixes=CHECK,NOT_TUNIT_NPM,NOT_TUNIT_OPM,NOT_CGSCC_OPM,IS__CGSCC____,IS________NPM,IS__CGSCC_NPM

target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define i64 @fn2() {
; IS__TUNIT_OPM: Function Attrs: nofree nosync nounwind readnone willreturn
; IS__TUNIT_OPM-LABEL: define {{[^@]+}}@fn2
; IS__TUNIT_OPM-SAME: () #[[ATTR0:[0-9]+]] {
; IS__TUNIT_OPM-NEXT:  entry:
; IS__TUNIT_OPM-NEXT:    [[CALL2:%.*]] = call i64 @fn1(i64 undef) #[[ATTR0]]
; IS__TUNIT_OPM-NEXT:    ret i64 [[CALL2]]
;
; IS__TUNIT_NPM: Function Attrs: nofree nosync nounwind readnone willreturn
; IS__TUNIT_NPM-LABEL: define {{[^@]+}}@fn2
; IS__TUNIT_NPM-SAME: () #[[ATTR0:[0-9]+]] {
; IS__TUNIT_NPM-NEXT:  entry:
; IS__TUNIT_NPM-NEXT:    [[CALL2:%.*]] = call i64 @fn1(i64 undef) #[[ATTR0]], !range [[RNG0:![0-9]+]]
; IS__TUNIT_NPM-NEXT:    ret i64 [[CALL2]]
;
; IS__CGSCC_OPM: Function Attrs: nofree norecurse nosync nounwind readnone willreturn
; IS__CGSCC_OPM-LABEL: define {{[^@]+}}@fn2
; IS__CGSCC_OPM-SAME: () #[[ATTR0:[0-9]+]] {
; IS__CGSCC_OPM-NEXT:  entry:
; IS__CGSCC_OPM-NEXT:    [[CONV:%.*]] = sext i32 undef to i64
; IS__CGSCC_OPM-NEXT:    [[DIV:%.*]] = sdiv i64 8, 0
; IS__CGSCC_OPM-NEXT:    [[CALL2:%.*]] = call i64 @fn1(i64 undef) #[[ATTR1:[0-9]+]]
; IS__CGSCC_OPM-NEXT:    ret i64 [[CALL2]]
;
; IS__CGSCC_NPM: Function Attrs: nofree norecurse nosync nounwind readnone willreturn
; IS__CGSCC_NPM-LABEL: define {{[^@]+}}@fn2
; IS__CGSCC_NPM-SAME: () #[[ATTR0:[0-9]+]] {
; IS__CGSCC_NPM-NEXT:  entry:
; IS__CGSCC_NPM-NEXT:    [[CONV:%.*]] = sext i32 undef to i64
; IS__CGSCC_NPM-NEXT:    [[DIV:%.*]] = sdiv i64 8, 0
; IS__CGSCC_NPM-NEXT:    [[CALL2:%.*]] = call i64 @fn1(i64 undef) #[[ATTR1:[0-9]+]], !range [[RNG0:![0-9]+]]
; IS__CGSCC_NPM-NEXT:    ret i64 [[CALL2]]
;
entry:
  %conv = sext i32 undef to i64
  %div = sdiv i64 8, %conv
  %call2 = call i64 @fn1(i64 %div)
  ret i64 %call2
}

define i64 @fn2b(i32 %arg) {
; IS__TUNIT_OPM: Function Attrs: nofree nosync nounwind readnone willreturn
; IS__TUNIT_OPM-LABEL: define {{[^@]+}}@fn2b
; IS__TUNIT_OPM-SAME: (i32 [[ARG:%.*]]) #[[ATTR0]] {
; IS__TUNIT_OPM-NEXT:  entry:
; IS__TUNIT_OPM-NEXT:    [[CONV:%.*]] = sext i32 [[ARG]] to i64
; IS__TUNIT_OPM-NEXT:    [[DIV:%.*]] = sdiv i64 8, [[CONV]]
; IS__TUNIT_OPM-NEXT:    [[CALL2:%.*]] = call i64 @fn1(i64 [[DIV]]) #[[ATTR0]]
; IS__TUNIT_OPM-NEXT:    ret i64 [[CALL2]]
;
; IS__TUNIT_NPM: Function Attrs: nofree nosync nounwind readnone willreturn
; IS__TUNIT_NPM-LABEL: define {{[^@]+}}@fn2b
; IS__TUNIT_NPM-SAME: (i32 [[ARG:%.*]]) #[[ATTR0]] {
; IS__TUNIT_NPM-NEXT:  entry:
; IS__TUNIT_NPM-NEXT:    [[CONV:%.*]] = sext i32 [[ARG]] to i64
; IS__TUNIT_NPM-NEXT:    [[DIV:%.*]] = sdiv i64 8, [[CONV]]
; IS__TUNIT_NPM-NEXT:    [[CALL2:%.*]] = call i64 @fn1(i64 [[DIV]]) #[[ATTR0]], !range [[RNG0]]
; IS__TUNIT_NPM-NEXT:    ret i64 [[CALL2]]
;
; IS__CGSCC____: Function Attrs: nofree norecurse nosync nounwind readnone willreturn
; IS__CGSCC____-LABEL: define {{[^@]+}}@fn2b
; IS__CGSCC____-SAME: (i32 [[ARG:%.*]]) #[[ATTR0:[0-9]+]] {
; IS__CGSCC____-NEXT:  entry:
; IS__CGSCC____-NEXT:    [[CONV:%.*]] = sext i32 [[ARG]] to i64
; IS__CGSCC____-NEXT:    [[DIV:%.*]] = sdiv i64 8, [[CONV]]
; IS__CGSCC____-NEXT:    [[CALL2:%.*]] = call i64 @fn1(i64 [[DIV]]) #[[ATTR1:[0-9]+]], !range [[RNG0:![0-9]+]]
; IS__CGSCC____-NEXT:    ret i64 [[CALL2]]
;
entry:
  %conv = sext i32 %arg to i64
  %div = sdiv i64 8, %conv
  %call2 = call i64 @fn1(i64 %div)
  ret i64 %call2
}

define i64 @fn2c() {
; IS__TUNIT_OPM: Function Attrs: nofree nosync nounwind readnone willreturn
; IS__TUNIT_OPM-LABEL: define {{[^@]+}}@fn2c
; IS__TUNIT_OPM-SAME: () #[[ATTR0]] {
; IS__TUNIT_OPM-NEXT:  entry:
; IS__TUNIT_OPM-NEXT:    [[CALL2:%.*]] = call i64 @fn1(i64 noundef 42) #[[ATTR0]]
; IS__TUNIT_OPM-NEXT:    ret i64 [[CALL2]]
;
; IS__TUNIT_NPM: Function Attrs: nofree nosync nounwind readnone willreturn
; IS__TUNIT_NPM-LABEL: define {{[^@]+}}@fn2c
; IS__TUNIT_NPM-SAME: () #[[ATTR0]] {
; IS__TUNIT_NPM-NEXT:  entry:
; IS__TUNIT_NPM-NEXT:    [[CALL2:%.*]] = call i64 @fn1(i64 noundef 42) #[[ATTR0]], !range [[RNG0]]
; IS__TUNIT_NPM-NEXT:    ret i64 [[CALL2]]
;
; IS__CGSCC_OPM: Function Attrs: nofree norecurse nosync nounwind readnone willreturn
; IS__CGSCC_OPM-LABEL: define {{[^@]+}}@fn2c
; IS__CGSCC_OPM-SAME: () #[[ATTR0]] {
; IS__CGSCC_OPM-NEXT:  entry:
; IS__CGSCC_OPM-NEXT:    [[CONV:%.*]] = sext i32 undef to i64
; IS__CGSCC_OPM-NEXT:    [[ADD:%.*]] = add i64 42, 0
; IS__CGSCC_OPM-NEXT:    [[CALL2:%.*]] = call i64 @fn1(i64 noundef 42) #[[ATTR1]]
; IS__CGSCC_OPM-NEXT:    ret i64 [[CALL2]]
;
; IS__CGSCC_NPM: Function Attrs: nofree norecurse nosync nounwind readnone willreturn
; IS__CGSCC_NPM-LABEL: define {{[^@]+}}@fn2c
; IS__CGSCC_NPM-SAME: () #[[ATTR0]] {
; IS__CGSCC_NPM-NEXT:  entry:
; IS__CGSCC_NPM-NEXT:    [[CONV:%.*]] = sext i32 undef to i64
; IS__CGSCC_NPM-NEXT:    [[ADD:%.*]] = add i64 42, 0
; IS__CGSCC_NPM-NEXT:    ret i64 42
;
entry:
  %conv = sext i32 undef to i64
  %add = add i64 42, %conv
  %call2 = call i64 @fn1(i64 %add)
  ret i64 %call2
}

define internal i64 @fn1(i64 %p1) {
; IS__TUNIT____: Function Attrs: nofree nosync nounwind readnone willreturn
; IS__TUNIT____-LABEL: define {{[^@]+}}@fn1
; IS__TUNIT____-SAME: (i64 returned [[P1:%.*]]) #[[ATTR0:[0-9]+]] {
; IS__TUNIT____-NEXT:  entry:
; IS__TUNIT____-NEXT:    [[TOBOOL:%.*]] = icmp ne i64 [[P1]], 0
; IS__TUNIT____-NEXT:    [[COND:%.*]] = select i1 [[TOBOOL]], i64 [[P1]], i64 [[P1]]
; IS__TUNIT____-NEXT:    ret i64 [[COND]]
;
; IS__CGSCC____: Function Attrs: nofree norecurse nosync nounwind readnone willreturn
; IS__CGSCC____-LABEL: define {{[^@]+}}@fn1
; IS__CGSCC____-SAME: (i64 returned [[P1:%.*]]) #[[ATTR0]] {
; IS__CGSCC____-NEXT:  entry:
; IS__CGSCC____-NEXT:    [[TOBOOL:%.*]] = icmp ne i64 [[P1]], 0
; IS__CGSCC____-NEXT:    [[COND:%.*]] = select i1 [[TOBOOL]], i64 [[P1]], i64 [[P1]]
; IS__CGSCC____-NEXT:    ret i64 [[COND]]
;
entry:
  %tobool = icmp ne i64 %p1, 0
  %cond = select i1 %tobool, i64 %p1, i64 %p1
  ret i64 %cond
}
;.
; IS__TUNIT____: attributes #[[ATTR0]] = { nofree nosync nounwind readnone willreturn }
;.
; IS__CGSCC____: attributes #[[ATTR0]] = { nofree norecurse nosync nounwind readnone willreturn }
; IS__CGSCC____: attributes #[[ATTR1]] = { readnone willreturn }
;.
; IS__TUNIT_NPM: [[RNG0]] = !{i64 -2147483606, i64 2147483690}
;.
; IS__CGSCC____: [[RNG0]] = !{i64 -8, i64 43}
;.

; ModuleID = 'hmac_sha256.bc'
source_filename = "hmac_sha256.c"
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.12.0"

@__func__.hmac_sha256 = private unnamed_addr constant [12 x i8] c"hmac_sha256\00", align 1
@.str = private unnamed_addr constant [14 x i8] c"hmac_sha256.c\00", align 1
@.str.1 = private unnamed_addr constant [33 x i8] c"message_size <= MAX_MESSAGE_SIZE\00", align 1
@inner = internal global [192 x i8] zeroinitializer, align 16

; Function Attrs: nounwind ssp uwtable
define void @hmac_sha256(i8*, i64, i8*, i64, i8*) #0 {
  %6 = alloca i8*, align 8
  %7 = alloca i64, align 8
  %8 = alloca i8*, align 8
  %9 = alloca i64, align 8
  %10 = alloca i8*, align 8
  %11 = alloca [64 x i8], align 16
  %12 = alloca i64, align 8
  %13 = alloca i32, align 4
  %14 = alloca i32, align 4
  %15 = alloca [96 x i8], align 16
  %16 = alloca i32, align 4
  store i8* %0, i8** %6, align 8
  store i64 %1, i64* %7, align 8
  store i8* %2, i8** %8, align 8
  store i64 %3, i64* %9, align 8
  store i8* %4, i8** %10, align 8
  %17 = load i64, i64* %9, align 8
  %18 = icmp ule i64 %17, 128
  %19 = xor i1 %18, true
  %20 = zext i1 %19 to i32
  %21 = sext i32 %20 to i64
  %22 = icmp ne i64 %21, 0
  br i1 %22, label %23, label %25

; <label>:23:                                     ; preds = %5
  call void @__assert_rtn(i8* getelementptr inbounds ([12 x i8], [12 x i8]* @__func__.hmac_sha256, i32 0, i32 0), i8* getelementptr inbounds ([14 x i8], [14 x i8]* @.str, i32 0, i32 0), i32 29, i8* getelementptr inbounds ([33 x i8], [33 x i8]* @.str.1, i32 0, i32 0)) #4
  unreachable
                                                  ; No predecessors!
  br label %26

; <label>:25:                                     ; preds = %5
  br label %26

; <label>:26:                                     ; preds = %25, %24
  %27 = load i64, i64* %7, align 8
  %28 = icmp ugt i64 %27, 64
  br i1 %28, label %29, label %33

; <label>:29:                                     ; preds = %26
  %30 = load i8*, i8** %6, align 8
  %31 = load i64, i64* %7, align 8
  %32 = getelementptr inbounds [64 x i8], [64 x i8]* %11, i32 0, i32 0
  call void @SHA256(i8* %30, i64 %31, i8* %32)
  store i64 32, i64* %12, align 8
  br label %39

; <label>:33:                                     ; preds = %26
  %34 = getelementptr inbounds [64 x i8], [64 x i8]* %11, i32 0, i32 0
  %35 = load i8*, i8** %6, align 8
  %36 = load i64, i64* %7, align 8
  %37 = call i8* @__memcpy_chk(i8* %34, i8* %35, i64 %36, i64 64) #5
  %38 = load i64, i64* %7, align 8
  store i64 %38, i64* %12, align 8
  br label %39

; <label>:39:                                     ; preds = %33, %29
  %40 = load i64, i64* %12, align 8
  %41 = trunc i64 %40 to i32
  store i32 %41, i32* %13, align 4
  br label %42

; <label>:42:                                     ; preds = %49, %39
  %43 = load i32, i32* %13, align 4
  %44 = icmp slt i32 %43, 64
  br i1 %44, label %45, label %52

; <label>:45:                                     ; preds = %42
  %46 = load i32, i32* %13, align 4
  %47 = sext i32 %46 to i64
  %48 = getelementptr inbounds [64 x i8], [64 x i8]* %11, i64 0, i64 %47
  store i8 0, i8* %48, align 1
  br label %49

; <label>:49:                                     ; preds = %45
  %50 = load i32, i32* %13, align 4
  %51 = add nsw i32 %50, 1
  store i32 %51, i32* %13, align 4
  br label %42

; <label>:52:                                     ; preds = %42
  store i32 0, i32* %14, align 4
  br label %53

; <label>:53:                                     ; preds = %67, %52
  %54 = load i32, i32* %14, align 4
  %55 = icmp slt i32 %54, 64
  br i1 %55, label %56, label %70

; <label>:56:                                     ; preds = %53
  %57 = load i32, i32* %14, align 4
  %58 = sext i32 %57 to i64
  %59 = getelementptr inbounds [64 x i8], [64 x i8]* %11, i64 0, i64 %58
  %60 = load i8, i8* %59, align 1
  %61 = zext i8 %60 to i32
  %62 = xor i32 54, %61
  %63 = trunc i32 %62 to i8
  %64 = load i32, i32* %14, align 4
  %65 = sext i32 %64 to i64
  %66 = getelementptr inbounds [192 x i8], [192 x i8]* @inner, i64 0, i64 %65
  store i8 %63, i8* %66, align 1
  br label %67

; <label>:67:                                     ; preds = %56
  %68 = load i32, i32* %14, align 4
  %69 = add nsw i32 %68, 1
  store i32 %69, i32* %14, align 4
  br label %53

; <label>:70:                                     ; preds = %53
  %71 = load i8*, i8** %8, align 8
  %72 = load i64, i64* %9, align 8
  %73 = call i8* @__memcpy_chk(i8* getelementptr inbounds ([192 x i8], [192 x i8]* @inner, i64 0, i64 64), i8* %71, i64 %72, i64 128) #5
  store i32 0, i32* %16, align 4
  br label %74

; <label>:74:                                     ; preds = %88, %70
  %75 = load i32, i32* %16, align 4
  %76 = icmp slt i32 %75, 64
  br i1 %76, label %77, label %91

; <label>:77:                                     ; preds = %74
  %78 = load i32, i32* %16, align 4
  %79 = sext i32 %78 to i64
  %80 = getelementptr inbounds [64 x i8], [64 x i8]* %11, i64 0, i64 %79
  %81 = load i8, i8* %80, align 1
  %82 = zext i8 %81 to i32
  %83 = xor i32 92, %82
  %84 = trunc i32 %83 to i8
  %85 = load i32, i32* %16, align 4
  %86 = sext i32 %85 to i64
  %87 = getelementptr inbounds [96 x i8], [96 x i8]* %15, i64 0, i64 %86
  store i8 %84, i8* %87, align 1
  br label %88

; <label>:88:                                     ; preds = %77
  %89 = load i32, i32* %16, align 4
  %90 = add nsw i32 %89, 1
  store i32 %90, i32* %16, align 4
  br label %74

; <label>:91:                                     ; preds = %74
  %92 = load i64, i64* %9, align 8
  %93 = add i64 64, %92
  %94 = getelementptr inbounds [96 x i8], [96 x i8]* %15, i64 0, i64 64
  call void @SHA256(i8* getelementptr inbounds ([192 x i8], [192 x i8]* @inner, i32 0, i32 0), i64 %93, i8* %94)
  %95 = getelementptr inbounds [96 x i8], [96 x i8]* %15, i32 0, i32 0
  %96 = load i8*, i8** %10, align 8
  call void @SHA256(i8* %95, i64 96, i8* %96)
  ret void
}

; Function Attrs: noreturn
declare void @__assert_rtn(i8*, i8*, i32, i8*) #1

declare void @SHA256(i8*, i64, i8*) #2

; Function Attrs: nounwind
declare i8* @__memcpy_chk(i8*, i8*, i64, i64) #3

attributes #0 = { nounwind ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { noreturn "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { noreturn }
attributes #5 = { nounwind }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"PIC Level", i32 2}
!1 = !{!"Apple LLVM version 8.1.0 (clang-802.0.42)"}

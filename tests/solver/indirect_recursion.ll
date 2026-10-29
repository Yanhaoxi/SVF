; The recursive call edge is discovered after the first solve round. Stores to
; %slot must then become weak even though their operand points-to sets are stable.
@before = global i32 1
@after = global i32 2
@dispatch = global ptr @recur

define ptr @leaf(i1 %again) {
entry:
  ret ptr null
}

define ptr @recur(i1 %again) {
entry:
  %slot = alloca ptr
  store ptr @before, ptr %slot
  br i1 %again, label %call, label %exit
call:
  %fp = load ptr, ptr @dispatch
  %ignored = call ptr %fp(i1 false)
  br label %exit
exit:
  store ptr @after, ptr %slot
  %result = load ptr, ptr %slot
  ret ptr %result
}

define i32 @main() {
entry:
  %checked = call ptr @recur(i1 true)
  %value = load i32, ptr %checked
  ret i32 %value
}

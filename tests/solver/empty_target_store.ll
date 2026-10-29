; Andersen sees @array through %slot, but the final flow-sensitive %q is empty.
; The store through %q lies on @array's memory path to %observed.
@before = global i8 0
@after = global i8 0
@array = global [2 x ptr] zeroinitializer

define i32 @main() {
entry:
  %slot = alloca ptr
  store ptr @array, ptr %slot
  store ptr null, ptr %slot
  %q = load ptr, ptr %slot
  store ptr @before, ptr @array
  store ptr @after, ptr %q
  %observed = load ptr, ptr @array
  ret i32 0
}

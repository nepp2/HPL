
# Plan to simplify the interpreter

The basic idea is that the language should self-host as much as possible.

It can be based on a few core primitives:

f64
u64
i64
bool
pointer (64 bit)
object (Rc::<HashMap<refstr, (u64, u128)>>)
function
refstr

pointer needs operations:
  malloc
  free
  deref
  offset

f64, i64, u64 need operations:
  +, -, *, /, %

bool needs operations:
  &&, ||

refstr, f64, i64, u64, bool need operations:
  cast, ==, >, <, >=, <=, !=

function needs operations:
  call

object needs operations:
  get
  set


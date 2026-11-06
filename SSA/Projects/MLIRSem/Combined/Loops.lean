/-
Tests for `scf.for`, parsed with the region-aware elaborator.

Argument order (see `TransformRegions.lean`):
* top-level `^entry(...)`: the LAST argument is variable 0 (as before), so the
  input vectors below list the arguments in reverse;
* nested regions `^bb0(...)`: the FIRST argument is variable 0, matching
  `Scf.Op.regSig`, i.e. `(%i, %iter_args…, %captured…)`.
-/
import SSA.Projects.MLIRSem.Combined.Syntax

namespace MLIRSem
open Builtin LeanMLIR

abbrev i32 : Ty := .shaped .scalar (.int (.int 32))
abbrev i64 : Ty := .shaped .scalar (.int (.int 64))

private def v32 (x : Int) : TyDenote.toType i32 := PoisonOr.value (BitVec.ofInt 32 x)
private def v64 (x : Int) : TyDenote.toType i64 := PoisonOr.value (BitVec.ofInt 64 x)

/-! ### One iter_arg: `init + Σ i` over `[lb, ub)` -/

def sumLoop := [mlirsem_com| {
  ^entry(%lb : i32, %ub : i32, %step : i32, %init : i32):
    %r = "scf.for"(%lb, %ub, %step, %init) ({
      ^bb0(%i : i32, %acc : i32):
        %n = "arith.addi"(%acc, %i) : (i32, i32) -> i32
        "scf.yield"(%n) : (i32) -> ()
    }) : (i32, i32, i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }]

/-- Inputs for `^entry(%lb, %ub, %step, %init)`, in reverse. -/
def sumIn (lb ub step init : Int) : Ctxt.Valuation (Ctxt.ofList [i32, i32, i32, i32]) :=
  Ctxt.Valuation.ofHVector [v32 init, v32 step, v32 ub, v32 lb]ₕ

#eval sumLoop.denote (sumIn 0 4 1 10)    -- expect ok [16]   (10 + 0+1+2+3)
#eval sumLoop.denote (sumIn 0 10 3 0)    -- expect ok [18]   (0+3+6+9)
#eval sumLoop.denote (sumIn 5 5 1 7)     -- expect ok [7]    (zero iterations)
#eval sumLoop.denote (sumIn 0 4 0 0)     -- expect error (UB: step = 0)

/-! ### Two iter_args of different types, plus a captured value

The `i32` accumulator adds the captured `%k` each iteration; the `i64` one
counts iterations. Different types make an argument-order mistake a type error
rather than a silently wrong answer. -/

def twoLoop := [mlirsem_com| {
  ^entry(%lb : i32, %ub : i32, %step : i32, %s0 : i32, %c0 : i64, %one : i64, %k : i32):
    %s, %c = "scf.for"(%lb, %ub, %step, %s0, %c0, %one, %k) ({
      ^bb0(%i : i32, %acc : i32, %cnt : i64, %one_ : i64, %k_ : i32):
        %acc2 = "arith.addi"(%acc, %k_) : (i32, i32) -> i32
        %cnt2 = "arith.addi"(%cnt, %one_) : (i64, i64) -> i64
        "scf.yield"(%acc2, %cnt2) : (i32, i64) -> ()
    }) : (i32, i32, i32, i32, i64, i64, i32) -> (i32, i64)
    "func.return"(%s, %c) : (i32, i64) -> ()
  }]

def twoIn (lb ub step s0 c0 k : Int) :
    Ctxt.Valuation (Ctxt.ofList [i32, i64, i64, i32, i32, i32, i32]) :=
  Ctxt.Valuation.ofHVector [v32 k, v64 1, v64 c0, v32 s0, v32 step, v32 ub, v32 lb]ₕ

#eval twoLoop.denote (twoIn 0 4 1 100 0 5)   -- expect ok [120, 4]

end MLIRSem

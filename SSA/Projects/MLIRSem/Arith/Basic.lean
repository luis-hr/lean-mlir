import SSA.Projects.MLIRSem.Builtin.Types

open LeanMLIR
namespace Arith

structure IntegerOverflowFlags where
  nsw : Bool := false
  nuw : Bool := false
  deriving Repr, DecidableEq, Lean.ToExpr, Inhabited

inductive Op : Type
  | addi (t : Builtin.ShapedInt) (nswnuw : IntegerOverflowFlags := {} )
  | muli (t : Builtin.ShapedInt) (nswnuw : IntegerOverflowFlags := {} )
  | divsi (t : Builtin.ShapedInt) (exact : Bool)
  deriving DecidableEq, Inhabited, Lean.ToExpr, Repr

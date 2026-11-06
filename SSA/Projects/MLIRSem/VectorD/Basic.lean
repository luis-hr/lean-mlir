import LeanMLIR.Framework
import LeanMLIR.Util
import LeanMLIR.Tactic.SimpSet
import LeanMLIR.Basic
import SSA.Projects.MLIRSem.Builtin.Types

namespace VectorD

inductive ReductionKind where
  | add
  | mul
  deriving Repr, DecidableEq, Lean.ToExpr, Inhabited

inductive Op where
  | reduce (length : ℕ) (t : Builtin.Scalar) (acc : Bool) : ReductionKind -> Op
  | extract (length : ℕ) (t : Builtin.Scalar)
  -- | extract (vector_dim : List ℕ) (ind_list : List (Option ℕ))
  deriving DecidableEq, Inhabited, Lean.ToExpr, Repr

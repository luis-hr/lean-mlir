import SSA.Projects.MLIRSem.Builtin.Types

namespace Scf

open Builtin

inductive Op where
  | scf_for (u_cmp : Bool) (i_typ : IntType) (i_args ctx : List Ty)
  deriving DecidableEq, Inhabited, Lean.ToExpr, Repr

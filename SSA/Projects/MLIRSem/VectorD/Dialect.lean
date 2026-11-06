import SSA.Projects.MLIRSem.VectorD.Basic
import SSA.Projects.MLIRSem.VectorD.Semantics
import SSA.Projects.MLIRSem.EffectM
import LeanMLIR

open LeanMLIR
open Builtin

namespace VectorD

@[simp, reducible]
def Op.sig : Op -> List Ty
  | .reduce length t true .add =>
    [.shaped (.vector [length]) t, .shaped .scalar t]
  | .reduce length t false .add =>
    [.shaped (.vector [length]) t ]
  | .reduce length t true .mul =>
    [.shaped (.vector [length]) t, .shaped .scalar t]
  | .reduce length t false .mul =>
    [.shaped (.vector [length]) t]
  | .extract length t => [.shaped (.vector [length]) t, .shaped .scalar (.int .index)]

def Op.outTy : Op -> List Ty
  | .reduce _ t _ _ => [.shaped .scalar t]
  | .extract _ t => [.shaped .scalar t]

def Op.effectKind : Op -> EffectKind
  | .reduce _ _ _ .mul => .pure
  | .reduce _ _ _ .add => .pure
  | .extract _ _  => .pure

def Op.denote [Monad m] [HasUB m] : (o : Op) → HVector toType o.sig → o.effectKind.toMonad m (HVector toType o.outTy)
  | .reduce length (.int _) true .add, args => [reduceAddPoison (args.getN 0) (args.getN 1)]ₕ
  | .reduce length (.int _) false .add, args => [reduceAddPoison (args.getN 0)]ₕ
  | .reduce length (.int _) true .mul, args => [reduceMulPoison (args.getN 0) (args.getN 1)]ₕ
  | .reduce length (.int _) false .mul, args => [reduceMulPoison (args.getN 0)]ₕ
  | .extract length (.int _), args => [extractPoison (args.getN 0) (args.getN 1)]ₕ

abbrev VectorDialect : Dialect where
  Op := Op
  Ty := Ty
  m  := UBM

instance : DialectSignature VectorDialect where
  signature o := ⟨o.sig, [], o.outTy, o.effectKind⟩

instance : DialectDenote VectorDialect where
  denote o args _ := o.denote (m := UBM) args

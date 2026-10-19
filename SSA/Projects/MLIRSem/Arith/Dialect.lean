import SSA.Projects.MLIRSem.Arith.Basic
import SSA.Projects.MLIRSem.Arith.Semantics
import LeanMLIR

namespace Arith
open Builtin
open LeanMLIR


@[simp, reducible]
def Op.sig : Op → List Ty
  | .addi t _ => [t.toTy, t.toTy]
  | .muli t _ => [t.toTy, t.toTy]
  | .divsi t _ => [t.toTy, t.toTy]

def Op.outTy : Op → List Ty
  | .addi t _ => [t.toTy]
  | .muli t _ => [t.toTy]
  | .divsi t _ => [t.toTy]

def Op.effectKind : Op → EffectKind
  | .divsi _ _ => .impure
  | .addi _ _ => .pure
  | .muli _ _ => .pure

def Op.denote [Monad m] [HasUB m]: (o : Op) → HVector toType o.sig → o.effectKind.toMonad m (HVector toType o.outTy)
  | .addi t flags, args => [t.shape.map₂ (addiPoison flags) (args.getN 0) (args.getN 1)]ₕ
  | .muli t flags, args => [t.shape.map₂ (muliPoison flags) (args.getN 0) (args.getN 1)]ₕ
  | .divsi t ex, args =>
    (fun v => [v]ₕ) <$> t.shape.mapM₂ (m := m) (divsiPoison ex) (args.getN 0) (args.getN 1)

abbrev ArithDialect : Dialect where
  Op := Op
  Ty := Ty
  m  := UBM

instance : DialectSignature ArithDialect where
  signature o := ⟨o.sig, [], o.outTy, o.effectKind⟩

instance : DialectDenote ArithDialect where
  denote o args _ := o.denote (m := UBM) args

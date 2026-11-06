/-
The combined dialect: one `Op` type containing the ops of every dialect,
so that a single program (`Com`) can mix them.

It defines no semantics of its own: every function just delegates to the
dialect the op came from. Because all dialects share `Builtin.Ty` and the
same monad, no type or value conversions are needed.
-/
import SSA.Projects.MLIRSem.Arith.Dialect
import SSA.Projects.MLIRSem.VectorD.Dialect
import SSA.Projects.MLIRSem.Scf.Dialect

namespace MLIRSem
open Builtin LeanMLIR

inductive Op
  | arith  (o : Arith.Op)
  | vector (o : VectorD.Op)
  | scf    (o : Scf.Op)
  deriving DecidableEq, Inhabited, Lean.ToExpr, Repr

@[simp, reducible]
def Op.sig : Op → List Ty
  | .arith o  => o.sig
  | .vector o => o.sig
  | .scf o    => o.sig

/-- Only `scf` ops have regions. -/
@[simp, reducible]
def Op.regSig : Op → RegionSignature Ty
  | .arith _  => []
  | .vector _ => []
  | .scf o    => o.regSig

def Op.outTy : Op → List Ty
  | .arith o  => o.outTy
  | .vector o => o.outTy
  | .scf o    => o.outTy

def Op.effectKind : Op → EffectKind
  | .arith o  => o.effectKind
  | .vector o => o.effectKind
  | .scf o    => o.effectKind

/-- `regs` holds the denotations of the op's regions (empty unless the op is `scf`). -/
def Op.denote [Monad m] [HasUB m] :
    (o : Op) → HVector toType o.sig →
    HVector (fun t => t.1.Valuation → m (HVector toType t.2)) o.regSig →
    o.effectKind.toMonad m (HVector toType o.outTy)
  | .arith o,  args, _    => Arith.Op.denote (m := m) o args
  | .vector o, args, _    => VectorD.Op.denote (m := m) o args
  | .scf o,    args, regs => Scf.Op.denote (m := m) o args regs

abbrev MLIRSemDialect : Dialect where
  Op := Op
  Ty := Ty
  m  := UBM

instance : DialectSignature MLIRSemDialect where
  signature o := ⟨o.sig, o.regSig, o.outTy, o.effectKind⟩

instance : DialectDenote MLIRSemDialect where
  denote o args regs := o.denote (m := UBM) args regs

end MLIRSem

import SSA.Projects.MLIRSem.Builtin.Types
import SSA.Projects.MLIRSem.Scf.Basic
import SSA.Projects.MLIRSem.Scf.Semantics
import LeanMLIR

def HVector.split {A : α → Type} : (as : List α) → HVector A (as ++ bs) → HVector A as × HVector A bs
  | [],      xs         => (.nil, xs)
  | _ :: as, .cons x xs => let (l, r) := split as xs; (.cons x l, r)

namespace Scf
open Builtin
open LeanMLIR

/-- The type of the induction variable (and of lb, ub, step). -/
abbrev ivTy (it : IntType) : Ty := .shaped .scalar (.int it)

@[simp, reducible]
def Op.sig : Op → List Ty
  | .scf_for _ it iArgs ctx => [ivTy it, ivTy it, ivTy it] ++ iArgs ++ ctx

@[simp, reducible]
def Op.effectKind : Op → EffectKind
  | .scf_for _ _ _ _ => .impure

@[simp, reducible]
def Op.regSig : Op → RegionSignature Ty
  | .scf_for _ it iArgs ctx => [(⟨ivTy it :: iArgs ++ ctx⟩, iArgs)]

@[simp, reducible]
def Op.outTy : Op → List Ty
  | .scf_for _ _ iArgs _ => iArgs

def Op.denote [Monad m] [HasUB m] : (o : Op) → HVector toType o.sig →
    HVector (fun t => t.1.Valuation → m (HVector toType t.2)) o.regSig →
    o.effectKind.toMonad m (HVector toType o.outTy)
  | .scf_for u it iArgs ctx, args, regs =>
    let (bounds, rest) := args.split [ivTy it, ivTy it, ivTy it]
    let (inits, caps)  := rest.split iArgs
    let body := regs.getN 0
    scfFor (m := m) u it.width (bounds.getN 0) (bounds.getN 1) (bounds.getN 2)
      (fun i acc => body (Ctxt.Valuation.ofHVector ((i : toType (ivTy it)) ::ₕ acc.append caps)))
      inits

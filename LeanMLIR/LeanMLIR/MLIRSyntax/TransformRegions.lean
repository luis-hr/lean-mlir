/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.MLIRSyntax.Transform
import LeanMLIR.MLIRSyntax.Transform.Utils
import LeanMLIR.MLIRSyntax.EDSL2

/-!
# Region-aware parsing

`mkCom` (Transform.lean) and `mkExprOf` (Transform/Utils.lean) ignore the regions
of an operation (`mkExprOf` even panics on ops whose signature has regions).

This file adds a *parallel*, region-aware pipeline. Nothing existing is changed,
so the dialects that use the old elaborators (including the kernel-reducing
`elabIntoCom` from EDSL.lean, which needs `mkCom` to stay non-`partial`) are
unaffected.

* `TransformExprWithRegions`: like `TransformExpr`, but `mkExprWithRegions` also
  receives the operation's regions, already parsed into `Com`s.
* `mkComR`: like `mkCom`, but recursively parses the regions of every operation.
* `Op.mkExprOfWithRegions`: like `mkExprOf`, but attaches the parsed regions,
  checking them against the operation's region signature.
* `SSA.elabIntoComR`: like `SSA.elabIntoCom'`, but uses `mkComR`.

## Argument order of nested regions

For a *nested* region, the context lists the block arguments in **source order**:
for `^bb0(%a : ta, %b : tb)` the context is `⟨[ta, tb]⟩`, and `%a` is variable 0.
This matches `Ctxt.Valuation.ofHVector`, which also maps the first element to
variable 0, so an op's denotation can build the region's valuation directly.

The *top-level* region keeps `mkCom`'s convention (the *last* argument is
variable 0), so existing programs and tests keep their meaning.
-/

namespace MLIR.AST
open Ctxt

/-- A parsed region: its argument context, the types it yields, and its body. -/
abbrev ParsedRegion (d : Dialect) [DialectSignature d] :=
  Σ (Γ : Ctxt d.Ty) (ty : List d.Ty), Com d Γ .impure ty

/-- Like `TransformExpr`, but `mkExprWithRegions` also gets the operation's
regions, already parsed (in the order they appear in the source). -/
class TransformExprWithRegions (d : Dialect) (φ : outParam Nat) [DialectSignature d]
    [TransformTy d φ] where
  mkExprWithRegions : (Γ : Ctxt d.Ty) → (opStx : AST.Op φ) → (regions : List (ParsedRegion d)) →
    ReaderM d (Σ eff ty, Expr d Γ eff ty)

/-! `partial` definitions need their result types to be inhabited. -/
instance : Inhabited (Except TransformError α) := ⟨.error <| .generic ""⟩
instance : Inhabited (StateT NameMapping (Except TransformError) α) :=
  ⟨fun _ => .error <| .generic ""⟩

variable {d : Dialect} {φ : Nat} [DialectSignature d] [DecidableEq d.Ty] [ToString d.Ty]

/-- Declare the given block arguments, in order.
(A copy of the private `declareBindings` from Transform.lean.)
The binder for the *last* element of `vals` ends up as variable 0. -/
private def declareArgs [TransformTy d φ] (Γ : Ctxt d.Ty) (vals : List (TypedSSAVal φ)) :
    BuilderM d (DerivedCtxt Γ) := do
  vals.foldlM (fun Γ' ssaVal => do
    let ⟨Γ'', _⟩ ← TypedSSAVal.newVal Γ'.ctxt ssaVal
    return Γ''
  ) (.ofCtxt Γ)

/-- Check a list of parsed regions against a region signature, and collect them
into the `HVector` that `Expr.mk` expects. -/
def regionsWithSignature : (sig : RegionSignature d.Ty) → List (ParsedRegion d) →
    Except TransformError
      (HVector (fun t : Ctxt d.Ty × List d.Ty => Com d t.1 .impure t.2) sig)
  | [], [] => pure .nil
  | (Γ, ty) :: sig, ⟨Γ', ty', com⟩ :: regs =>
    if h : Γ' = Γ ∧ ty' = ty then
      (fun rest => .cons (cast (by obtain ⟨rfl, rfl⟩ := h; rfl) com) rest)
        <$> regionsWithSignature sig regs
    else
      throw <| .generic s!"Region type mismatch: the region has arguments {Γ'.toList} \
        and yields {ty'}, but the operation expects arguments {Γ.toList} and yields {ty}"
  | sig, regs =>
    throw <| .generic s!"Expected {sig.length} region(s), but found {regs.length}"

variable [TransformTy d φ] [TransformExprWithRegions d φ] [TransformReturn d φ]

mutual

/-- Like `mkComHelper` (Transform.lean), but first parses the regions of each
operation and passes them to `mkExprWithRegions`. -/
partial def mkComRHelper (Γ : Ctxt d.Ty) : List (Op φ) → BuilderM d (Σ eff ty, Com d Γ eff ty)
  | [retStx] => do
      TransformReturn.mkReturn Γ retStx
  | opStx :: rest => do
    let regions ← (opStx.regions.mapM mkRegion : ExceptM d _)
    let ⟨_eff₁, ty₁, expr⟩ ← TransformExprWithRegions.mkExprWithRegions Γ opStx regions
    let numExpectedReturns := ty₁.length
    if opStx.res.length != numExpectedReturns then
      throw <| .generic
        s!"Expected {numExpectedReturns} return variables, but found {opStx.res.length}"
    else
      -- The op's results form `ty₁ ++ Γ`, so the FIRST result is variable 0.
      -- Each `addValToMapping` puts a name at index 0, so declare the results in
      -- reverse. (`mkComHelper` in Transform.lean declares them in order, which
      -- swaps the names of a multi-result op.)
      let _ ← (opStx.res.zip ty₁).reverse.foldlM (init:=Γ) fun Γ ⟨var, ty⟩ => do
        let ⟨Γ', _⟩ ← addValToMapping Γ (SSAValToString var.1) ty
        return Γ'
      let ⟨_eff₂, ty₂, body⟩ ← mkComRHelper (ty₁ ++ Γ) rest
      return ⟨_, ty₂, Com.letSup expr body⟩
  | [] => throw <| .generic "Ill-formed (empty) block"

/-- Parse a nested region. Regions are isolated from above, so parsing starts
from an empty name mapping. Block arguments are declared in reverse, so that the
*first* block argument is variable 0 (see the module docstring). The body is
cast to `.impure`, since that is what `Expr.mk` expects of regions. -/
partial def mkRegion (reg : Region φ) : ExceptM d (ParsedRegion d) :=
  match reg.ops with
  | [] => throw <| .generic "Ill-formed region (empty)"
  | ops => BuilderM.runWithEmptyMapping <| do
    let Γ ← declareArgs ∅ reg.args.reverse
    let ⟨eff, ty, com⟩ ← mkComRHelper Γ.ctxt ops
    return ⟨Γ.ctxt, ty, com.changeEffect (EffectKind.le_impure eff)⟩

end

/-- Like `mkCom`, but the regions of operations are parsed too. -/
def mkComR (reg : Region φ) :
    ExceptM d (Σ (Γ : Ctxt d.Ty) (eff : EffectKind) (ty : _), Com d Γ eff ty) :=
  match reg.ops with
  | [] => throw <| .generic "Ill-formed region (empty)"
  | ops => BuilderM.runWithEmptyMapping <| do
    let Γ ← declareArgs ∅ reg.args
    let com ← mkComRHelper Γ.ctxt ops
    return ⟨Γ.ctxt, com⟩

namespace Op

/-- Like `mkExprOf`, but also attaches the given (parsed) regions, checking them
against the region signature of `parsedOp`. -/
def mkExprOfWithRegions (opStx : Op φ) (Γ : Ctxt d.Ty) (parsedOp : d.Op)
    (regions : List (ParsedRegion d)) : ReaderM d (Σ eff ty, Expr d Γ eff ty) := do
  let args ← opStx.parseArgs Γ
  let signature := DialectSignature.signature parsedOp
  let regArgs ← (regionsWithSignature signature.regSig regions : ExceptM d _)
  return ⟨signature.effectKind, signature.returnTypes, ⟨
    parsedOp,
    rfl,
    EffectKind.le_refl _,
    ← args.withSignature _,
    regArgs
  ⟩⟩

end Op
end MLIR.AST

namespace SSA
open Qq Lean Meta Elab Term
open MLIR.AST

/-- Like `elabIntoCom'`, but nested regions are parsed (via `mkComR`). Use it as
```
elab "[foo_com| " reg:mlir_region "]" : term => SSA.elabIntoComR reg FooDialect
```
-/
def elabIntoComR (region : TSyntax `mlir_region) (d : Dialect) {φ : Nat}
    [ToExpr d.Op] [ToExpr d.Ty] [DialectToExpr d]
    [DialectSignature d] [DecidableEq d.Ty] [ToString d.Ty] [Repr d.Ty]
    [TransformTy d φ] [TransformExprWithRegions d φ] [TransformReturn d φ] :
    TermElabM Lean.Expr := withRef region <| do
  let ast : Region φ ← do
    let stx  ← `([mlir_region| $region])
    let expr ← elabTermEnsuringTypeQ stx q(Region $φ)
    synthesizeSyntheticMVarsNoPostponing
    let expr ← instantiateMVars expr
    evalExprOfTypeRegion φ expr
  let ⟨_Γ, _eff, _ty, com⟩ ← match mkComR (d := d) ast with
    | .error (e : TransformError) => throwError (repr e)
    | .ok res => pure res
  com.toExprM

end SSA

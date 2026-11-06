/-
Printing and parsing for the `scf` dialect.

`scf.for` has a region, so it is parsed through the region-aware pipeline in
`LeanMLIR/MLIRSyntax/TransformRegions.lean`: this file only decides *which* op a
piece of syntax is; the combined dialect's `TransformExprWithRegions` instance
attaches the parsed region.
-/
import SSA.Projects.MLIRSem.Scf.Dialect
import SSA.Projects.MLIRSem.Builtin.Syntax
import LeanMLIR

namespace Scf
open Builtin LeanMLIR MLIR.AST

def opName : Op → String
  | .scf_for .. => "scf.for"

def printAttributes : Op → String
  | .scf_for u .. => if u then "<{unsignedCmp}>" else ""

/-- Decide which `scf.for` a generic-form op is:
```
%r… = "scf.for"(%lb, %ub, %step, %init…, %cap…) ({
  ^bb0(%i : iN, %acc…, %cap…):
    …
    "scf.yield"(%next…) : (…) -> ()
}) : (iN, iN, iN, …) -> …
```
* the bound type comes from the first operand;
* the iter_args types are the result types;
* operands after the bounds and the initial values are captured values. This is
  our extension: MLIR lets the body use outer values directly, but LeanMLIR
  regions are isolated, so they are passed explicitly (and must also be the
  last block arguments).

The region itself is checked against `Op.regSig` by the framework. -/
def parseFor (opStx : MLIR.AST.Op 0) : Except TransformError Op := do
  let argTys ← opStx.argTypes.mapM Builtin.mkTy
  let resTys ← opStx.resTypes.mapM Builtin.mkTy
  let .shaped .scalar (.int it) :: _ := argTys
    | throw <| .generic "scf.for: the bounds must be scalar integers"
  if argTys.length < 3 + resTys.length then
    throw <| .generic "scf.for: expected lb, ub, step and one initial value per result"
  let ctx := argTys.drop (3 + resTys.length)
  return .scf_for (opStx.hasAttr "unsignedCmp") it resTys ctx

end Scf

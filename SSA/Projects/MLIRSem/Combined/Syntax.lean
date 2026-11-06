import SSA.Projects.MLIRSem.Combined.Dialect
import SSA.Projects.MLIRSem.Arith.Syntax
import SSA.Projects.MLIRSem.VectorD.Syntax
import SSA.Projects.MLIRSem.Scf.Syntax
import LeanMLIR
import LeanMLIR.MLIRSyntax.TransformRegions

namespace MLIRSem
open Builtin LeanMLIR MLIR.AST

/-! ## Printing -/

def opName : Op → String
  | .arith o  => Arith.opName o
  | .vector o => VectorD.opName o
  | .scf o    => Scf.opName o

def printAttributes : Op → String
  | .arith o  => Arith.printAttributes o
  | .vector o => VectorD.printAttributes o
  | .scf o    => Scf.printAttributes o

instance : DialectPrint MLIRSemDialect where
  printOpName     := opName
  printTy         := toString
  printAttributes := printAttributes
  dialectName     := "mlirsem"
  printReturn _   := "func.return"
  printFunc _     := "func.func @f"

/-! ## Lean-term generation (needed by `[mlirsem_com| …]`) -/

instance : DialectToExpr MLIRSemDialect where
  toExprM       := .const ``UBM []
  toExprDialect := .const ``MLIRSem.MLIRSemDialect []

/-! ## Parsing -/

def parseOp (opStx : MLIR.AST.Op 0) (argTys : List Ty) : Except TransformError Op :=
  if opStx.name.startsWith "arith." then
    Op.arith <$> Arith.parseOp opStx argTys
  else if opStx.name.startsWith "vector." then
    Op.vector <$> VectorD.parseOp opStx argTys
  else
    throw <| .unsupportedOp opStx.name

instance : DialectParse MLIRSemDialect 0 where
  mkTy := Builtin.mkTy

  -- `scf.yield` ends a loop body; it becomes the region's `Com.rets`.
  isValidReturn _Γ opStx := return opStx.name == "return" || opStx.name == "func.return"
    || opStx.name == "scf.yield"

  mkExpr Γ opStx := do
    let args ← opStx.parseArgs Γ
    let op ← parseOp opStx args.types
    opStx.mkExprOf Γ op (some args)

/-- Ops with regions (`scf.for`) are built here, with their parsed regions;
every other op goes through `DialectParse.mkExpr` above. -/
instance : TransformExprWithRegions MLIRSemDialect 0 where
  mkExprWithRegions Γ opStx regions := do
    if opStx.name == "scf.for" then
      let op ← (Scf.parseFor opStx : Except TransformError _)
      opStx.mkExprOfWithRegions Γ (Op.scf op) regions
    else if regions.isEmpty then
      TransformExpr.mkExpr Γ opStx
    else
      throw <| .generic s!"`{opStx.name}` does not take regions"

-- Uses the region-aware elaborator, so programs may contain `scf.for`.
open Qq Lean Elab Term Meta in
elab "[mlirsem_com| " reg:mlir_region "]" : term => SSA.elabIntoComR reg MLIRSemDialect

end MLIRSem

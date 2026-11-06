/-
Parser for the `arith` dialect: turns generic-form MLIR into `Com ArithDialect …`.

Usage:
  [arith_com| {
  ^bb0(%a : i32, %b : i32):
    %0 = "arith.addi"(%a, %b) <{overflowFlags = #arith.overflow<nsw>}> : (i32, i32) -> i32
    "func.return"(%0) : (i32) -> ()
  }]

Types are parsed by `Builtin.mkTy` (see `Builtin/Syntax.lean`): `iN`, and vectors
written as strings, `!"vector<4xi32>"`.
-/
import SSA.Projects.MLIRSem.Arith.Dialect
import SSA.Projects.MLIRSem.Builtin.Syntax
import LeanMLIR

namespace Arith
open Builtin LeanMLIR MLIR.AST

/-! ## Printing -/

def opName : Op → String
  | .addi _ _  => "arith.addi"
  | .muli _ _  => "arith.muli"
  | .divsi _ _ => "arith.divsi"
  | .constant _ _ => "arith.constant"

def flagsToString (f : IntegerOverflowFlags) : String :=
  match f.nsw, f.nuw with
  | false, false => ""
  | true,  false => "<{overflowFlags = #arith.overflow<nsw>}>"
  | false, true  => "<{overflowFlags = #arith.overflow<nuw>}>"
  | true,  true  => "<{overflowFlags = #arith.overflow<nsw, nuw>}>"

def printAttributes : Op → String
  | .addi _ f | .muli _ f => flagsToString f
  | .divsi _ true  => "<{isExact}>"
  | .divsi _ false => ""
  | .constant t v  => s!"<\{value = {v} : {toString (Ty.shaped .scalar (.int t))}}>"

instance : DialectPrint ArithDialect where
  printOpName     := opName
  printTy         := toString
  printAttributes := printAttributes
  dialectName     := "arith"
  printReturn _   := "func.return"
  printFunc _     := "func.func @f"

/-! ## Lean-term generation (needed by `[arith_com| …]`) -/

instance : DialectToExpr ArithDialect where
  toExprM       := .const ``UBM []
  toExprDialect := .const ``Arith.ArithDialect []

/-! ## Parsing -/

/-- `<{overflowFlags = #arith.overflow<…>}>`; absent means no flags. -/
def parseFlags (opStx : MLIR.AST.Op 0) : Except TransformError IntegerOverflowFlags :=
  match opStx.getAttr? "overflowFlags" with
  | none                                    => return {}
  | some (.opaque_ "arith.overflow" "none") => return {}
  | some (.opaque_ "arith.overflow" "nsw")  => return ⟨true, false⟩
  | some (.opaque_ "arith.overflow" "nuw")  => return ⟨false, true⟩
  | some (.list [.opaque_ "arith.overflow" "nsw", .opaque_ "arith.overflow" "nuw"])
  | some (.list [.opaque_ "arith.overflow" "nuw", .opaque_ "arith.overflow" "nsw"]) =>
      return ⟨true, true⟩
  | some _ => throw <| .generic s!"unsupported overflowFlags on {opStx.name}"

/-- `exact` is a unit attribute; accept both spellings. -/
def parseExact (opStx : MLIR.AST.Op 0) : Bool :=
  (opStx.getAttr? "isExact").isSome || (opStx.getAttr? "exact").isSome

/-- Syntax → `Op`, given the operand types. Independent of any particular dialect,
    so a combined dialect can reuse it. -/
def parseOp (opStx : MLIR.AST.Op 0) (argTys : List Ty) : Except TransformError Op := do
  -- `arith.constant` has no operands: its type comes from the `value` attribute,
  -- e.g. `<{value = 42 : i32}>` (an untyped `42` defaults to i64).
  if opStx.name == "arith.constant" then
    let (v, ty) ← opStx.getIntAttr "value"
    let .shaped .scalar (.int it) ← Builtin.mkTy ty
      | throw <| .generic "arith.constant: only scalar integer constants are supported"
    return Op.constant it v
  let ty :: _ := argTys
    | throw <| .generic s!"{opStx.name}: expected operands"
  let some t := ty.toShapedInt?
    | throw <| .generic s!"{opStx.name}: expected an integer-like operand"
  match opStx.name with
  | "arith.addi"  => return Op.addi t (← parseFlags opStx)
  | "arith.muli"  => return Op.muli t (← parseFlags opStx)
  | "arith.divsi" => return Op.divsi t (parseExact opStx)
  | name          => throw <| .unsupportedOp name

instance : DialectParse ArithDialect 0 where
  mkTy := Builtin.mkTy

  isValidReturn _Γ opStx := return opStx.name == "return" || opStx.name == "func.return"

  mkExpr Γ opStx := do
    let args ← opStx.parseArgs Γ
    let op ← parseOp opStx args.types
    opStx.mkExprOf Γ op (some args)

open Qq Lean Elab Term Meta in
elab "[arith_com| " reg:mlir_region "]" : term => SSA.elabIntoCom' reg ArithDialect

/-! ## Tests -/

abbrev i32 : Ty := .shaped .scalar (.int (.int 32))

/-- `a / b` without and with `exact`. -/
def exactTest : Com ArithDialect (Ctxt.ofList [i32, i32]) .impure [i32, i32] :=
  [arith_com| {
  ^bb0(%a : i32, %b : i32):
    %0 = "arith.divsi"(%a, %b) : (i32, i32) -> i32
    %1 = "arith.divsi"(%a, %b) <{isExact}> : (i32, i32) -> i32
    "func.return"(%0, %1) : (i32, i32) -> ()
  }]

#eval exactTest            -- prints the program back

/-- Valuation for `^bb0(%a, %b)`. The parser adds block arguments to the *front*
    of the context one by one, so the LAST argument (`%b`) is variable 0:
    `Ctxt.ofList [ty_b, ty_a]`. Hence `b` comes first in the vector. -/
def inputs (a b : BitVec 32) : Ctxt.Valuation (Ctxt.ofList [i32, i32]) :=
  Ctxt.Valuation.ofHVector
    (.cons (show TyDenote.toType i32 from PoisonOr.value b)
    (.cons (show TyDenote.toType i32 from PoisonOr.value a) .nil))

#eval exactTest.denote (inputs 7 2)   -- expect ok [3, poison]   (7/2 is inexact)
#eval exactTest.denote (inputs 8 2)   -- expect ok [4, 4]
#eval exactTest.denote (inputs 7 0)   -- expect error (UB)

/-! ### Vector test -/

abbrev v4i32 : Ty := .shaped (.vector [4]) (.int (.int 32))

def vecTest : Com ArithDialect (Ctxt.ofList [v4i32, v4i32]) .impure [v4i32] :=
  [arith_com| {
  ^bb0(%a : !"vector<4xi32>", %b : !"vector<4xi32>"):
    %0 = "arith.divsi"(%a, %b) : (!"vector<4xi32>", !"vector<4xi32>") -> !"vector<4xi32>"
    "func.return"(%0) : (!"vector<4xi32>") -> ()
  }]

/-- Lane `i` of `%a` is `a i`, of `%b` is `b i` (again `%b` is variable 0). -/
def vinputs (a b : Nat → Nat) : Ctxt.Valuation (Ctxt.ofList [v4i32, v4i32]) :=
  Ctxt.Valuation.ofHVector
    (.cons (show TyDenote.toType v4i32 from fun i => PoisonOr.value (BitVec.ofNat 32 (b i.val)))
    (.cons (show TyDenote.toType v4i32 from fun i => PoisonOr.value (BitVec.ofNat 32 (a i.val))) .nil))

-- [10,20,30,40] / [3,4,5,6]  → expect ok [3, 5, 6, 6]
#eval vecTest.denote (vinputs (fun i => 10 * (i + 1)) (fun i => i + 3))
-- [10,20,30,40] / [3,2,1,0]  → expect error (UB): lane 3 divides by zero
#eval vecTest.denote (vinputs (fun i => 10 * (i + 1)) (fun i => 3 - i))

end Arith

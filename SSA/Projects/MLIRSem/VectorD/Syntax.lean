/-
Parser for the `vector` dialect (`vector.reduction`, `vector.extract`).

Generic form, as printed by `mlir-opt --mlir-print-op-generic`:
  %0 = "vector.reduction"(%v)       <{kind = #vector.kind<add>}> : (vector<4xi32>) -> i32
  %1 = "vector.reduction"(%v, %acc) <{kind = #vector.kind<mul>}> : (vector<4xi32>, i32) -> i32
  %2 = "vector.extract"(%v, %i) : (vector<4xi32>, index) -> i32

`vector.extract`: only a single *dynamic* position into a 1-D vector is supported.
MLIR's generic form also carries `<{static_position = array<i64: -9223372036854775808>}>`
(that number marks "the position is an operand"); LeanMLIR's attribute parser has no
`array<…>` syntax, so leave the attribute out. Static positions (`%v[2]`) are not
supported: pass the position as an `index` operand instead.

Vector types must be written as strings, `!"vector<4xi32>"` (see `Builtin/Syntax.lean`).
Other attributes (e.g. `fastmath`) are ignored.
-/
import SSA.Projects.MLIRSem.VectorD.Dialect
import SSA.Projects.MLIRSem.Builtin.Syntax
import LeanMLIR

namespace VectorD
open Builtin LeanMLIR MLIR.AST

/-! ## Printing -/

def ReductionKind.name : ReductionKind → String
  | .add => "add"
  | .mul => "mul"

def opName : Op → String
  | .reduce .. => "vector.reduction"
  | .extract .. => "vector.extract"

def printAttributes : Op → String
  | .reduce _ _ _ k => s!"<\{kind = #vector.kind<{k.name}>}>"
  | .extract .. => ""

instance : DialectPrint VectorDialect where
  printOpName     := opName
  printTy         := toString
  printAttributes := printAttributes
  dialectName     := "vector"
  printReturn _   := "func.return"
  printFunc _     := "func.func @f"

/-! ## Lean-term generation (needed by `[vector_com| …]`) -/

instance : DialectToExpr VectorDialect where
  toExprM       := .const ``UBM []
  toExprDialect := .const ``VectorD.VectorDialect []

/-! ## Parsing -/

/-- `kind = #vector.kind<…>` (required). -/
def parseKind (opStx : MLIR.AST.Op 0) : Except TransformError ReductionKind :=
  match opStx.getAttr? "kind" with
  | some (.opaque_ "vector.kind" "add") => return .add
  | some (.opaque_ "vector.kind" "mul") => return .mul
  | some _ => throw <| .generic s!"{opStx.name}: unsupported reduction kind"
  | none   => throw <| .generic s!"{opStx.name}: missing `kind` attribute"

/-- Syntax → `Op`, given the operand types. Independent of any particular dialect,
    so a combined dialect can reuse it. -/
def parseOp (opStx : MLIR.AST.Op 0) (argTys : List Ty) : Except TransformError Op :=
  match opStx.name with
  | "vector.reduction" => do
    let .shaped (.vector [n]) s :: rest := argTys
      | throw <| .generic "vector.reduction: expected a 1-D vector as first operand"
    let kind ← parseKind opStx
    return .reduce n s (!rest.isEmpty) kind      -- a 2nd operand is the accumulator
  | "vector.extract" => do
    let [.shaped (.vector [n]) s, .shaped .scalar (.int .index)] := argTys
      | throw <| .generic "vector.extract: expected a 1-D vector and one `index` position"
    return .extract n s
  | name => throw <| .unsupportedOp name

instance : DialectParse VectorDialect 0 where
  mkTy := Builtin.mkTy

  isValidReturn _Γ opStx := return opStx.name == "return" || opStx.name == "func.return"

  mkExpr Γ opStx := do
    let args ← opStx.parseArgs Γ
    let op ← parseOp opStx args.types
    opStx.mkExprOf Γ op (some args)

open Qq Lean Elab Term Meta in
elab "[vector_com| " reg:mlir_region "]" : term => SSA.elabIntoCom' reg VectorDialect

/-! ## Tests -/

abbrev i32   : Ty := .shaped .scalar (.int (.int 32))
abbrev v4i32 : Ty := .shaped (.vector [4]) (.int (.int 32))

/-- Block arguments `(%v, %acc)` become the context `[acc, v]` (last argument first). -/
def redTest : Com VectorDialect (Ctxt.ofList [i32, v4i32]) .pure [i32, i32] :=
  [vector_com| {
  ^bb0(%v : !"vector<4xi32>", %acc : i32):
    %0 = "vector.reduction"(%v) <{kind = #vector.kind<add>}> : (!"vector<4xi32>") -> i32
    %1 = "vector.reduction"(%v, %acc) <{kind = #vector.kind<mul>}> : (!"vector<4xi32>", i32) -> i32
    "func.return"(%0, %1) : (i32, i32) -> ()
  }]

#eval redTest                         -- prints the program back

/-- `%v = [v 0, v 1, v 2, v 3]`, `%acc = acc`. -/
def redInputs (v : Nat → Nat) (acc : Nat) : Ctxt.Valuation (Ctxt.ofList [i32, v4i32]) :=
  Ctxt.Valuation.ofHVector
    (.cons (show TyDenote.toType i32 from PoisonOr.value (BitVec.ofNat 32 acc))
    (.cons (show TyDenote.toType v4i32 from fun i => PoisonOr.value (BitVec.ofNat 32 (v i.val))) .nil))

-- [1,2,3,4]: add → 10;  mul with acc 10 → 10 * 24 = 240
#eval redTest.denote (redInputs (· + 1) 10)

abbrev index : Ty := .shaped .scalar (.int .index)

/-- Block arguments `(%v, %i)` become the context `[index, v4i32]` (last argument first). -/
def extTest : Com VectorDialect (Ctxt.ofList [index, v4i32]) .pure [i32] :=
  [vector_com| {
  ^bb0(%v : !"vector<4xi32>", %i : index):
    %0 = "vector.extract"(%v, %i) : (!"vector<4xi32>", index) -> i32
    "func.return"(%0) : (i32) -> ()
  }]

#eval extTest                         -- prints the program back

/-- `%v = [v 0, v 1, v 2, v 3]`, `%i = i` (`none` = poison). -/
def extInputs (v : Nat → Nat) (i : Option Nat) : Ctxt.Valuation (Ctxt.ofList [index, v4i32]) :=
  Ctxt.Valuation.ofHVector
    (.cons (show TyDenote.toType index from
              match i with
              | some i => PoisonOr.value (BitVec.ofNat 64 i)
              | none   => PoisonOr.poison)
    (.cons (show TyDenote.toType v4i32 from fun j => PoisonOr.value (BitVec.ofNat 32 (v j.val))) .nil))

-- v = [10, 20, 30, 40]
#eval extTest.denote (extInputs (10 * · + 10) (some 2))   -- expect [30]
#eval extTest.denote (extInputs (10 * · + 10) (some 4))   -- expect [poison]  (out of bounds)
#eval extTest.denote (extInputs (10 * · + 10) none)       -- expect [poison]  (poison index)

end VectorD

/-
Parsing and printing of the builtin types, shared by every dialect in this project.
Each dialect's `DialectParse` instance uses `mkTy := Builtin.mkTy`.
-/
import SSA.Projects.MLIRSem.Builtin.Types
import SSA.Projects.MLIRSem.Builtin.Semantics
import LeanMLIR

namespace Builtin
open LeanMLIR MLIR.AST

/-! ## Printing -/

instance : ToString Ty where
  toString
    | .shaped .scalar (.int (.int w)) => s!"i{w}"
    | .shaped .scalar (.int .index) => "index"
    | .shaped (.vector ds) (.int (.int w)) =>
        s!"vector<{"x".intercalate (ds.map toString)}xi{w}>"
    | .shaped (.vector ds) (.int .index) =>
        s!"vector<{"x".intercalate (ds.map toString)}xindex>"

/-! ## Helpers -/

/-- The integer-like type an op works on, read from its first operand. -/
def Ty.toShapedInt? : Ty → Option ShapedInt
  | .shaped s (.int it) => some ⟨s, it⟩

/-! ### Vector types

The generic parser has no working `vector<…>` type syntax (its `vector` macro in
`GenericParser.lean` expands to an undefined `builtin.vector`, and MLIR's `4x8xi32`
does not tokenize well in Lean). As a stopgap, write vector types as strings:
`!"vector<4xi32>"`. The parser hands these to `mkTy` as `MLIRType.undefined s`. -/

/-- Split `["4", "8", "i32"]` into the leading numeric dims and the rest. -/
def splitDims : List String → List Nat × List String
  | p :: ps => match p.toNat? with
    | some n => let (ds, rest) := splitDims ps; (n :: ds, rest)
    | none   => ([], p :: ps)
  | [] => ([], [])

/-- Decode `"vector<4x8xi32>"` into dims `[4, 8]` and element width `32`. -/
def parseVectorStr (s : String) : Option (List Nat × Nat) := do
  guard (s.startsWith "vector<" && s.endsWith ">")
  let body := ((s.drop 7).dropEnd 1).toString
  let (dims, rest) := splitDims (body.splitOn "x")
  let elem := "x".intercalate rest
  guard (elem.startsWith "i")
  let w ← (elem.drop 1).toString.toNat?
  return (dims, w)

/-! ## Parsing -/

/-- Parse a generic-syntax MLIR type into a builtin `Ty`.
    Supports `iN` and (as strings) `!"vector<…xiN>"`. -/
def mkTy : MLIRType φ → Except TransformError Ty
  | .int .Signless (.concrete w) => return .shaped .scalar (.int (.int w))
  | .index => return .shaped .scalar (.int .index)
  | .undefined s => match parseVectorStr s with
    | some (dims, w) => return .shaped (.vector dims) (.int (.int w))
    | none => throw .unsupportedType
  | _ => throw .unsupportedType

/-! ## Showing values (for `#eval`), shared by all dialects -/

instance : ∀ t : Ty, Repr (TyDenote.toType t)
  | .shaped .scalar (.int _) =>
      ⟨fun x _ => toString (show PoisonOr (BitVec _) from x)⟩
  | .shaped (.vector _) (.int _) =>
      ⟨fun x _ => toString ((List.finRange _).map fun i => toString (show PoisonOr (BitVec _) from x i))⟩

end Builtin

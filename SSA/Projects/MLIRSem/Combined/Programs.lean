import SSA.Projects.MLIRSem.Combined.Syntax
import SSA.Projects.MLIRSem.Combined.theorems

namespace MLIRSem
open Builtin LeanMLIR

abbrev i32   : Ty := .shaped .scalar (.int (.int 32))
abbrev v4i32 : Ty := .shaped (.vector [4]) (.int (.int 32))

-- %0 = muli %a, %b : vector<4xi32>
-- %1 = vector.reduction1 <add>, %0 :
-- vector<4xi32> into i32
def prog₁ : Com MLIRSemDialect (Ctxt.ofList [v4i32, v4i32]) .pure [i32] :=
  [mlirsem_com| {
  ^bb0(%a : !"vector<4xi32>", %b : !"vector<4xi32>"):
    %0 = "arith.muli"(%a, %b) : (!"vector<4xi32>", !"vector<4xi32>") -> !"vector<4xi32>"
    %1 = "vector.reduction"(%0) <{kind = #vector.kind<add>}> : (!"vector<4xi32>") -> i32
    "func.return"(%1) : (i32) -> ()
  }]

-- %0 = muli %b, %a : vector<4xi32>
-- %1 = vector.reduction1 <add>, %0 :
-- vector<4xi32> into i32
def prog₂ : Com MLIRSemDialect (Ctxt.ofList [v4i32, v4i32]) .pure [i32] :=
  [mlirsem_com| {
  ^bb0(%a : !"vector<4xi32>", %b : !"vector<4xi32>"):
    %0 = "arith.muli"(%b, %a) : (!"vector<4xi32>", !"vector<4xi32>") -> !"vector<4xi32>"
    %1 = "vector.reduction"(%0) <{kind = #vector.kind<add>}> : (!"vector<4xi32>") -> i32
    "func.return"(%1) : (i32) -> ()
  }]


theorem prog₁_eq_prog₂ : prog₁.denote = prog₂.denote := by
  rw [prog₁, prog₂]
  simp_peephole
  intro a b
  simp only [Op.denote, Arith.Op.denote, VectorD.Op.denote,
    Shape.map₂, HVector.getN, HVector.get,
    Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil,
    Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append]
  show reduceAddPoison (fun i => Arith.muliPoison {} (a i) (b i))
     = reduceAddPoison (fun i => Arith.muliPoison {} (b i) (a i))
  congr 1
  funext i
  exact Arith.muliPoison_comm _ _ _

/-- The parsed program denotes `prog`. -/
theorem prog₁_eq_prog₂' : prog₁.denote = prog₂.denote := by
  rw [prog₁, prog₂]
  simp_peephole
  intro a b
  show (prog 4 32 a b).getN 0 = (prog 4 32 b a).getN 0
  rw [prog_comm]

end MLIRSem

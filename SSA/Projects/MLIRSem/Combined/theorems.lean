import SSA.Projects.MLIRSem.Combined.Dialect
import SSA.Projects.MLIRSem.Arith.theorems
import SSA.Projects.MLIRSem.VectorD.theorems

namespace MLIRSem
open Builtin

def prog (n w : Nat) (x y : Fin [n].prod → IntW w) :
    HVector toType [Ty.shaped .scalar (.int (.int w))] :=
  let t : ShapedInt := ⟨.vector [n], .int w⟩
  let r0 : HVector toType [t.toTy] :=
    Op.denote (m := UBM) (.arith (.muli t {})) [x, y]ₕ .nil
  Op.denote (m := UBM) (.vector (.reduce n (.int (.int w)) false .add)) [r0.getN 0]ₕ .nil

/-- Swapping the `muli` operands does not change the result. -/
theorem prog_comm (n w : Nat) (x y : Fin [n].prod → IntW w) :
    prog n w x y = prog n w y x := by
  unfold prog
  simp only [Op.denote, Arith.Op.denote, VectorD.Op.denote, Shape.map₂, HVector.getN, HVector.get]
  congr 2
  funext i
  exact Arith.muliPoison_comm _ _ _

theorem muliPoison_noflags (x y : IntW w) : Arith.muliPoison {} x y = mulPoison x y := by
  unfold IntW at x y
  cases x <;> cases y <;> rfl

theorem prog_is_dot (n w : Nat) (x y : Fin [n].prod → IntW w) :
    prog n w x y =
      ([VectorD.dot_prod x y]ₕ : HVector toType [Ty.shaped .scalar (.int (.int w))]) := by
  unfold prog VectorD.dot_prod
  simp only [Op.denote, Arith.Op.denote, VectorD.Op.denote, Shape.map₂, HVector.getN, HVector.get,
    muliPoison_noflags, reduceAddPoison, VectorD.reduceAddPoison']

/-- `prog_comm` again, now as a consequence of `prog_is_dot` and `dot_prod_comm`. -/
theorem prog_comm' (n w : Nat) (x y : Fin [n].prod → IntW w) :
    prog n w x y = prog n w y x := by
  rw [prog_is_dot, prog_is_dot, VectorD.dot_prod_comm]

#print axioms prog_comm
#print axioms prog_is_dot

end MLIRSem

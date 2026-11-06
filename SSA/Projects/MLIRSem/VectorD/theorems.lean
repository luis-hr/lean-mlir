import SSA.Projects.MLIRSem.VectorD.Semantics

namespace VectorD

open Builtin

def reduceAddPoison' (x : Fin n -> IntW m)
  (init : IntW m := .value (0#m)) :
  IntW m :=
  Fin.foldl n (fun acc i => addPoison (x i) acc ) init

def dot_prod (x : Fin n -> IntW m) (y : Fin n -> IntW m) : IntW m :=
  let prod := fun (i : Fin n)  => mulPoison (x i)  (y i)
  reduceAddPoison prod

theorem mulPoison_comm (a b : IntW w) : mulPoison a b = mulPoison b a := by
  unfold IntW at a b
  cases a <;> cases b <;> simp [mulPoison, BitVec.mul_comm]

theorem dot_prod_comm (x : Fin n -> IntW m) (y : Fin n -> IntW m) :
  dot_prod x y = dot_prod y x := by
  simp only [dot_prod, mulPoison_comm]

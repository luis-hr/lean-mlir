import SSA.Projects.MLIRSem.Arith.Semantics

open Builtin
namespace Arith

theorem umulOverflow_comm (a b : BitVec w) :
  a.umulOverflow b = b.umulOverflow a :=
  by
  simp [BitVec.umulOverflow, Nat.mul_comm]

theorem smulOverflow_comm (a b : BitVec w) :
  BitVec.smulOverflow a b = b.smulOverflow a :=
  by
  simp [BitVec.smulOverflow, Int.mul_comm]

theorem muliPoison_comm (x y : IntW w) (f : IntegerOverflowFlags) :
    muliPoison f x y  = muliPoison f y x  := by
  unfold IntW at x y
  cases x <;> cases y <;> simp [muliPoison, BitVec.mul_comm, smulOverflow_comm, umulOverflow_comm]

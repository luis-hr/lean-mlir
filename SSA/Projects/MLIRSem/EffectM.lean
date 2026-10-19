inductive UB | ub
  deriving DecidableEq, Repr, Inhabited

abbrev UBM := Except UB

class HasUB (m : Type u → Type v) where
  throwUB {α : Type u} : m α
export HasUB (throwUB)

instance : HasUB UBM := ⟨.error .ub⟩

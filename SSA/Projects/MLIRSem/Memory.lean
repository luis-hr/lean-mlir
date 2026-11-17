import SSA.Projects.MLIRSem.Builtin.Semantics
import SSA.Projects.MLIRSem.EffectM

open Builtin

abbrev Heap := Nat -> Option Buffer

abbrev MemM := StateT Heap UBM

instance : HasUB MemM := ⟨StateT.lift throwUB⟩

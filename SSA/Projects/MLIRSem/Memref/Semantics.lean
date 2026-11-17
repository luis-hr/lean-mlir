import SSA.Projects.MLIRSem.Builtin.Semantics
import SSA.Projects.MLIRSem.Memref.Basic
import SSA.Projects.MLIRSem.Memory

open Builtin


def loadMemory (s : Scalar) (loc : Nat) (ind : List Nat) : MemM (Scalar.denote s) := do
 let some b := (← get) loc | throwUB
 let some x := readVec b.sizes b.data ind | throwUB
 if h : b.data_type = s then pure (h ▸ x) else throwUB

def writeMemory (s : Scalar) (loc : Nat) (val : Scalar.denote s) (ind : List Nat)
  : MemM (PUnit) := do
 let heap ← get
 let some b := heap loc | throwUB
 if h : b.data_type = s then
    let some v' := writeVec b.sizes val (h.symm ▸ b.data) ind | throwUB
    set (fun l => if l = loc then some {b with data := (h ▸ v')} else heap l)
 else throwUB

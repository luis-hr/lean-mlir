import SSA.Projects.MLIRSem.VectorD.Basic
import SSA.Projects.MLIRSem.Builtin.Semantics

open Builtin
-- For the sake of modularity, the definition of poison operations on bitvectors
-- is repeated here so that this dialect does not depend on Arith.

def addPoison (x : IntW n) (y : IntW n) := do
  let x' ← x
  let y' ← y
  .value (x' + y')

def mulPoison (x : IntW n) (y : IntW n) := do
  let x' ← x
  let y' ← y
  .value (x' * y')

def reduceAddPoison (x : Fin n -> IntW m)
  (init : IntW m := .value (0#m)) :
  IntW m :=
  Fin.foldl n (fun acc i => addPoison (x i) acc ) init

def reduceMulPoison (x : Fin n -> IntW m)
  (init : IntW m := .value (1#m)) :
  IntW m :=
  Fin.foldl n (fun acc i => mulPoison (x i) acc ) init

def extractPoison (v : Fin n → IntW w) : IntW index_def → IntW w
  | .value i => if h : i.toNat < n then v ⟨i.toNat, h⟩ else .poison
  | .poison  => .poison



def test_1 (i : Fin 10) : (IntW 10) := .value (i.val)

#eval reduceAddPoison test_1 (.value 10)

def test_2 (i : Fin 10) : IntW 10 := if i.val = 3 then .poison else .value (BitVec.ofNat 10 i.val)
#eval reduceAddPoison test_2          -- expect poison

def test_3 (_ : Fin 10) : IntW 10 := .value (BitVec.ofNat 10 1000)
#eval reduceAddPoison test_3          -- expect (value 0x310#10)

#eval reduceAddPoison test_1 (.value 5#10)   -- expect 50 → (value 0x032#10)

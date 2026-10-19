import SSA.Projects.MLIRSem.Builtin.Semantics
import SSA.Projects.MLIRSem.Arith.Basic
import SSA.Projects.MLIRSem.EffectM
namespace Arith

open Builtin

def addiPoison (flags : IntegerOverflowFlags := {})
(x : IntW n ) (y : IntW n ) : IntW n := do
  let x' ← x
  let y' ← y
  if flags.nsw ∧ BitVec.saddOverflow x' y' then
    .poison
  else if flags.nuw ∧ BitVec.uaddOverflow x' y' then
    .poison
  else
    .value <| x' + y'

def muliPoison (flags : IntegerOverflowFlags := {}) (x : IntW n) (y : IntW n)  : IntW n := do
  let x' ← x
  let y' ← y
  if flags.nsw ∧ BitVec.smulOverflow x' y' then
    .poison
  else if flags.nuw ∧ BitVec.umulOverflow x' y' then
    .poison
  else
    .value <| x' * y'


def divsiPoison [Monad m] [HasUB m] (exact : Bool := false) (x y : IntW n)  :
 m (IntW n) :=
  match y with
  | .poison => throwUB
  | .value y' =>
    if y' = 0#n then throwUB
    else match x with
      | .poison =>
        if y' = BitVec.allOnes n then throwUB
        else pure .poison
      | .value x' =>
        if x' = BitVec.intMin n ∧ y' = BitVec.allOnes n then throwUB
        else if exact ∧ x'.srem y' ≠ 0#n then pure .poison
        else pure (.value (x'.sdiv y'))



end Arith

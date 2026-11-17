import LeanMLIR.Framework
import LeanMLIR.Util
import LeanMLIR.Tactic.SimpSet
import LeanMLIR.Basic


namespace Builtin
abbrev index_def := 64


inductive Shape
  | scalar
  | vector : List Nat -> Shape -- for instance 3x4 vector. Hence the list
  deriving DecidableEq, Inhabited, Lean.ToExpr, Repr

inductive IntType
  | int : Nat -> IntType -- ex: i32, i64
  | index : IntType
--| uint : Nat -> IntType
--| sint : Nat -> IntType
  deriving DecidableEq, Inhabited, Lean.ToExpr, Repr

inductive Scalar
  | int : IntType -> Scalar
--| float : FloatType -> S
  deriving DecidableEq, Inhabited, Lean.ToExpr, Repr

inductive Ty
  | shaped : Shape -> Scalar -> Ty
  | memref : List (Option Nat) -> Scalar -> Ty
  deriving DecidableEq, Inhabited, Lean.ToExpr, Repr

structure ShapedInt where
  shape : Shape
  val : IntType
  deriving DecidableEq, Inhabited, Lean.ToExpr, Repr

structure MemrefScalar where
  sizes : List (Option Nat)
  data : Scalar
  deriving DecidableEq, Inhabited, Lean.ToExpr, Repr

def MemrefScalar.toTy (t : MemrefScalar) := Ty.memref t.sizes t.data

def ShapedInt.toTy (t : ShapedInt) : Ty := .shaped t.shape (.int (t.val))

def IntType.width : IntType -> Nat
  | .int w => w
  | .index => index_def

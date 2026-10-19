import SSA.Projects.MLIRSem.Builtin.Types

namespace Builtin

abbrev IntW w := PoisonOr (BitVec w)

def Shape.denote : Shape -> Type -> Type
  | .scalar, t => t
  | .vector dims, t => Fin (dims.prod) -> t

def Shape.map₂  (f : α → β →  γ) :
 (s : Shape) → s.denote α → s.denote β → s.denote γ
  | .scalar,   a, b => f a b
  | .vector _, a, b => fun i => f (a i) (b i)

 def Shape.mapM₂ [Monad m] (f : α → β → m γ) :
    (s : Shape) → s.denote α → s.denote β → m (s.denote γ)
  | .scalar,   a, b => f a b
  | .vector _, a, b => do
      let v ← (Vector.ofFn fun i => (a i, b i)).mapM fun p => f p.1 p.2
      pure fun i => v[i]

def IntType.denote : IntType -> Type
  | .int w => IntW w -- A bitvector of length w that can turn into
  -- poison during undefined behavior.

def Scalar.denote : Scalar -> Type
  | .int t => IntType.denote t

instance : TyDenote Ty where
  toType
  | .shaped s e => s.denote e.denote

@[simp_denote] theorem toType_toTy (t : ShapedInt) :
    TyDenote.toType t.toTy = t.shape.denote (IntW (t.val.width)) := rfl

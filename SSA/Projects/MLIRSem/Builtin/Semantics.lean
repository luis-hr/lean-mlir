import SSA.Projects.MLIRSem.Builtin.Types

namespace Builtin

abbrev IntW w := PoisonOr (BitVec w)


def denoteVec : List Nat → Type → Type
  | [],      t => t
  | n :: tl, t => Fin n → denoteVec tl t

def Shape.denote : Shape -> Type -> Type
  | .scalar, t => t
  | .vector dims, t => denoteVec dims t

def map₂_helper (f : α → β → γ)  :
(l : List ℕ) → denoteVec l α → denoteVec l β → denoteVec l γ
    | [], a, b => f a b
    | _ :: tl, a, b => fun i => map₂_helper f tl (a i) (b i)

def map₂_helperM [Monad m] (f : α → β → m γ)  :
(l : List ℕ) → denoteVec l α → denoteVec l β → m (denoteVec l γ)
    | [], a, b => f a b
    | [n], a, b =>  do
      let v ← (Vector.ofFn (fun i => (a i, b i))).mapM (fun p => f p.1 p.2)
      pure (fun i => v[i])
    | n :: tl, a, b => do
      let v1 := (Vector.ofFn (fun i => (a i, b i)))
      let v2 := v1.mapM (fun p => map₂_helperM f tl p.1 p.2)
      let v ← v2
      pure (fun i => v[i])

def Shape.map₂  (f : α → β →  γ) :
 (s : Shape) → s.denote α → s.denote β → s.denote γ
  | .scalar,   a, b => f a b
  | .vector dims, a , b => map₂_helper f dims a b

 def Shape.mapM₂ [Monad m] (f : α → β → m γ) :
    (s : Shape) → s.denote α → s.denote β → m (s.denote γ)
  | .scalar,   a, b => f a b
  | .vector l, a, b => map₂_helperM f l a b

def IntType.denote (t : IntType) : Type := IntW t.width

def Scalar.denote : Scalar -> Type
  | .int t => IntType.denote t

structure Buffer where
  data_type : Scalar
  sizes : List Nat
  data : denoteVec sizes (data_type.denote)

def readVec : (sizes : List Nat) → denoteVec sizes α → List Nat → Option α
  | [],      x, []      => some x
  | d :: ds, v, i :: is => if h : i < d then readVec ds (v ⟨i, h⟩) is else none
  | _,       _, _       => none

def writeVec : (sizes : List Nat) → α → denoteVec sizes α → List Nat → Option (denoteVec sizes α)
  | [], v , _, []  =>  some v
  | d :: ds, v, f, i :: is => if h : i < d then
      (writeVec ds v (f ⟨i, h⟩) is).map
      (fun res_v x => if x = i then res_v else f x)
    else none
  | _, _, _ , _ => none

def ex_vec1 := fun (_ : Fin 4) (_ : Fin 3) => 1

#eval (Option.getD (writeVec [4, 3] 2 ex_vec1 [1, 1]) ex_vec1) 1 1

instance : TyDenote Ty where
  toType
  | .shaped s e => s.denote e.denote
  | .memref _ _ => Nat



@[simp_denote] theorem toType_toTy (t : ShapedInt) :
    TyDenote.toType t.toTy = t.shape.denote (IntW (t.val.width)) := rfl

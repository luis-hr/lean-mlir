import SSA.Projects.MLIRSem.Builtin.Semantics
import SSA.Projects.MLIRSem.EffectM

open Builtin

namespace Scf

-- n is the number of iterations. iv computes the value of the induction variable
-- at a given step.
def forLoop [Monad m] (n : Nat) (iv : Nat → ι) (body : ι → σ → m σ) (init : σ) : m σ :=
  (List.range n).foldlM (fun s k => body (iv k) s) init

theorem trip_count_0 [Monad m] (iv : Nat → ι) (body : ι → σ → m σ) (init : σ ) :
  forLoop 0 iv body init = pure init := rfl

def indexInvariant (body : ι → α → β)
  (iv : Nat → ι ) : Prop :=
  ∀ i j st, body (iv i) st = body (iv j) st

def atZero  (body : ι → α → β) (iv : Nat → ι) : α → β :=
  fun (s : α ) => body (iv 0) s

theorem eval_atZero [Monad m] (body : ι → σ → m σ)
   (iv : ℕ → ι) (hf : indexInvariant body iv) (i : ℕ) (st : σ ) :
    atZero body iv st = body (iv i) st := by
    unfold indexInvariant at hf
    rewrite [hf]
    rfl

theorem foldlM_pure [Monad m] [LawfulMonad m]
    (f : σ → α → m σ) (g : σ → α → σ) (l : List α)
    (h : ∀ a ∈ l, ∀ s, f s a = pure (g s a)) (init : σ) :
    l.foldlM f init = pure (l.foldl g init) := by
  induction l generalizing init with
  | nil => simp
  | cons a as ih =>
    rw [List.foldlM_cons, List.foldl_cons, h a (by simp), pure_bind]
    exact ih (fun b hb s => h b (by simp [hb]) s) _

theorem forLoop_pure [Monad m] [LawfulMonad m] (n : Nat) (iv : Nat → ι)
    (body : ι → σ → m σ) (g : ι → σ → σ)
    (h : ∀ k < n, ∀ s, body (iv k) s = pure (g (iv k) s)) (init : σ) :
    forLoop n iv body init = pure ((List.range n).foldl (fun s k => g (iv k) s) init) := by
  unfold forLoop
  exact foldlM_pure _ _ _ (fun k hk s => h k (List.mem_range.mp hk) s) init


theorem pure_fold_iterate [Monad M] [LawfulMonad M] (n : Nat) (iv : Nat → ι)
  (g : ι → σ → σ) (hf : indexInvariant g iv) (init : σ) :
    List.foldl (fun s k => g (iv k) s) init (List.range n) =
    ((atZero g iv)^[n] ) init := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, Function.iterate_succ_apply']
    simp only [List.foldl_cons, List.foldl_nil, atZero]
    exact hf n 0 _

def representable (signed : Bool) (w : ℕ) (x : ℤ) : Bool :=
  if signed then decide (-(2 ^ (w - 1) : ℤ) ≤ x ∧ x < 2 ^ (w - 1))
  else decide (0 ≤ x ∧ x < 2 ^ w)

def tripCount (lb ub step : ℤ) : ℕ :=
  ((ub - lb + step - 1) / step).toNat

def scfForInt [Monad m] [HasUB m] (w : ℕ) (lb ub step : ℤ)
    (body : IntW w → σ → m σ) (init : σ) (u_cmp : Bool): m σ :=
  if step ≤ 0 then throwUB
  else
  let trip_count := tripCount lb ub step
  if !(representable u_cmp w (lb + trip_count*step)) then throwUB
  else
  forLoop trip_count
         (fun k => PoisonOr.value (BitVec.ofInt w (lb + k * step))) body init

def scfFor [Monad m] [HasUB m] (unsignedCmp : Bool) (w : ℕ)
    (lb ub step : IntW w) (body : IntW w → σ → m σ) (init : σ) : m σ :=
  match lb, ub, step with
  | .value l, .value u, .value s =>
      let toZ : BitVec w → ℤ := if unsignedCmp then (↑·.toNat) else (·.toInt)
      scfForInt w (toZ l) (toZ u) (toZ s) body init unsignedCmp
  | _, _, _ => throwUB

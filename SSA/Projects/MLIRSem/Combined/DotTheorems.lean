import SSA.Projects.MLIRSem.Combined.Dot
import SSA.Projects.MLIRSem.Combined.theorems

namespace MLIRSem
open Builtin LeanMLIR

private abbrev i32   : Ty := .shaped .scalar (.int (.int 32))
private abbrev v4i32 : Ty := .shaped (.vector [4]) (.int (.int 32))

def dotInputs (a b : Fin 4 → IntW 32) : Ctxt.Valuation (Ctxt.ofList [v4i32, v4i32]) :=
  Ctxt.Valuation.ofHVector
    [(show TyDenote.toType v4i32 from b), (show TyDenote.toType v4i32 from a)]ₕ


theorem addiPoison_noflags_swap (x y : IntW w) : Arith.addiPoison {} x y = addPoison y x := by
  unfold IntW at x y
  cases x <;> cases y <;> simp [Arith.addiPoison, addPoison, BitVec.add_comm]

def loopChain (a b : Fin 4 → IntW 32) : IntW 32 :=
  let m (i : Fin 4) := Arith.muliPoison {} (a i) (b i)
  Arith.addiPoison {} (Arith.addiPoison {} (Arith.addiPoison {} (Arith.addiPoison {}
    (.value 0) (m 0)) (m 1)) (m 2)) (m 3)

theorem reduce_eq_chain (a b : Fin 4 → IntW 32) :
    reduceAddPoison (fun i => Arith.muliPoison {} (a i) (b i)) = loopChain a b := by
  simp only [loopChain, addiPoison_noflags_swap, reduceAddPoison,
    Fin.foldl_succ_last, Fin.foldl_zero]
  rfl


theorem scfFor_0_4_1 {σ} (lb ub step : IntW IntType.index.width)
    (hlb : lb = .value (BitVec.ofInt _ 0)) (hub : ub = .value (BitVec.ofInt _ 4))
    (hstep : step = .value (BitVec.ofInt _ 1))
    (body : IntW IntType.index.width → σ → UBM σ) (init : σ) :
    Scf.scfFor (m := UBM) false IntType.index.width lb ub step body init =
      (do let s ← body (.value 0#64) init
          let s ← body (.value 1#64) s
          let s ← body (.value 2#64) s
          body (.value 3#64) s) := by
  subst hlb hub hstep
  simp [Scf.scfFor, Scf.representable, Scf.scfForInt, Scf.tripCount, Scf.forLoop, List.range_succ,
    IntType.width, index_def]

theorem dotLoop_spec (a b : Fin 4 → IntW 32) :
    dotLoop.denote (dotInputs a b) = pure ([loopChain a b]ₕ : HVector toType [i32]) := by
  unfold dotLoop dotInputs
  simp only [simp_denote]
  simp only [Op.denote, Arith.Op.denote, Scf.Op.denote, HVector.split]
  rw [scfFor_0_4_1]
  case hlb => rfl
  case hub => rfl
  case hstep => rfl
  simp only [Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil,
    Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append, Ctxt.Valuation.cons_eval,
    Ctxt.Valuation.cons_zero, Ctxt.Var.last, VectorD.Op.denote, Shape.map₂,
    HVector.getN, HVector.get, HVector.append, pure_bind]
  rfl

theorem dotRed_spec (a b : Fin 4 → IntW 32) :
    dotRed.denote (dotInputs a b) =
      ([reduceAddPoison (fun i => Arith.muliPoison {} (a i) (b i))]ₕ : HVector toType [i32]) := by
  unfold dotRed dotInputs
  simp_peephole
  rfl

theorem dotLoop_eq_dotRed (a b : Fin 4 → IntW 32) :
    dotLoop.denote (dotInputs a b) = pure (dotRed.denote (dotInputs a b)) := by
  rw [dotLoop_spec, dotRed_spec]
  exact congrArg (fun x => pure [x]ₕ) (reduce_eq_chain a b).symm

theorem dotRed_is_dot_prod (a b : Fin 4 → IntW 32) :
    dotRed.denote (dotInputs a b) = ([VectorD.dot_prod a b]ₕ : HVector toType [i32]) := by
  rw [dotRed_spec]
  simp only [VectorD.dot_prod, muliPoison_noflags]

#print axioms dotLoop_eq_dotRed

end MLIRSem

module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Finrank

@[expose] public section

noncomputable section
namespace GKGauge
open Matrix MvPolynomial LinearMap Finset
variable {k F : Type*} [Field k] [Infinite k] [Field F] [Algebra k F]

/-- A polynomial with coefficients in the larger field is detected even by
assignments in the smaller infinite field. -/
theorem exists_base_eval {σ : Type*} (p : MvPolynomial σ F) (hp : p ≠ 0) :
    ∃ x : σ → k, MvPolynomial.eval (fun i => algebraMap k F (x i)) p ≠ 0 := by
  classical
  by_contra! h
  apply hp
  apply MvPolynomial.funext_set (fun _ : σ => Set.range (algebraMap k F))
    (fun _ => Set.infinite_range_of_injective (algebraMap k F).injective)
  intro t ht
  choose x hx using fun i => ht i (Set.mem_univ i)
  simpa only [← funext hx, map_zero] using h x

variable {σ n : Type*} [Fintype σ] [Fintype n] [DecidableEq n]
def genericMatrix (v : σ → Matrix n n F) : Matrix n n (MvPolynomial σ F) :=
  fun a b => ∑ i, C (v i a b) * X i

theorem eval_genericMatrix (v : σ → Matrix n n F) (x : σ → F) :
    (MvPolynomial.eval x).mapMatrix (genericMatrix v) = ∑ i, x i • v i := by
  classical
  ext a b
  simp [genericMatrix, Matrix.sum_apply, mul_comm]

theorem exists_base_invertible (v : σ → Matrix n n F) (h : ∃ x : σ → F, (∑ i, x i • v i).det ≠ 0) :
    ∃ x : σ → k, (∑ i, (algebraMap k F (x i)) • v i).det ≠ 0 := by
  classical
  obtain ⟨x,hx⟩ := h
  have hp : (genericMatrix v).det ≠ 0 := by
    intro hz
    apply hx
    rw [← eval_genericMatrix, ← RingHom.map_det, hz, map_zero]
  obtain ⟨a,ha⟩ := exists_base_eval (k:=k) _ hp
  refine ⟨a, ?_⟩
  rw [← eval_genericMatrix, ← RingHom.map_det]
  exact ha

end GKGauge
#print axioms GKGauge.exists_base_invertible

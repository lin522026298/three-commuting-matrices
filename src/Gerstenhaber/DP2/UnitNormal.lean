module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases
public import Lean.Elab.Tactic.Omega

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Gerstenhaber.DP2
open Module Matrix

/-- The actual field-linear multiplication operator on the square of the
coefficient algebra. Its rank is taken over the field, not over the ring. -/
def scalarMulVec {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (L : Matrix (Fin 2) (Fin 2) R) : (Fin 2 → R) →ₗ[K] (Fin 2 → R) :=
  (Matrix.toLin' L).restrictScalars K

def fieldRank (K : Type*) [Field K] {R : Type*} [CommRing R] [Algebra K R]
    (L : Matrix (Fin 2) (Fin 2) R) : ℕ :=
  Module.finrank K (LinearMap.range (scalarMulVec (K := K) L))

/-- The two by two Cayley--Hamilton identity, valid over a possibly
nonreduced coefficient ring, in the form needed for the rank reduction. -/
theorem square_zero_of_trace_det_zero {R : Type*} [CommRing R]
    (L : Matrix (Fin 2) (Fin 2) R) (htr : L.trace=0) (hdet : L.det=0) :
    L*L=0 := by
  have hCH : L*L-L.trace • L+L.det • (1 : Matrix (Fin 2) (Fin 2) R)=0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_succ,Matrix.trace_fin_two,Matrix.det_fin_two] <;> ring
  simpa only [htr,hdet,zero_smul,sub_zero,add_zero] using hCH

/-- A square-zero two by two ring matrix has field rank at most the field
dimension of its coefficient algebra. -/
theorem fieldRank_le_of_square_zero {K R : Type*} [Field K] [CommRing R]
    [Algebra K R] [Module.Finite K R]
    (L : Matrix (Fin 2) (Fin 2) R) (hL : L*L=0) :
    fieldRank K L ≤ Module.finrank K R := by
  let f := scalarMulVec (K := K) L
  have hi : LinearMap.range f ≤ LinearMap.ker f := by
    rintro v ⟨w,rfl⟩
    change L *ᵥ (L *ᵥ w)=0
    rw [Matrix.mulVec_mulVec,hL,Matrix.zero_mulVec]
  have hr := f.finrank_range_add_finrank_ker
  have hm := Submodule.finrank_mono hi
  have hd : Module.finrank K (Fin 2 → R)=2*Module.finrank K R := by
    rw [Module.finrank_pi_fintype]
    simp
  change Module.finrank K (LinearMap.range f) ≤ Module.finrank K R
  omega

/-- Left multiplication by an invertible ring matrix preserves the
actual field rank; no field structure on the coefficient ring is used. -/
theorem fieldRank_left_mul_of_isUnit {K R : Type*} [Field K] [CommRing R]
    [Algebra K R] [Module.Finite K R]
    (H L : Matrix (Fin 2) (Fin 2) R) (hH : IsUnit H) :
    fieldRank K (H*L)=fieldRank K L := by
  have hi := Matrix.mulVec_injective_of_isUnit hH
  have hk : LinearMap.ker (scalarMulVec (K := K) (H*L))=
      LinearMap.ker (scalarMulVec (K := K) L) := by
    ext v
    change (H*L) *ᵥ v=0 ↔ L *ᵥ v=0
    rw [← Matrix.mulVec_mulVec]
    constructor
    · intro h
      apply hi
      simpa using h
    · intro h
      rw [h,Matrix.mulVec_zero]
  have h1 := (scalarMulVec (K := K) (H*L)).finrank_range_add_finrank_ker
  have h2 := (scalarMulVec (K := K) L).finrank_range_add_finrank_ker
  rw [hk] at h1
  change Module.finrank K (LinearMap.range (scalarMulVec (K := K) (H*L)))=
    Module.finrank K (LinearMap.range (scalarMulVec (K := K) L))
  omega

/-- The genuine unit-normal entry-syzygy criterion. It bounds the actual
field-linear matrix rank on any finite commutative coefficient algebra. -/
theorem unit_normal_dimension_bound {K R : Type*} [Field K] [CommRing R]
    [Algebra K R] [Module.Finite K R]
    (L H : Matrix (Fin 2) (Fin 2) R)
    (hL : L.det=0) (hH : IsUnit H.det) (htr : (H.transpose*L).trace=0) :
    fieldRank K L ≤ Module.finrank K R := by
  have hHu : IsUnit H.transpose := (Matrix.isUnit_iff_isUnit_det _).mpr (by
    rwa [Matrix.det_transpose])
  have hd : (H.transpose*L).det=0 := by rw [Matrix.det_mul,hL,mul_zero]
  have hs := square_zero_of_trace_det_zero (H.transpose*L) htr hd
  have hr := fieldRank_le_of_square_zero (K := K) (H.transpose*L) hs
  rwa [fieldRank_left_mul_of_isUnit H.transpose L hHu] at hr

end Gerstenhaber.DP2

#print axioms Gerstenhaber.DP2.square_zero_of_trace_det_zero
#print axioms Gerstenhaber.DP2.fieldRank_le_of_square_zero
#print axioms Gerstenhaber.DP2.fieldRank_left_mul_of_isUnit
#print axioms Gerstenhaber.DP2.unit_normal_dimension_bound

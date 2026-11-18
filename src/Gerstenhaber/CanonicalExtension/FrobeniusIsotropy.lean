module

public import Gerstenhaber.DP2.LinearRow.RelativeDuality
public import Gerstenhaber.DP2.LinearRow.MonicFrobenius
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Lean.Elab.Tactic.Omega

/-!
The genuine finite Frobenius endpoint for the canonical extension proof.
No statement about canonical syzygies or three commuting matrices is
assumed here. The input is the actual multiplication pairing and actual
vanishing of all determinant pairings on a scalar subspace of B times B.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace Gerstenhaber.CanonicalExtension

open Module LinearMap
open Gerstenhaber.DP2.LinearRow

variable {K B : Type*} [Field K] [CommRing B] [Algebra K B]

def determinantForm (tau : B →ₗ[K] K) : LinearMap.BilinForm K (B × B) :=
  (frobeniusPairing tau).compl₁₂ (LinearMap.fst K B B) (LinearMap.snd K B B) -
    (frobeniusPairing tau).compl₁₂ (LinearMap.snd K B B) (LinearMap.fst K B B)

@[simp] theorem determinantForm_apply (tau : B →ₗ[K] K) (x y : B × B) :
    determinantForm tau x y = tau (x.1 * y.2 - x.2 * y.1) := by
  simp [determinantForm, map_sub]

theorem determinantForm_isAlt (tau : B →ₗ[K] K) :
    (determinantForm tau).IsAlt := by
  intro x
  simp [determinantForm_apply, mul_comm]

theorem determinantForm_nondegenerate (tau : B →ₗ[K] K)
    (htau : Function.Injective (frobeniusPairing tau)) :
    (determinantForm tau).Nondegenerate := by
  have hleft : (determinantForm tau).SeparatingLeft := by
    intro x hx
    have hx1 : x.1 = 0 := by
      apply htau
      ext b
      have h := hx (0,b)
      simpa using h
    have hx2 : x.2 = 0 := by
      apply htau
      ext b
      have h := hx (b,0)
      simpa using h
    exact Prod.ext hx1 hx2
  refine ⟨hleft, ?_⟩
  intro x hx
  apply hleft x
  intro y
  exact (determinantForm_isAlt tau).eq_iff.mp (hx y)

theorem determinant_zero_subspace_finrank_le
    [FiniteDimensional K B] (tau : B →ₗ[K] K)
    (htau : Function.Injective (frobeniusPairing tau))
    (L : Submodule K (B × B))
    (hL : ∀ x ∈ L, ∀ y ∈ L, x.1 * y.2 - x.2 * y.1 = 0) :
    finrank K L ≤ finrank K B := by
  let omega := determinantForm tau
  have hnondeg : omega.Nondegenerate := determinantForm_nondegenerate tau htau
  have hiso : L ≤ omega.orthogonal L := by
    intro x hx y hy
    change determinantForm tau y x = 0
    rw [determinantForm_apply, hL y hy x hx, map_zero]
  have hdim := Submodule.finrank_mono hiso
  have hsum := omega.finrank_add_finrank_orthogonal' L
  rw [hnondeg.ker_eq_bot, inf_bot_eq, finrank_bot, add_zero] at hsum
  have hprod : finrank K (B × B) = finrank K B + finrank K B :=
    Module.finrank_prod
  omega

/-- The Frobenius hypothesis is constructed for the actual monic quotient. -/
theorem monic_quotient_determinant_zero_finrank_le
    (P : Polynomial K) (hP : P.Monic)
    (L : Submodule K (AdjoinRoot P × AdjoinRoot P))
    (hL : ∀ x ∈ L, ∀ y ∈ L, x.1 * y.2 - x.2 * y.1 = 0) :
    finrank K L ≤ P.natDegree := by
  let := (monicPowerBasis hP).finiteDimensional_of_finite
  have hdim : finrank K (AdjoinRoot P) = P.natDegree := by
    simpa using Module.finrank_eq_card_basis (monicPowerBasis hP)
  have h := determinant_zero_subspace_finrank_le (monicCoeffTrace hP)
    (frobeniusPairing_monicCoeffTrace_bijective hP).1 L hL
  simpa only [hdim] using h

/-- In particular the actual truncated-polynomial endpoint has bound q. -/
theorem truncated_determinant_zero_finrank_le (q : ℕ)
    (L : Submodule K
      (AdjoinRoot ((Polynomial.X : Polynomial K)^q) ×
        AdjoinRoot ((Polynomial.X : Polynomial K)^q)))
    (hL : ∀ x ∈ L, ∀ y ∈ L, x.1 * y.2 - x.2 * y.1 = 0) :
    finrank K L ≤ q := by
  have h := monic_quotient_determinant_zero_finrank_le
    ((Polynomial.X : Polynomial K)^q) (Polynomial.monic_X_pow q) L hL
  simpa using h

end Gerstenhaber.CanonicalExtension

module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

@[expose] public section

namespace GKDivisor

/-- An iterated Frobenius on an affine algebra over a perfect field is finite. -/
theorem finite_iterateFrobenius (k R : Type*) [Field k] [PerfectField k]
    [CommRing R] [Algebra k R] [Algebra.FiniteType k R]
    (p : ℕ) [ExpChar k p] [ExpChar R p] (e : ℕ) :
    (iterateFrobenius R p e).Finite := by
  apply RingHom.finite_iff_isIntegral_and_finiteType.mpr
  constructor
  · intro x
    refine ⟨Polynomial.X ^ (p ^ e) - Polynomial.C x,
      Polynomial.monic_X_pow_sub_C _ (expChar_pow_pos R p e).ne', ?_⟩
    simp [Polynomial.eval₂_sub, iterateFrobenius_def]
  · apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap k R)
    have h : (iterateFrobenius R p e).comp (algebraMap k R) =
        (algebraMap k R).comp (iterateFrobenius k p e) := by
      ext x
      simp [RingHom.comp_apply, iterateFrobenius_def]
    rw [h]
    exact (RingHom.finiteType_algebraMap.mpr inferInstance).comp
      (RingHom.FiniteType.of_surjective _ (iterateFrobeniusEquiv k p e).surjective)

end GKDivisor

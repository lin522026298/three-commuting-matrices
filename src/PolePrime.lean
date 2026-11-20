module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.DedekindDomain.Dvr

@[expose] public section

set_option linter.style.haveILetI false
noncomputable section
namespace GKDivisor

open scoped nonZeroDivisors

/-- A prime minimal over a single nonzero nonunit has exactly height one. -/
theorem exists_heightOne_containing {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (q : R) (hq : q ≠ 0) (hn : ¬ IsUnit q) :
    ∃ P : Ideal R, P.IsPrime ∧ q ∈ P ∧ P.height = 1 := by
  let I := Ideal.span ({q} : Set R)
  obtain ⟨P, hP⟩ := I.nonempty_minimalPrimes (by simpa [I] using hn)
  haveI hp : P.IsPrime := hP.isPrime
  have hone : I.height = 1 := Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hq) hn
  refine ⟨P, hp, hP.1.2 (Ideal.subset_span (by simp)), le_antisymm ?_ ?_⟩
  · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes I P hP
  · rw [← hone]; exact Ideal.height_mono hP.1.2

/-- The local ring of a height-one prime on a normal noetherian domain is a DVR. -/
theorem atPrime_isDVR {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (P : Ideal R) [P.IsPrime] (hP : P.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  let L := Localization.AtPrime P
  haveI : IsNoetherianRing L := IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  haveI : IsIntegrallyClosed L :=
    isIntegrallyClosed_of_isLocalization L P.primeCompl P.primeCompl_le_nonZeroDivisors
  haveI : Ring.KrullDimLE 1 L := Ring.krullDimLE_iff.mpr (by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P L, hP]; simp)
  haveI : Ring.DimensionLEOne L := ⟨fun h hpr => hpr.isMaximal_of_ne_bot h⟩
  haveI : IsDedekindDomain L := {}
  exact ((IsDiscreteValuationRing.TFAE L
    (IsLocalization.AtPrime.not_isField R (Ideal.ne_bot_of_height_eq_one hP) L)).out 1 3).mpr
      (inferInstance : IsDedekindDomain L)

/-- No divisorial input: the ordinary nonzero nonunit supplies the prime and the DVR. -/
theorem nonunit_divisor {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (q : R) (hq : q ≠ 0) (hn : ¬ IsUnit q) :
    ∃ P : Ideal R, ∃ hp : P.IsPrime, q ∈ P ∧ P.height = 1 ∧
      IsDiscreteValuationRing (@Localization.AtPrime R _ P hp) := by
  obtain ⟨P,hp,hqP,hheight⟩ := exists_heightOne_containing q hq hn
  exact ⟨P,hp,hqP,hheight,atPrime_isDVR P hheight⟩

#print axioms GKDivisor.nonunit_divisor
end GKDivisor

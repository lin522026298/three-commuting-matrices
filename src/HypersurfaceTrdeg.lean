import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.UFD
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Polynomial.UniqueFactorization

set_option linter.style.haveILetI false
set_option maxHeartbeats 150000
noncomputable section
namespace GKDivisor
open Polynomial Ideal
universe u

theorem trdeg_integral_inj {k S A : Type u} [Field k] [CommRing S] [CommRing A]
    [IsDomain A] [Nontrivial S] [Algebra k S] [Algebra k A]
    (f : S →ₐ[k] A) (hi : Function.Injective f) (hI : f.IsIntegral) :
    Algebra.trdeg k A = Algebra.trdeg k S := by
  letI : Algebra S A := f.toRingHom.toAlgebra
  haveI : FaithfulSMul S A := (faithfulSMul_iff_algebraMap_injective S A).mpr hi
  haveI : IsScalarTower k S A := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  haveI : Algebra.IsIntegral S A := ⟨hI⟩
  rw [← trdeg_add_eq k S (A := A), trdeg_eq_zero (R := S) (A := A), add_zero]

private theorem transport_exists_inj {k S B C : Type u} [Field k] [CommRing S]
    [CommRing B] [CommRing C] [Algebra k S] [Algebra k B] [Algebra k C]
    (g : S →ₐ[k] B) (hg : Function.Injective g) (hgm : g.IsIntegral)
    (e : B ≃ₐ[k] C) :
    ∃ h : S →ₐ[k] C, Function.Injective h ∧ h.IsIntegral := by
  refine ⟨e.toAlgHom.comp g, e.injective.comp hg, ?_⟩
  exact hgm.trans g.toRingHom e.toRingEquiv.toRingHom
    (RingHom.isIntegral_of_surjective _ e.surjective)

private theorem univariate_hypersurface {k S : Type u} [Field k] [CommRing S] [IsDomain S]
    [Algebra k S] (F : S[X]) (hLC : IsUnit F.leadingCoeff) (hn : ¬IsUnit F) :
    ∃ h : S →ₐ[k] (S[X] ⧸ Ideal.span {F}), Function.Injective h ∧ h.IsIntegral := by
  have hF : F.degree ≠ 0 := by
    intro he
    have eq := Polynomial.eq_C_of_degree_eq_zero he
    have hh : IsUnit (F.coeff 0) := by simpa [Polynomial.leadingCoeff, Polynomial.natDegree, he] using hLC
    exact hn (by rw [eq]; exact hh.map Polynomial.C)
  let J := Ideal.span ({F} : Set S[X])
  let g := ((Ideal.Quotient.mkₐ S J).comp (Algebra.ofId S S[X])).restrictScalars k
  have hgi : Function.Injective g := AdjoinRoot.of.injective_of_degree_ne_zero hF
  have hgm : g.IsIntegral := (Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hLC).quotient_isIntegral <|
    Submodule.smul_of_tower_mem _ _ (Ideal.subset_span (Set.mem_singleton F))
  exact ⟨g,hgi,hgm⟩

private noncomputable def nChange {k : Type u} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n+1)) k) :
    MvPolynomial (Fin (n+1)) k ≃ₐ[k] (MvPolynomial (Fin n) k)[X] :=
  (NoetherNormalization.varChange f).trans (MvPolynomial.finSuccEquiv k n)

private noncomputable def nQuot {k : Type u} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n+1)) k) :
    (MvPolynomial (Fin (n+1)) k ⧸ Ideal.span {f}) ≃ₐ[k]
      ((MvPolynomial (Fin n) k)[X] ⧸ Ideal.span {nChange f f}) :=
  Ideal.quotientEquivAlg (R₁ := k) (Ideal.span {f}) (Ideal.span {nChange f f}) (nChange f)
    (by rw [Ideal.map_span,Set.image_singleton]; rfl)

/-- One nonzero nonunit equation in n+1 variables admits a transcendence normalization
with exactly n independent variables, including nonhomogeneous hypersurfaces. -/
theorem hypersurface_integral_inj {k : Type u} [Field k] {n : ℕ}
    (f : MvPolynomial (Fin (n+1)) k) (hf : f ≠ 0) (hn : ¬ IsUnit f) :
    ∃ g : MvPolynomial (Fin n) k →ₐ[k]
      (MvPolynomial (Fin (n+1)) k ⧸ Ideal.span {f}), Function.Injective g ∧ g.IsIntegral := by
  have hLC : IsUnit (nChange f f).leadingCoeff := NoetherNormalization.varChange_leadingCoeff_isUnit f hf
  have hnu : ¬ IsUnit (nChange f f) := fun h => hn (by simpa using h.map (nChange f).symm)
  obtain ⟨g, hi, hm⟩ := univariate_hypersurface (k := k) (nChange f f) hLC hnu
  exact transport_exists_inj g hi hm (nQuot f).symm

#print axioms GKDivisor.hypersurface_integral_inj
end GKDivisor

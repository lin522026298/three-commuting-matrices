module

public import HypersurfaceTrdeg
public import HeightContract
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

@[expose] public section

set_option linter.style.haveILetI false
set_option maxHeartbeats 350000
noncomputable section
namespace GKDivisor
open Ideal
universe u

theorem poly_trdeg (k : Type u) [Field k] (n : ℕ) :
    Algebra.trdeg k (MvPolynomial (Fin n) k) = n := by
  simp [MvPolynomial.trdeg_of_isDomain]

theorem trdeg_polynomial_divisor {k : Type u} [Field k] {n : ℕ}
    (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime] (hp : p.height = 1) :
    Algebra.trdeg k (MvPolynomial (Fin n) k ⧸ p) + 1 = n := by
  cases n with
  | zero =>
    obtain ⟨z,hz,hn⟩ := p.ne_bot_iff.mp (Ideal.ne_bot_of_height_eq_one hp)
    let e := MvPolynomial.isEmptyAlgEquiv k (Fin 0)
    have hu : IsUnit (e z) := isUnit_iff_ne_zero.mpr ((map_ne_zero_iff e e.injective).mpr hn)
    have hu' : IsUnit z := by simpa using hu.map e.symm
    exact False.elim ((Ideal.IsPrime.ne_top (I := p) inferInstance) (p.eq_top_of_isUnit_mem hz hu'))
  | succ n =>
    haveI : p.IsPrincipal := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hp
    obtain ⟨f,hgen⟩ := Submodule.IsPrincipal.principal (S := p)
    change p = Ideal.span {f} at hgen
    have hne : f ≠ 0 := by
      intro e; apply Ideal.ne_bot_of_height_eq_one hp
      simpa [e] using hgen
    have hnu : ¬ IsUnit f := by
      intro h; apply Ideal.IsPrime.ne_top (I := p) inferInstance
      exact hgen.trans (Ideal.span_singleton_eq_top.mpr h)
    haveI hprime : (Ideal.span {f}).IsPrime := hgen ▸ ‹p.IsPrime›
    obtain ⟨g,hi,hm⟩ := hypersurface_integral_inj f hne hnu
    have ht := trdeg_integral_inj g hi hm
    rw [hgen, ht, poly_trdeg]; simp

/-- Codimension-one dimension formula for affine domains over a field.  The ordinary
quotient domain is used first, then its fraction field is identified with the residue field. -/
theorem affine_heightOne_dimension (k R : Type u) [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R] (P : Ideal R) [P.IsPrime] (hP : P.height = 1) :
    Algebra.trdeg k (R ⧸ P) + 1 = Algebra.trdeg k R := by
  obtain ⟨n,f,hi,hf⟩ := exists_finite_inj_algHom_of_fg k R
  let S := MvPolynomial (Fin n) k
  letI : Algebra S R := f.toRingHom.toAlgebra
  haveI : FaithfulSMul S R := (faithfulSMul_iff_algebraMap_injective S R).mpr hi
  haveI : Module.Finite S R := hf
  haveI : IsScalarTower k S R := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let p := P.under S
  have hp : p.height = 1 := heightOne_under P hP
  have hQ : Algebra.trdeg k (R ⧸ P) = Algebra.trdeg k (S ⧸ p) :=
    trdeg_integral_inj (IsScalarTower.toAlgHom k (S ⧸ p) (R ⧸ P))
      (FaithfulSMul.algebraMap_injective _ _)
      (algebraMap_isIntegral_iff.mpr inferInstance)
  rw [hQ,trdeg_polynomial_divisor p hp,trdeg_integral_inj f hi (algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral S R)),poly_trdeg]

#print axioms GKDivisor.affine_heightOne_dimension
end GKDivisor

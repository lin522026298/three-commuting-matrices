module

public import JetCoefficient
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.PrincipalIdealDomain

@[expose] public section

noncomputable section
namespace DVRMinimal
open Polynomial Ideal

theorem jet_exact_ker {F B : Type*} [Field F] [CommRing B] (s : F →+* B)
    (u : B) (N : ℕ) (hN : u^N=0) (hlt : ∀ j < N, u^j ≠ 0) :
    RingHom.ker (Polynomial.eval₂RingHom s u) = Ideal.span {(X:F[X])^N} := by
  let f := Polynomial.eval₂RingHom s u
  have hu : f X = u := eval₂_X ..
  let g := Submodule.IsPrincipal.generator (RingHom.ker f)
  have hg : RingHom.ker f = Ideal.span {g} := (Ideal.span_singleton_generator _).symm
  have he : (X:F[X])^N ∈ RingHom.ker f := by rw [RingHom.mem_ker,map_pow,hu,hN]
  have hd : g ∣ X^N := Ideal.mem_span_singleton.mp (hg ▸ he)
  obtain ⟨j,hj,ha⟩ := (dvd_prime_pow (Polynomial.prime_X (R:=F)) N).mp hd
  have eq : RingHom.ker f = Ideal.span {(X:F[X])^j} := hg.trans (Ideal.span_singleton_eq_span_singleton.mpr ha)
  have hz : (X:F[X])^j ∈ RingHom.ker f := eq ▸ Ideal.subset_span (Set.mem_singleton _)
  rw [RingHom.mem_ker,map_pow,hu] at hz
  have hje : j = N := le_antisymm hj (le_of_not_gt (fun h => hlt j h hz))
  rwa [hje] at eq

theorem jetRingEquiv {B F : Type*} [CommRing B] [Field F] (q : B →+* F)
    (s : F →+* B) (hs : ∀ a,q (s a)=a) (u : B)
    (hk : RingHom.ker q = Ideal.span {u}) (N : ℕ) (hN : u^N=0)
    (hlt : ∀ j<N, u^j≠0) :
    ∃ e : (F[X] ⧸ Ideal.span {(X:F[X])^N}) ≃+* B,
      ∀ p : F[X], e (Ideal.Quotient.mk _ p) = (eval₂RingHom s u) p := by
  let f := eval₂RingHom s u
  let h := jet_exact_ker s u N hN hlt
  let e := (Ideal.quotEquivOfEq h.symm).trans
    (RingHom.quotientKerEquivOfSurjective (polynomial_jet B F q s hs u hk ⟨N,hN⟩))
  exact ⟨e,fun p => rfl⟩

#print axioms jet_exact_ker
#print axioms jetRingEquiv
end DVRMinimal

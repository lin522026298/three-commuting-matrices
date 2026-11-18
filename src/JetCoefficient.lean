import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.Algebra.Polynomial.Eval.Defs

noncomputable section
namespace DVRMinimal
open Polynomial

theorem charZero_formallySmooth (k F : Type*) [Field k] [CharZero k] [Field F] [Algebra k F] :
    Algebra.FormallySmooth k F := by
  obtain ⟨s,hs⟩ := exists_isTranscendenceBasis k F
  letI := hs.isAlgebraic_field
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1

theorem finiteJet_section {k B F : Type*} [Field k] [CharZero k]
    [CommRing B] [Field F] [Algebra k B] [Algebra k F] (q : B →ₐ[k] F)
    (hq : Function.Surjective q) (hn : IsNilpotent (RingHom.ker q.toRingHom)) :
    ∃ s : F →ₐ[k] B, ∀ a, q (s a) = a := by
  letI := charZero_formallySmooth k F
  exact ⟨Algebra.FormallySmooth.liftOfSurjective (AlgHom.id k F) q hq hn,
    Algebra.FormallySmooth.liftOfSurjective_apply _ _ _ _⟩

theorem polynomial_jet (B F : Type*) [CommRing B] [Field F] (q : B →+* F)
    (s : F →+* B) (hs : ∀ a, q (s a)=a) (u : B)
    (hk : RingHom.ker q = Ideal.span {u}) (hn : IsNilpotent u) :
    Function.Surjective (Polynomial.eval₂RingHom s u) := by
  obtain ⟨N,hN⟩ := hn
  have aux (j : ℕ) (x : B) : ∃ p : F[X], ∃ v : B,
      x = (Polynomial.eval₂RingHom s u) p + u^j*v := by
    induction j generalizing x with
    | zero => exact ⟨0,x,by simp⟩
    | succ j ih =>
      have hz : x-s (q x) ∈ RingHom.ker q := by
        rw [RingHom.mem_ker,map_sub,hs,sub_self]
      rw [hk,Ideal.mem_span_singleton] at hz
      obtain ⟨b,hb⟩ := hz
      obtain ⟨p,v,hv⟩ := ih b
      refine ⟨C (q x)+X*p,v,?_⟩
      simp only [map_add,map_mul,coe_eval₂RingHom,eval₂_C,eval₂_X,pow_succ']
      rw [hv] at hb; change x = s (q x)+u*((eval₂RingHom s u) p) + (u*u^j)*v; linear_combination hb
  intro x
  obtain ⟨p,v,hp⟩ := aux N x
  exact ⟨p,by simpa [hN] using hp.symm⟩

/-- No coefficient field in V: the section exists in V / m^N. -/
theorem coefficient_truncation {k V : Type*} [Field k] [CharZero k] [CommRing V]
    [Algebra k V] (m : Ideal V) [m.IsMaximal] (N : ℕ) (hN : 0<N) :
    ∃ s : (V ⧸ m) →ₐ[k] (V ⧸ m^N), ∀ a,
        Ideal.Quotient.factorₐ k (Ideal.pow_le_self hN.ne' : m^N ≤ m) (s a)=a := by
  letI : Field (V ⧸ m) := Ideal.Quotient.field m
  let q := Ideal.Quotient.factorₐ k (Ideal.pow_le_self hN.ne' : m^N ≤ m)
  apply finiteJet_section q
  · exact Ideal.Quotient.factor_surjective (Ideal.pow_le_self hN.ne' : m^N ≤ m)
  · change IsNilpotent (RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_self hN.ne' : m^N ≤ m)))
    refine ⟨N,?_⟩
    rw [Ideal.Quotient.factor_ker,←Ideal.map_pow,Ideal.map_quotient_self]; rfl

#print axioms charZero_formallySmooth
#print axioms finiteJet_section
#print axioms polynomial_jet
#print axioms coefficient_truncation
end DVRMinimal

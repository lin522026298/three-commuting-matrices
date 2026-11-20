module

public import ExactJet
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

@[expose] public section

noncomputable section
namespace DVRMinimal
open Polynomial
variable {k V : Type*} [Field k] [CharZero k] [CommRing V] [IsDomain V] [Algebra k V]

/-- Uniformizers are not presumed to come from a power-series coefficient system.
The identifier e sends polynomial X to the chosen actual uniformizer. -/
theorem uniformizer_jet_iso (k : Type*) [Field k] [CharZero k] [Algebra k V] (u : V) (hu : Irreducible u)
    (m : Ideal V) [m.IsMaximal] (hm : m=Ideal.span {u}) (N : ℕ) (hn : 0<N) :
    ∃ e : ((V ⧸ m)[X] ⧸ Ideal.span {(X:(V ⧸ m)[X])^N}) ≃+* (V ⧸ m^N),
      e (Ideal.Quotient.mk _ X) = Ideal.Quotient.mk (m^N) u ∧
      ∀ a : V ⧸ m, Ideal.Quotient.factor (Ideal.pow_le_self hn.ne' : m^N ≤ m)
          (e (Ideal.Quotient.mk _ (C a))) = a := by
  letI := Ideal.Quotient.field m
  let a := Ideal.Quotient.mk (m^N)
  let t := a u
  let q := Ideal.Quotient.factor (Ideal.pow_le_self hn.ne' : m^N ≤ m)
  obtain ⟨s,hs⟩ := coefficient_truncation (k:=k) m N hn
  have hk : RingHom.ker q = Ideal.span {t} := by
    rw [Ideal.Quotient.factor_ker]
    calc m.map a = (Ideal.span {u}).map a := congrArg (Ideal.map a) hm
         _ = Ideal.span {t} := by rw [Ideal.map_span, Set.image_singleton]
  have ht (j : ℕ) : t^j=0 ↔ N≤j := by
    change (a u)^j=0 ↔ _
    rw [← map_pow,Ideal.Quotient.eq_zero_iff_mem,hm,Ideal.span_singleton_pow,Ideal.mem_span_singleton]
    exact pow_dvd_pow_iff hu.ne_zero hu.not_isUnit
  obtain ⟨e,he⟩ := jetRingEquiv q s.toRingHom hs t hk N ((ht N).mpr le_rfl)
    (fun j hj => fun z => (not_le_of_gt hj) ((ht j).mp z))
  refine ⟨e,?_,?_⟩
  · rw [he,coe_eval₂RingHom,eval₂_X]
  · intro c; rw [he,coe_eval₂RingHom,eval₂_C]; exact hs c

#print axioms uniformizer_jet_iso
end DVRMinimal

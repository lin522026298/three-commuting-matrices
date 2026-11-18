import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.DiscreteValuationRing.Basic
noncomputable section
namespace DVRMinimal
open Ideal
abbrev JetI {R : Type*} [CommRing R] (t : R) (N : ℕ) := Ideal.span {t^N}
abbrev jetMk {R : Type*} [CommRing R] (t : R) (N : ℕ) := Ideal.Quotient.mk (JetI t N)

theorem jet_dvd {R : Type*} [CommRing R] (t a : R) {j N : ℕ} (hj : j ≤ N) :
    (jetMk t N t)^j ∣ jetMk t N a ↔ t^j ∣ a := by
  constructor
  · rintro ⟨w,h⟩
    obtain ⟨v,rfl⟩ := Ideal.Quotient.mk_surjective w
    have hz : jetMk t N (a-t^j*v)=0 := by rw [map_sub,map_mul,map_pow,h,sub_self]
    have hd : t^N ∣ a-t^j*v := Ideal.mem_span_singleton.mp ((Ideal.Quotient.eq_zero_iff_mem).mp hz)
    have he := (pow_dvd_pow t hj).trans hd
    exact (dvd_sub_left (dvd_mul_right (t^j) v)).mp he
  · intro d
    simpa only [map_pow] using map_dvd (jetMk t N) d

theorem jet_div_preserved {R S : Type*} [CommRing R] [CommRing S] {t : R} {u : S} {N : ℕ}
    (e : R ⧸ JetI t N ≃+* S ⧸ JetI u N) (et : e (jetMk t N t) = jetMk u N u)
    {a : R} {b : S} (hab : e (jetMk t N a) = jetMk u N b) {j : ℕ} (hj : j≤N) :
    t^j ∣ a ↔ u^j ∣ b := by
  rw [←jet_dvd t a hj,←jet_dvd u b hj,←hab,←et]
  constructor
  · exact fun h => by simpa only [map_pow] using map_dvd e h
  · exact fun h => by simpa only [map_pow,e.symm_apply_apply] using map_dvd e.symm h

open IsDiscreteValuationRing PowerSeries in
theorem exact_preserved_order {R F : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field F] {t : R} (ht : Irreducible t) {N : ℕ}
    (e : R ⧸ JetI t N ≃+* PowerSeries F ⧸ JetI X N)
    (et : e (jetMk t N t) = jetMk X N X)
    {a : R} {b : PowerSeries F} (hab : e (jetMk t N a)=jetMk X N b)
    {j : ℕ} (ha : addVal R a=j) (hj : j<N) : b.order=j := by
  have eq (i : ℕ) (hi : i≤N) : (i:ℕ∞)≤(j:ℕ∞) ↔ (i:ℕ∞)≤b.order := by
    nth_rw 1 [←ht.addVal_pow i]
    rw [←ha,addVal_le_iff_dvd]
    exact (jet_div_preserved e et hab hi).trans (X_pow_dvd_iff.trans nat_le_order_iff.symm)
  apply le_antisymm _ ((eq j hj.le).mp le_rfl)
  by_contra! H
  have next : (↑(j+1):ℕ∞)≤b.order := Order.add_one_le_of_lt H
  exact (not_le_of_gt (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self j) : (j:ℕ∞)<↑(j+1))) ((eq (j+1) hj).mpr next)

#print axioms jet_div_preserved
#print axioms exact_preserved_order
end DVRMinimal

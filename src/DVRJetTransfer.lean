module

public import LocalJetIso
public import PolynomialPowerJet
public import JetOrder

@[expose] public section

noncomputable section
namespace DVRMinimal
open Polynomial
open scoped PowerSeries
variable {V : Type*} [CommRing V] [IsDomain V]

/-- An exact (not assumed) coefficient/residue-preserving finite jet model.
The inverse direction is used to transport arbitrary polynomial graph identities. -/
theorem dvrJetTransfer (k : Type*) [Field k] [Algebra k V]
    (t : V) (ht : Irreducible t) (m : Ideal V) [m.IsMaximal] [Algebra.FormallySmooth k (V ⧸ m)] (hm : m=Ideal.span {t})
    (N : ℕ) (hN : 0<N) :
    let F := V ⧸ m
    ∃ e : (V ⧸ JetI t N) ≃+* (PowerSeries F ⧸ JetI PowerSeries.X N),
      e (jetMk t N t) = jetMk PowerSeries.X N PowerSeries.X ∧
        ∀ (a : V) (b : PowerSeries F), e (jetMk t N a) = jetMk PowerSeries.X N b →
          PowerSeries.constantCoeff b = Ideal.Quotient.mk m a := by
  letI := Ideal.Quotient.field m
  let F := V ⧸ m
  obtain ⟨e0,ex,ec⟩ := uniformizer_jet_iso k t ht m hm N hN
  have hI : m^N = JetI t N := by rw [hm,Ideal.span_singleton_pow]
  let etr := Ideal.quotEquivOfEq hI
  let pl := polySeriesJetEquiv F N
  let e := etr.symm.trans (e0.symm.trans pl)
  have he (p : F[X]) : e (etr (e0 (Ideal.Quotient.mk _ p))) =
      jetMk PowerSeries.X N (p : PowerSeries F) := by
    simp only [e,RingEquiv.trans_apply,etr.symm_apply_apply,e0.symm_apply_apply]
    rfl
  have hmk (v : V) : etr (Ideal.Quotient.mk (m^N) v) = jetMk t N v := rfl
  have het : e (jetMk t N t)=jetMk PowerSeries.X N PowerSeries.X := by
    have h := he (X : F[X]); rw [ex,hmk,Polynomial.coe_X] at h; exact h
  refine ⟨e,het,?_⟩
  intro a b hab
  let c := Ideal.Quotient.mk m a
  obtain ⟨v,hv⟩ := Ideal.Quotient.mk_surjective (e0 (Ideal.Quotient.mk _ (C c)))
  have hc : Ideal.Quotient.mk m v=c := by
    have h := ec c
    rw [←hv] at h; exact h
  have hc' : e (jetMk t N v)=jetMk PowerSeries.X N (PowerSeries.C c) := by
    have h := he (C c); rw [←hv,hmk,Polynomial.coe_C] at h; exact h
  have ha : t ∣ a-v := by
    apply Ideal.mem_span_singleton.mp
    rw [←hm,←Ideal.Quotient.eq_zero_iff_mem,map_sub,hc,sub_self]
  have hb : PowerSeries.X ∣ b-PowerSeries.C c := by
    have hsub : e (jetMk t N (a-v))=jetMk PowerSeries.X N (b-PowerSeries.C c) := by
      rw [map_sub,map_sub,hab,hc',map_sub]
    have d := (jet_div_preserved e het hsub (j:=1) hN).mp (by simpa using ha)
    simpa using d
  have hz := PowerSeries.X_dvd_iff.mp hb
  rw [map_sub,PowerSeries.constantCoeff_C,sub_eq_zero] at hz
  exact hz

#print axioms dvrJetTransfer
end DVRMinimal

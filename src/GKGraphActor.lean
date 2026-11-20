module

public import GKGraphTransport
public import ActorIndex

@[expose] public section

set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 90000
noncomputable section
namespace GKGraph
open IsDiscreteValuationRing Module
variable (k : Type*) [Field k] (r : ℕ) {O : Type*} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O]
abbrev bad (T : Fin 6 → Mat O r) (hT : Relations r T) :=
  length O (DivisorG3.QP (T 0)) <
    length O (DivisorG3.actor (T 0) (T 1) (T 3) (T 2) (T 4) hT.y.symm hT.z.symm)

theorem bad_iff_selected (T : Fin 6 → Mat O r) (hP : (T 0).det ≠ 0)
    (hT : Relations r T) (hr : 0 < r) :
    bad r T hT ↔ ∃ s : selectCols r,
      addVal O (fullMinor r (T 0) (T 1) (T 2) s) < addVal O ((T 0).det^(r-1)) := by
  have h := DivisorG3.bad_iff_minor (T 0) (T 1) (T 3) (T 2) (T 4) (T 5) hP
    (by simpa only [Fintype.card_fin] using hr) hT.y.symm hT.z.symm hT.comm.symm
  let f (n : ℕ) := ∃ s : Row r → Row r ⊕ (Fin n × Fin n),
    addVal O (((DivisorG3.blockColumns (T 0) (DivisorG3.box (T 1) (T 2) n n)).submatrix id s).det) <
      addVal O ((T 0).det^(n-1))
  change bad r T hT ↔ f (Fintype.card (Fin r)) at h
  rw [Fintype.card_fin] at h
  exact h

/-- A bad actual DVR endomorphism algebra exhibits a *concrete* nonzero nonunit
in the graph of an inverse selected full minor. -/
theorem chart_of_bad [Algebra k O] (T : Fin 6 → Mat O r) (hP : (T 0).det ≠ 0)
    (hT : Relations r T) (hr : 0 < r) (hb : bad r T hT) :
    ∃ s : selectCols r, universalMinor k r s ≠ 0 ∧
      GKRational.q (K := K k r) (gdelta k r^(r-1)) (universalMinor k r s) ≠ 0 ∧
      ¬ IsUnit (GKRational.q (K := K k r) (gdelta k r^(r-1)) (universalMinor k r s)) := by
  obtain ⟨s,hs⟩ := (bad_iff_selected r T hP hT hr).mp hb
  refine ⟨s,?_,strict_minor_nonunit k r T hP hT s hs⟩
  intro hz
  have hzero : fullMinor r (T 0) (T 1) (T 2) s = 0 := by rw [←point_minor k r T hP hT,hz,map_zero]
  rw [hzero,AddValuation.map_zero] at hs
  exact not_top_lt hs

/-- The generic or any other DVR receiving the inverse-minor chart, with q in
its maximal ideal and nonzero determinant, reproduces a bad actual module. -/
theorem bad_at_pole (s : selectCols r) (hr : 0 < r)
    (ψ : GKRational.adj (K := K k r) (gdelta k r ^ (r-1)) (universalMinor k r s) →+* O)
    (φ : ring k r →+* O) (extends_ : ∀ b, ψ (algebraMap _ _ b) = φ b)
    (hδ : φ (gdelta k r) ≠ 0) (hd : universalMinor k r s ≠ 0)
    (hn : ¬ IsUnit (ψ (GKRational.q _ _))) :
    bad r (datum k r φ) (datum_relations k r φ) := by
  apply (bad_iff_selected r _ (by rwa [datum_det]) (datum_relations k r φ) hr).mpr
  exact ⟨s,strict_at_inverse_pole k r s ψ φ extends_ hδ hd hn⟩

end GKGraph

import JetBaseChange
import ActualSixJet

noncomputable section
namespace GKDivisor.Jet
open PowerSeries IsDiscreteValuationRing
universe u
attribute [local instance] BadPole.cr BadPole.dom BadPole.dvr BadPole.alg
variable {k : Type u} [Field k] {r : ℕ} {s : GKGraph.selectCols r}

def constEntries {E : Type*} [Field E] (T : Fin 6 → GKGraph.Mat (PowerSeries E) r) :
    GKGraph.AllVars r → E := fun z => constantCoeff (T z.1 z.2.1 z.2.2)

/-- A concrete width-r DVR presentation over E[[X]]. The last requirement
counts the *actual constant entries* rather than the size of E. -/
structure SeriesPole (k E : Type u) [Field k] [Field E] [Algebra k E]
    (r : ℕ) (s : GKGraph.selectCols r) where
  T : Fin 6 → GKGraph.Mat (PowerSeries E) r
  relations : GKGraph.Relations r T
  det_ne : (T 0).det ≠ 0
  strict : addVal _ (GKGraph.fullMinor r (T 0) (T 1) (T 2) s) < addVal _ ((T 0).det^(r-1))
  count : Algebra.trdeg k (Algebra.adjoin k (Set.range (constEntries T))) + 1 = (3*r*r : ℕ)

theorem SeriesPole.bad {E : Type u} [Field E] [Algebra k E] (D : SeriesPole k E r s) (hr : 0<r) :
    BadDatum D.T D.relations := (badDatum_iff_strict _ _ D.det_ne hr).mpr ⟨s,D.strict⟩

/-- Precision and both finite orders are obtained from the selected original minor. -/
theorem pole_orders (B : BadPole k r (GKGraph.universalMinor k r s)) :
    ∃ a d : ℕ, addVal B.V (B.matrices 0).det = a ∧
      addVal B.V (GKGraph.fullMinor r (B.matrices 0) (B.matrices 1) (B.matrices 2) s) = d ∧
      (d:ℕ∞) < (r-1) • (a:ℕ∞) := by
  have hd := B.same_minor_strict
  have hA := B.det_ne_zero
  rw [addVal_pow] at hd
  let n := addVal B.V (B.matrices 0).det
  let v := addVal B.V (GKGraph.fullMinor r (B.matrices 0) (B.matrices 1) (B.matrices 2) s)
  have hn : n ≠ ⊤ := addVal_eq_top_iff.not.mpr hA
  have hv : v ≠ ⊤ := ne_top_of_lt hd
  exact ⟨n.toNat,v.toNat,(ENat.natCast_toNat_eq_self.mpr hn).symm,(ENat.natCast_toNat_eq_self.mpr hv).symm,
    by simpa only [ENat.natCast_toNat_eq_self.mpr hn,ENat.natCast_toNat_eq_self.mpr hv] using hd⟩

/-- Common constructor for any coefficient field extension. -/
theorem realize_series {E : Type u} [Field E] [Algebra k E]
    (B : BadPole k r (GKGraph.universalMinor k r s))
    (e : IsLocalRing.ResidueField B.V →ₐ[k] E)
    (a d : ℕ) (hd : (d:ℕ∞) < (r-1) • (a:ℕ∞))
    (T : Fin 6 → GKGraph.Mat (PowerSeries E) r) (rel : GKGraph.Relations r T)
    (ha : (T 0).det.order = a) (hv : (GKGraph.fullMinor r (T 0) (T 1) (T 2) s).order = d)
    (hc : ∀ l i j, constantCoeff (T l i j) = e (IsLocalRing.residue B.V (B.matrices l i j))) :
    ∃ S : SeriesPole k E r s, S.T = T ∧ constEntries S.T = e ∘ B.residualMap ∘ GKGraph.gcoord k r := by
  have se : constEntries T = e ∘ B.residualMap ∘ GKGraph.gcoord k r := by
    funext z
    exact hc z.1 z.2.1 z.2.2
  have he := count_extension e (B.residualMap ∘ GKGraph.gcoord k r)
  have hn : (T 0).det ≠ 0 := by intro eq; rw [eq,PowerSeries.order_zero] at ha; exact ENat.natCast_ne_top a ha.symm
  refine ⟨⟨T, rel, hn, ?_, ?_⟩,rfl,se⟩
  · rw [addVal_pow,series_value,series_value,ha,hv]
    exact hd
  · rw [se,he]
    exact B.count

theorem pole_to_series [CharZero k] (B : BadPole k r (GKGraph.universalMinor k r s)) :
    ∃ S : SeriesPole k (IsLocalRing.ResidueField B.V) r s,
      constEntries S.T = B.residualMap ∘ GKGraph.gcoord k r := by
  obtain ⟨a,d,ha,hd,hl⟩ := pole_orders B
  obtain ⟨t,ht⟩ := exists_irreducible B.V
  obtain ⟨T,rel,hA,hD,hc⟩ := DVRMinimal.actual_six_jet r k B.matrices B.matrix_relations s t ht a d (a+d+1)
    ha hd (by omega) (by omega)
  obtain ⟨S,_,hs⟩ := realize_series B (AlgHom.id k _) a d hl T rel hA hD hc
  exact ⟨S,hs⟩

#print axioms GKDivisor.Jet.pole_to_series
end GKDivisor.Jet

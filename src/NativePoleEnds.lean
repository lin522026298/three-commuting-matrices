import PoleClosedJets
import PresentedWidth
import GraphToFamily
import ActualMinimalEnds

set_option linter.style.haveILetI false
noncomputable section
namespace GKDivisor.Jet
open PowerSeries DivisorG3 Module LinearMap
open Gerstenhaber.FourBlocks.PrimaryDecomposition Gerstenhaber.FourBlocks.MinimalSource
universe u
variable {k E : Type u} [Field k] [Field E] [Algebra k E] {r : ℕ} {s : GKGraph.selectCols r}
variable (D : SeriesPole k E r s)
abbrev SeriesPole.carrier := QP (D.T 0)
abbrev SeriesPole.native := nativeTriple (D.T 0) (D.T 1) (D.T 3) (D.T 2) (D.T 4)
  D.relations.y.symm D.relations.z.symm

theorem SeriesPole.native_facts (hr : 0<r) :
    FiniteDimensional E D.carrier ∧ IsNilpotent (D.native 0) ∧
    (∀ i j, Commute (D.native i) (D.native j)) ∧ finrank E D.carrier < finrank E (Generated D.native) ∧
    finrank E (D.native 0).ker + (redP (D.T 0)).rank = r := by
  have hbad := D.bad hr
  have H := (bad_iff_minor (D.T 0) (D.T 1) (D.T 3) (D.T 2) (D.T 4) (D.T 5) D.det_ne
    (by simpa using hr) D.relations.y.symm D.relations.z.symm D.relations.comm.symm).mp hbad
  obtain ⟨fin,hn,hc,hb⟩ := strict_to_native _ _ _ _ _ _ D.det_ne (by simpa using hr)
    D.relations.y.symm D.relations.z.symm D.relations.comm.symm H
  letI := fin
  exact ⟨fin,hn,hc,hb,actual_kernel_plus_residue_rank (D.T 0) (D.native 0) (fun _ => rfl)⟩

lemma matrix_zero_of_rank_zero {M : Matrix (Fin r) (Fin r) E} (h : M.rank = 0) : M = 0 := by
  apply Matrix.toLin'.injective
  rw [map_zero,Matrix.toLin'_apply']
  exact LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h)

theorem SeriesPole.minimal_width [IsAlgClosed E] [CharZero E] (hr : 0<r)
    (small : ∀ j<r, DVRMinimal.SafeEverywhere.{u} j) :
    finrank E (D.native 0).ker = r ∧ redP (D.T 0) = 0 := by
  obtain ⟨fin,hn,hc,bad,h⟩ := D.native_facts hr
  letI := fin
  have he : finrank E (D.native 0).ker = r := by
    by_contra ne
    have hl : finrank E (D.native 0).ker < r := by omega
    exact bad.not_ge (small _ hl E D.carrier D.native hc hn rfl)
  exact ⟨he, matrix_zero_of_rank_zero (by omega)⟩

theorem SeriesPole.minimal_nil_ends [IsAlgClosed E] [CharZero E] (hr : 0<r)
    (small : ∀ j<r, DVRMinimal.SafeEverywhere.{u} j) :
    letI : FiniteDimensional E D.carrier := (D.native_facts hr).1
    ∃ (chi : Fin 3 → E) (_ : chi 0 = 0) (hnil : ∀ i, IsNilpotent (shifted D.native chi i)),
      DVRMinimal.TwoEnds (FiniteNilTriple.of D.carrier (shifted D.native chi)
        (shifted_commute D.native chi (D.native_facts hr).2.2.1) hnil) ∧
      finrank E D.carrier < finrank E (Generated (shifted D.native chi)) := by
  letI : FiniteDimensional E D.carrier := (D.native_facts hr).1
  obtain ⟨_,hn,hc,bad,_⟩ := D.native_facts hr
  have he := (D.minimal_width hr small).1
  obtain ⟨chi,h0,hN,ends⟩ := DVRMinimal.least_bad_shifted_two_ends D.native hc hn bad
    (fun j hj => small j (he ▸ hj))
  exact ⟨chi,h0,hN,ends,(adjoin_shifted D.native chi) ▸ bad⟩

#print axioms GKDivisor.Jet.SeriesPole.native_facts
#print axioms GKDivisor.Jet.SeriesPole.minimal_width
#print axioms GKDivisor.Jet.SeriesPole.minimal_nil_ends
end GKDivisor.Jet

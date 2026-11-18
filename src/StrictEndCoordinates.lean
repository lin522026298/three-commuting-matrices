import LeastPresentedEnds
import GraphToFamily
import GKGraphActor
set_option linter.style.haveILetI false
noncomputable section
namespace GKEnds
open Module LinearMap DivisorG3 PowerSeries IsDiscreteValuationRing
open DVRMinimal GKGraph
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] (r : ℕ)

/-- Direct entry point: a genuine column selection on an arbitrary power-series presentation,
without a separately specified finite triple, minimality of the presentation, eigenvalues,
action on a pointed space, or any assumed rank/commutation of the constant matrices. -/
theorem strict_end_coordinates (S : Fin 6 → Mat (O k) r)
    (sr : Relations r S) (hp : (S 0).det≠0) (hr : 0 < r)
    (s : selectCols r) (hs : addVal (O k) (fullMinor r (S 0) (S 1) (S 2) s) <
      addVal (O k) ((S 0).det^(r-1)))
    (small : ∀ j<r, SafeEverywhere.{u} j) :
    r0 r S 0=0 ∧ ∃ a b : k, SubregularPair (r0 r S 1-a • 1) (r0 r S 2-b • 1) ∧
      SubregularPair (r0 r S 3-a • 1) (r0 r S 4-b • 1) := by
  have pos : 0<Fintype.card (Fin r) := by simpa using hr
  have hb := (bad_iff_selected r S hp sr hr).mpr ⟨s,hs⟩
  have low := (bad_iff_minor _ _ _ _ _ _ hp pos sr.y.symm sr.z.symm sr.comm.symm).mp hb
  obtain ⟨fin,hn,hc,bad'⟩ := strict_to_native _ _ _ _ _ _ hp pos sr.y.symm sr.z.symm sr.comm.symm low
  letI := fin
  exact least_presented_ends r S hp sr.y.symm sr.z.symm _ hc rfl (fun _ => rfl) (fun _ => rfl) hn bad' small
#print axioms strict_end_coordinates
end GKEnds

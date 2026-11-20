module

public import OrbitGauge

@[expose] public section
noncomputable section
set_option maxHeartbeats 45000
namespace GKGauge
open Module Matrix Finset
variable {k F : Type} [Field k] [Infinite k] [Field F] [Algebra k F] 

theorem finset_to_list (s : Finset F) (N : ℕ) (h : s.card ≤ N) :
    ∃ w : Fin N → F, ∀ L : IntermediateField k F, (∀ i, w i ∈ L) →
      IntermediateField.adjoin k (s : Set F) ≤ L := by
  classical
  let e : (s : Type) ≃ Fin s.card := Fintype.equivFinOfCardEq (by simp)
  let w : Fin N → F := fun i => if hi : i.val < s.card then (e.symm ⟨i.val,hi⟩).val else 0
  refine ⟨w,?_⟩
  intro L hL; apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  let j := e ⟨x,hx⟩
  let i : Fin N := ⟨j.val,lt_of_lt_of_le j.isLt h⟩
  have hmem := hL i
  change x ∈ L
  simpa only [w,i,dite_eq_left j.isLt,Fin.eta,j,e.symm_apply_apply] using hmem

end GKGauge
#print axioms GKGauge.finset_to_list

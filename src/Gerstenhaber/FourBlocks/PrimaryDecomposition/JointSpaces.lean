module

public import Gerstenhaber.FourBlocks.PrimaryDecomposition.Invariant
public import Gerstenhaber.FourBlocks.MinimalSource.BlockClosure

/-! The literal simultaneous maximal generalized eigenspaces of a
commuting family. Their finite support, full direct sum, shifted
nilpotence and inherited shifted-kernel bounds are constructed here. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Gerstenhaber.FourBlocks.PrimaryDecomposition

open Module LinearMap

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

def jointSpace (T : ι → Module.End K V) (chi : ι → K) : Submodule K V :=
  ⨅ i, (T i).maxGenEigenspace (chi i)

abbrev JointCharacters (T : ι → Module.End K V) :=
  {chi : ι → K // jointSpace T chi ≠ ⊥}

theorem jointSpace_stable (T : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j)) (chi : ι → K) (i : ι) :
    Set.MapsTo (T i) (jointSpace T chi) (jointSpace T chi) := by
  intro x hx
  change T i x ∈ jointSpace T chi
  apply (Submodule.mem_iInf (fun j => (T j).maxGenEigenspace (chi j))).mpr
  intro j
  exact Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) (chi j)
    ((iInf_le (fun j => (T j).maxGenEigenspace (chi j)) j) hx)

theorem jointSpace_independent (T : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j)) : iSupIndep (jointSpace T) := by
  exact Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo T
    (fun i j phi => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) phi)

@[instance_reducible]
noncomputable def jointCharactersFintype [FiniteDimensional K V]
    (T : ι → Module.End K V) (hcomm : ∀ i j, Commute (T i) (T j)) :
    Fintype (JointCharacters T) :=
  (jointSpace_independent T hcomm).fintypeNeBotOfFiniteDimensional

theorem jointSpace_iSup [FiniteDimensional K V] [IsAlgClosed K]
    (T : ι → Module.End K V) (hcomm : ∀ i j, Commute (T i) (T j)) :
    ⨆ chi, jointSpace T chi=⊤ := by
  exact Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo T
    (fun i j phi => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) phi)
    (fun i => (T i).iSup_maxGenEigenspace_eq_top)

theorem jointSpace_isInternal [FiniteDimensional K V] [IsAlgClosed K]
    (T : ι → Module.End K V) (hcomm : ∀ i j, Commute (T i) (T j))
    [DecidableEq (JointCharacters T)] :
    DirectSum.IsInternal (fun chi : JointCharacters T => jointSpace T chi.val) := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact (jointSpace_independent T hcomm).comp Subtype.val_injective
  · apply top_unique
    rw [←jointSpace_iSup T hcomm]
    apply iSup_le
    intro chi
    by_cases hchi : jointSpace T chi=⊥
    · rw [hchi]
      exact bot_le
    · exact le_iSup (fun chi : JointCharacters T => jointSpace T chi.val) ⟨chi,hchi⟩

theorem jointCharacters_iSup [FiniteDimensional K V] [IsAlgClosed K]
    (T : ι → Module.End K V) (hcomm : ∀ i j, Commute (T i) (T j)) :
    ⨆ chi : JointCharacters T, jointSpace T chi.val=⊤ := by
  classical
  exact (jointSpace_isInternal T hcomm).submodule_iSup_eq_top

theorem sum_finrank_jointSpace [FiniteDimensional K V] [IsAlgClosed K]
    (T : ι → Module.End K V) (hcomm : ∀ i j, Commute (T i) (T j))
    [Fintype (JointCharacters T)] :
    (∑ chi : JointCharacters T, finrank K (jointSpace T chi.val))=finrank K V := by
  classical
  let e := LinearEquiv.ofBijective
    (DirectSum.coeLinearMap (fun chi : JointCharacters T => jointSpace T chi.val))
    (jointSpace_isInternal T hcomm)
  have h := e.finrank_eq
  rw [Module.finrank_directSum] at h
  exact h

theorem restricted_commute (T : ι → Module.End K V) (P : Submodule K V)
    (hP : ∀ i, Set.MapsTo (T i) P P) (hcomm : ∀ i j, Commute (T i) (T j)) (i j : ι) :
    Commute (restricted T P hP i) (restricted T P hP j) :=
  LinearMap.restrict_commute (hcomm i j) (hP i) (hP j)

theorem shifted_commute (T : ι → Module.End K V) (chi : ι → K)
    (hcomm : ∀ i j, Commute (T i) (T j)) (i j : ι) :
    Commute (shifted T chi i) (shifted T chi j) := by
  change Commute (T i-algebraMap K (Module.End K V) (chi i))
    (T j-algebraMap K (Module.End K V) (chi j))
  exact ((hcomm i j).sub_left (Algebra.commute_algebraMap_left (chi i) (T j))).sub_right
    (Algebra.commute_algebraMap_right (chi j) (T i-algebraMap K (Module.End K V) (chi i)))

theorem joint_shift_nilpotent [FiniteDimensional K V]
    (T : ι → Module.End K V) (hcomm : ∀ i j, Commute (T i) (T j))
    (chi : ι → K) (i : ι) :
    IsNilpotent (shifted (restricted T (jointSpace T chi) (jointSpace_stable T hcomm chi)) chi i) := by
  have hs : Set.MapsTo (T i-chi i • (1 : Module.End K V)) (jointSpace T chi) (jointSpace T chi) := by
    intro x hx
    exact (jointSpace T chi).sub_mem (jointSpace_stable T hcomm chi i hx)
      ((jointSpace T chi).smul_mem (chi i) hx)
  have heq : shifted (restricted T (jointSpace T chi) (jointSpace_stable T hcomm chi)) chi i =
      (T i-chi i • (1 : Module.End K V)).restrict hs := by ext x; rfl
  rw [heq]
  exact Module.End.isNilpotent_restrict_of_le (iInf_le _ i)
    ((T i).isNilpotent_restrict_maxGenEigenspace_sub_algebraMap (chi i))

theorem joint_shift_kernel_le [FiniteDimensional K V]
    (T : ι → Module.End K V) (hcomm : ∀ i j, Commute (T i) (T j))
    (chi : ι → K) (i : ι) :
    finrank K (shifted (restricted T (jointSpace T chi) (jointSpace_stable T hcomm chi)) chi i).ker ≤
      finrank K (T i-chi i • 1).ker := by
  apply Gerstenhaber.FourBlocks.MinimalSource.finrank_ker_le_of_injective_intertwining
    _ _ (jointSpace T chi).subtype (jointSpace T chi).injective_subtype
  intro x
  rfl

end Gerstenhaber.FourBlocks.PrimaryDecomposition

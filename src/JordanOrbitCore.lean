module

public import FiniteList
public import JordanBudget
public import JordanLower

@[expose] public section
noncomputable section
set_option maxHeartbeats 45000
namespace GKGauge
open JordanPrimitive Module Matrix Finset
variable {k F : Type} [Field k] [Infinite k] [Field F] [Algebra k F] {d : ℕ} (m : Fin d → ℕ)

def jCentEquiv :
    Cent (K:=F) m ≃ₗ[F] intertwiner (matrixJ (K:=F) m) (matrixJ m) where
  toFun a := ⟨LinearMap.toMatrixAlgEquiv (coordBasis m) a.val,
    ((commJ m a).map (LinearMap.toMatrixAlgEquiv (coordBasis m)).toAlgHom).eq.symm⟩
  invFun a := decode m a.val (show Commute a.val (matrixJ m) from a.property.symm)
  left_inv a := by apply Subtype.ext; exact AlgEquiv.symm_apply_apply _ _
  right_inv a := by apply Subtype.ext; exact encode_decode m a.val _
  map_add' a b := by apply Subtype.ext; exact (LinearMap.toMatrixAlgEquiv (coordBasis (K:=F) m)).map_add a.val b.val
  map_smul' t a := by apply Subtype.ext; exact (LinearMap.toMatrixAlgEquiv (coordBasis (K:=F) m)).toLinearEquiv.map_smul t a.val

omit [Infinite k] in
theorem jordan_entries_base : ∀ i j, (matrixJ (K:=F) m) i j ∈ (algebraMap k F).range := by
  rintro ⟨h,p,a⟩ ⟨l,q,b⟩
  by_cases he : h=l
  · subst l; rw [matrixJ_apply]; split
    · exact (algebraMap k F).range.one_mem
    · exact (algebraMap k F).range.zero_mem
  · rw [matrixJ_other m h l p q a b he]
    exact (algebraMap k F).range.zero_mem

theorem count_le_c : Fintype.card (Ix m) ≤ finrank F (Cent (K:=F) m) := by
  rw [← Module.finrank_eq_card_basis (coordBasis (K:=F) m)]
  exact total_le_centralizer m

/-- One arbitrary nilpotent matrix in an actual grouped Jordan similarity class.
The only remaining input to cover all nilpotents is existence of the Jordan basis. -/
theorem single_given_shape (A : Matrix (Ix m) (Ix m) F)
    (h : ∃ H : Matrix _ _ F, H.det ≠ 0 ∧ A*H=H*matrixJ m) :
    FieldParams (k:=k) A ((Fintype.card (Ix m))^2-Fintype.card (Ix m)) := by
  obtain ⟨s,H,hs,_,_,_,hA⟩ := orbit_parameters A _ h (jordan_entries_base (k:=k) m)
  rw [← (jCentEquiv (F:=F) m).finrank_eq,←pow_two] at hs
  have hN := count_le_c (F:=F) m
  obtain ⟨w,hw⟩ := finset_to_list (k:=k) s _ (hs.trans (Nat.sub_le_sub_left hN _))
  exact ⟨w,fun L hi i j => hw L hi (hA i j)⟩
end GKGauge
#print axioms GKGauge.jCentEquiv
#print axioms GKGauge.count_le_c
#print axioms GKGauge.single_given_shape

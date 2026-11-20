module

public import JordanPrimitive

@[expose] public section

noncomputable section
namespace JordanPrimitive
open Module
variable {K : Type*} [Field K] {H : ℕ} (m : Fin H → ℕ)

/-- The truncation is literal coordinate deletion; its inverse pads with zeros. -/
def kernelCoordinates (k : ℕ) : LinearMap.ker (J (K:=K) m ^ k) ≃ₗ[K]
    ((h : Fin H) → Fin (min k (h.val+1)) → Fin (m h) → K) where
  toFun v h j := v.1 h ⟨j.val,lt_of_lt_of_le j.isLt (min_le_right _ _)⟩
  invFun w := ⟨fun h j => if hj : j.val < k then w h ⟨j.val,lt_min hj j.isLt⟩ else 0,by
    change (J m ^ k) _ = 0
    funext h j
    rw [Jpow]
    split_ifs with hc he
    · change j.val+k < k at he
      omega
    · rfl
    · rfl⟩
  left_inv v := by
    apply Subtype.ext
    funext h j
    by_cases hc : j.val < k
    · simp [hc]
    · have hk : k ≤ j.val := Nat.le_of_not_gt hc
      let p : Fin (h.val+1) := ⟨j.val-k,by have := j.isLt; omega⟩
      have hp : p.val+k = j.val := Nat.sub_add_cancel hk
      have hv : (J m ^ k) v.1 = 0 := v.2
      have he := congrFun (congrFun hv h) p
      rw [Jpow] at he
      simpa [hc,hp,j.isLt] using he.symm
  right_inv w := by funext h j; simp [lt_of_lt_of_le j.isLt (min_le_left _ _)]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem kernel_dimension (k : ℕ) : finrank K (LinearMap.ker (J (K:=K) m ^ k)) =
      ∑ h, min k (h.val+1) * m h := by
  rw [(kernelCoordinates (K:=K) m k).finrank_eq,finrank_pi_fintype]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [finrank_pi_fintype]
  simp

end JordanPrimitive

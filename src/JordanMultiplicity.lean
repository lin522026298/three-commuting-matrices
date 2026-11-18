import JordanPrimitive
noncomputable section
namespace JordanPrimitive
open Module
variable {K : Type*} [Field K] {H : ℕ} (m : Fin H → ℕ)

def socEmbed : ((h : Fin H) → Fin (m h) → K) →ₗ[K] V K m :=
  LinearMap.pi (fun h => (LinearMap.single K (fun _ : Fin (h.val+1) => Fin (m h) → K) 0).comp
    (LinearMap.proj h))

def ker_equiv : (LinearMap.ker (J (K:=K) m)) ≃ₗ[K] ((h : Fin H) → Fin (m h) → K) where
  toFun v h := v.1 h 0
  invFun w := ⟨socEmbed m w,by
    change J m (socEmbed m w) = 0
    apply ((fl_iff m 0 _).mp _).1
    intro h j hj
    have hj' : j ≠ 0 := fun e => by subst j; simp at hj
    simp [socEmbed,Pi.single_eq_of_ne hj']⟩
  left_inv v := by
    apply Subtype.ext
    funext h j
    by_cases hz : j=0
    · subst j; simp [socEmbed]
    · have hc := (fl_iff m 0 v.1).mpr ⟨v.2,v.1,by simp⟩
      have he := hc h j (Or.inl (fun e => hz (Fin.ext e)))
      simp [socEmbed,Pi.single_eq_of_ne hz,he]
  right_inv w := by funext h; simp [socEmbed]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem number_of_blocks_is_nullity :
    finrank K (LinearMap.ker (J (K:=K) m)) = ∑ h, m h := by
  rw [(ker_equiv (K:=K) m).finrank_eq,finrank_pi_fintype]
  simp

theorem total_dimension :
    finrank K (V K m) = ∑ h, (h.val+1)*m h := by
  change finrank K ((h : Fin H) → Fin (h.val+1) → (Fin (m h) → K)) = _
  rw [finrank_pi_fintype]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [finrank_pi_fintype]
  simp

end JordanPrimitive

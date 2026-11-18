import JordanStrings
import JordanKernel
noncomputable section
namespace JordanPrimitive
open Module
variable {K : Type*} [Field K] {H : ℕ} (m : Fin H → ℕ)

/-- The full centralizer dimension; no geometric orbit or dimension hypotheses. -/
theorem centralizer_dimension : finrank K (Cent (K:=K) m) =
    ∑ h, m h * (∑ l, min (h.val+1) (l.val+1) * m l) := by
  rw [(coefficientEquiv (K:=K) m).finrank_eq]
  change finrank K ((h : Fin H) → Fin (m h) → LinearMap.ker (J (K:=K) m ^ (h.val+1))) = _
  rw [finrank_pi_fintype]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [finrank_pi_fintype]
  simp [kernel_dimension]

end JordanPrimitive

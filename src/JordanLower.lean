module

public import JordanDimension
public import JordanMultiplicity

@[expose] public section
noncomputable section
namespace JordanPrimitive
open Module
variable {K : Type*} [Field K] {H : ℕ} (m : Fin H → ℕ)

/-- The centralizer has at least r dimensions, so the orbit gauge for a
single nilpotent automatically saves r slots. -/
theorem total_le_centralizer : finrank K (V K m) ≤ finrank K (Cent (K:=K) m) := by
  rw [total_dimension,centralizer_dimension]
  apply Finset.sum_le_sum
  intro h _
  have hh := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun l : Fin H => min (h.val+1) (l.val+1) * m l)
    (fun l _ => Nat.zero_le _) (Finset.mem_univ h)
  simp only [min_self] at hh
  by_cases hz : m h = 0
  · simp [hz]
  · have hp : 1 ≤ m h := Nat.one_le_iff_ne_zero.mpr hz
    calc
      (h.val+1)*m h ≤ 1 * ∑ l, min (h.val+1) (l.val+1) * m l := by simpa using hh
      _ ≤ _ := Nat.mul_le_mul_right _ hp

end JordanPrimitive

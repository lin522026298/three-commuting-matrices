module

public import JordanPrimitive

@[expose] public section

/-! This stronger converse is not required by the divisor count.  It verifies that no
non-diagonal dependence on intermediate strings is being ignored. -/
noncomputable section
namespace JordanPrimitive
open Module
variable {K : Type*} [Field K] {H : ℕ} (m : Fin H → ℕ)

theorem kernel_push (z : Cent (K:=K) m) (hz : primitive m z = 0)
    (k : ℕ) (v : V K m) (hv : Fl m k v) : Fl m (k+1) (z.1 v) := by
  have hc := map_fl m z k hv
  intro h j hj
  by_cases he : h.val = k
  · by_cases hj0 : j = 0
    · subst j; subst k
      rw [eval_fl m z h v hv]
      have hp : part m z h = 0 := congrFun hz h
      rw [hp]; rfl
    · exact hc h j (Or.inl (fun e => hj0 (Fin.ext e)))
  · apply hc
    rcases hj with hj|hj
    · exact Or.inl hj
    · exact Or.inr (by omega)

theorem kernel_kills_socle (z : Cent (K:=K) m) (hz : primitive m z = 0)
    (v : V K m) (hv : J m v = 0) : (z.1 ^ H) v = 0 := by
  have hi (k : ℕ) : Fl m k ((z.1 ^ k) v) := by
    induction k with
    | zero =>
      rw [pow_zero]
      apply (fl_iff m 0 v).mpr
      exact ⟨hv,v,by simp⟩
    | succ k ih =>
      rw [pow_succ',mul_apply_eq_comp]
      exact kernel_push m z hz k _ ih
  funext h j
  exact hi H h j (Or.inr h.isLt)

/-- If an endomorphism P centralizes a nilpotent and kills its kernel,
then P^k kills the kernel of the kth power. -/
theorem commuting_kills_kernel_pow {M : Type*} [AddCommGroup M] [Module K M]
    (P T : Module.End K M) (hPT : Commute P T)
    (hker : ∀ v, T v = 0 → P v = 0) (k : ℕ) (v : M) (hv : (T^k) v = 0) :
    (P^k) v = 0 := by
  induction k generalizing v with
  | zero => simpa using hv
  | succ k ih =>
    rw [pow_succ,mul_apply_eq_comp] at hv
    rw [pow_succ',mul_apply_eq_comp]
    apply hker
    calc
      T ((P^k) v) = (P^k) (T v) := congrArg (fun f : Module.End K M => f v)
        (hPT.pow_left k).eq.symm
      _ = 0 := ih _ hv

theorem kernel_nilpotent_bound (z : Cent (K:=K) m) (hz : primitive m z = 0) :
    z.1 ^ (H*H) = 0 := by
  rw [pow_mul]
  apply LinearMap.ext
  intro v
  apply commuting_kills_kernel_pow _ (J m) ((commJ m z).pow_left H)
    (kernel_kills_socle m z hz) H v
  funext h j
  rw [Jpow, dite_eq_right (by have := h.isLt; omega)]
  rfl

/-- This is an iff for the original endomorphism and every primitive block. -/
theorem nilpotent_iff_blocks (z : Cent (K:=K) m) :
    IsNilpotent z.1 ↔ ∀ h, IsNilpotent (part m z h) := by
  refine ⟨part_nilpotent m z,?_⟩
  intro hp
  choose e he using hp
  let N := ∑ h, e h
  have hzero : primitive m (z^N) = 0 := by
    rw [map_pow]
    funext h
    change ((primitive m z) h)^N = 0
    apply pow_eq_zero_of_le (Finset.single_le_sum (fun i _ => Nat.zero_le (e i))
      (Finset.mem_univ h)) (he h)
  refine ⟨N*(H*H),?_⟩
  rw [pow_mul]
  exact kernel_nilpotent_bound m (z^N) hzero

end JordanPrimitive

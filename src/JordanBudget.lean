module

public import JordanLiteralParameters

@[expose] public section

/-! Adapter only: the unconditioned literal free-coordinate theorem is in
JordanLiteralParameters; the separate single-nilpotent-matrix orbit count is
here *explicitly* an input, not a theorem smuggled into the centralizer proof. -/
noncomputable section
namespace JordanPrimitive
open Module
variable {k K : Type*} [Field k] [Field K] [Algebra k K] {H : ℕ} (m : Fin H → ℕ)

def FieldParams {I : Type*} (Z : Matrix I I K) (n : ℕ) : Prop :=
  ∃ w : Fin n → K, ∀ S : IntermediateField k K, (∀ i, w i ∈ S) → ∀ i j, Z i j ∈ S

theorem fixed_shape_budget_of_single_matrix
    (hsingle : ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) K),
      IsNilpotent Q → FieldParams (k:=k) Q (n^2-n))
    (Z : Matrix (Ix m) (Ix m) K) (hZ : Commute Z (matrixJ m)) (hn : IsNilpotent Z) :
    FieldParams (k:=k) Z (finrank K (Cent (K:=K) m) - ∑ h, m h) := by
  classical
  obtain ⟨u,hu⟩ := literal_parameter_list m Z hZ
  have hblock := (matrix_block_nilpotent_iff m Z hZ).mp hn
  choose w hw using fun h => hsingle (m h) (rawBlock m Z h) (hblock h)
  let c := finrank K (Cent (K:=K) m)
  let I := Fin (c - ∑ h, m h ^ 2) ⊕ ((h : Fin H) × Fin ((m h)^2 - m h))
  have hm (h : Fin H) : m h ≤ m h ^ 2 := by
    by_cases hv : m h = 0
    · simp [hv]
    · have hp : 0 < m h := Nat.pos_of_ne_zero hv; nlinarith
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hm i)
  have hc := primitive_rank_nullity (K:=K) m
  have hI : Fintype.card I = c - ∑ h, m h := by
    simp only [I,Fintype.card_sum,Fintype.card_fin,Fintype.card_sigma]
    rw [Finset.sum_tsub_distrib _ (fun h _ => hm h)]
    dsimp [c]; omega
  let e : I ≃ Fin (c - ∑ h, m h) := Fintype.equivFinOfCardEq hI
  let raw : I → K := Sum.elim u (fun t => w t.1 t.2)
  refine ⟨fun i => raw (e.symm i),?_⟩
  intro S hS
  have hall (i : I) : raw i ∈ S := by simpa using hS (e i)
  apply hu S S.zero_mem (fun i => hall (Sum.inl i))
  intro h
  apply hw h S
  intro i
  exact hall (Sum.inr ⟨h,i⟩)

end JordanPrimitive

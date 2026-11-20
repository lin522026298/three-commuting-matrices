module

public import FieldReduction
public import FullG3

@[expose] public section
noncomputable section
namespace G3Scalar
open Module

theorem field_small (k : Type) [Field k] (n : ℕ)
    (A : Fin 3 → Matrix (Fin n) (Fin n) k) (hc : ∀ i j, Commute (A i) (A j)) :
    finrank k (Algebra.adjoin k (Set.range A)) ≤ n :=
  field_small_of_closed G3Assembly.matrix_triple_bound k n A hc

theorem field_triple_bound (K : Type*) [Field K] (n : ℕ)
    (A : Fin 3 → Matrix (Fin n) (Fin n) K) (hc : ∀ i j, Commute (A i) (A j)) :
    finrank K (Algebra.adjoin K (Set.range A)) ≤ n :=
  field_triple_bound_of_closed G3Assembly.matrix_triple_bound K n A hc

/-- Literal three-named-matrix version, with no nonzero size assumption. -/
theorem field_three_matrices {K : Type*} [Field K] {n : ℕ}
    (X Y Z : Matrix (Fin n) (Fin n) K) (hxy : Commute X Y) (hxz : Commute X Z)
    (hyz : Commute Y Z) : finrank K (Algebra.adjoin K ({X,Y,Z} : Set _)) ≤ n := by
  let A : Fin 3 → Matrix (Fin n) (Fin n) K := ![X,Y,Z]
  have comm (i j : Fin 3) : Commute (A i) (A j) := by
    fin_cases i <;> fin_cases j <;>
      first | exact Commute.refl _ | exact hxy | exact hxz | exact hyz | exact hxy.symm | exact hxz.symm | exact hyz.symm
  have range : Set.range A = ({X,Y,Z} : Set _) := by
    ext v
    constructor
    · rintro ⟨i,rfl⟩; fin_cases i <;> simp [A]
    · rintro (h|h|h)
      · exact ⟨0,h.symm⟩
      · exact ⟨1,h.symm⟩
      · exact ⟨2,(Set.mem_singleton_iff.mp h).symm⟩
  exact range ▸ field_triple_bound K n A comm

#print axioms field_small
#print axioms field_triple_bound
#print axioms field_three_matrices
end G3Scalar

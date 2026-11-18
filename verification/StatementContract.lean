import FullG3
/-- Independent client in ordinary multiplication notation, with no project-defined predicate. -/
theorem all_complex_matrices_contract :
    ∀ (n : ℕ) (A B C : Matrix (Fin n) (Fin n) ℂ),
      A * B = B * A → B * C = C * B → C * A = A * C →
        Module.finrank ℂ (Algebra.adjoin ℂ ({A,B,C} : Set (Matrix (Fin n) (Fin n) ℂ))) ≤ n := by
  intro n A B C eAB eBC eCA
  exact G3Assembly.complex_three_matrices A B C eAB eCA.symm eBC
/-- Fully spelled out Type-0 algebraically closed characteristic-zero contract. -/
theorem all_closed_char_zero_contract (k : Type) [Field k] [IsAlgClosed k] [CharZero k] :
    ∀ (n : ℕ) (f : Fin 3 → Matrix (Fin n) (Fin n) k),
      (∀ i j, f i * f j = f j * f i) →
      Module.finrank k (Algebra.adjoin k (Set.range f)) ≤ n := by
  intro n f h
  exact G3Assembly.matrix_triple_bound k n f h
#print axioms all_complex_matrices_contract
#print axioms all_closed_char_zero_contract
#print axioms G3Assembly.complex_three_matrices

/-- The finite dimension in the conclusion is not the default value of finrank
on an infinite-dimensional module. Every candidate subalgebra lives in a finite
matrix space. In particular no independent family of more than n elements fits. -/
theorem independent_columns_contract (n d : ℕ) (A B C : Matrix (Fin n) (Fin n) ℂ)
    (hAB : A*B=B*A) (hBC : B*C=C*B) (hCA : C*A=A*C)
    (f : (Fin d → ℂ) →ₗ[ℂ] (Algebra.adjoin ℂ ({A,B,C} : Set _)))
    (hf : Function.Injective f) : d ≤ n := by
  have _ : FiniteDimensional ℂ (Algebra.adjoin ℂ ({A,B,C} : Set _)) := inferInstance
  have low := LinearMap.finrank_le_finrank_of_injective hf
  rw [Module.finrank_pi,Fintype.card_fin] at low
  exact low.trans (all_complex_matrices_contract n A B C hAB hBC hCA)
#print axioms independent_columns_contract

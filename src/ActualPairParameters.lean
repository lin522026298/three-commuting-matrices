module

public import PairFromModels
public import JordanTrueNullity

@[expose] public section
noncomputable section
namespace GKGauge
open JordanPrimitive ActualJordan Matrix Module
variable {k F : Type} [Field k] [Infinite k] [Field F] [Algebra k F]
theorem actual_jordan_models (F : Type) [Field F] : JordanModels F :=
  fun _ U h => ActualJordan.exists_matrix_jordan_with_nullity U h
theorem nil_matrix_parameters (n : ℕ) (Q : Matrix (Fin n) (Fin n) F) (hn : IsNilpotent Q) :
    FieldParams (k:=k) Q (n^2-n) :=
  nil_matrix_parameters_of_jordan (actual_jordan_models F) _ Q hn
/-- The two given commuting nilpotent matrices have a common actual parameter set.
No assumed Jordan form, dimensions of varieties, parameter spaces, or similarity matrices. -/
theorem subregular_pair_parameters {n : ℕ} (U V : Matrix (Fin n) (Fin n) F)
    (h : Commute U V) (hn : IsNilpotent U) (hz : IsNilpotent V)
    (hk : 2 ≤ finrank F U.mulVecLin.ker) :
    ∃ s : Finset F, s.card ≤ n*n-2 ∧
      (∀ i j, U i j ∈ IntermediateField.adjoin k (s : Set F)) ∧
      (∀ i j, V i j ∈ IntermediateField.adjoin k (s : Set F)) :=
  subregular_pair_parameters_of_jordan (actual_jordan_models F) U V h hn hz hk
end GKGauge
#print axioms GKGauge.actual_jordan_models
#print axioms GKGauge.nil_matrix_parameters
#print axioms GKGauge.subregular_pair_parameters

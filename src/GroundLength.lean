import DVRScalar
import Mathlib.RingTheory.LocalRing.Length
noncomputable section
namespace DivisorG3
open Module IsLocalRing PowerSeries
variable (k : Type*) [Field k]
theorem same_residue : Function.Surjective (algebraMap (ResidueField k) (ResidueField (O k))) := by
  intro a
  obtain ⟨f,rfl⟩ := residue_surjective a
  refine ⟨residue k (constantCoeff f),?_⟩
  rw [ResidueField.algebraMap_residue]
  apply Ideal.Quotient.eq.mpr
  rw [←PowerSeries.ker_coeff_eq_max_ideal]
  change constantCoeff (C (constantCoeff f)-f)=0
  simp
theorem actual_length (W : Type*) [AddCommGroup W] [Module k W] [Module (O k) W]
    [IsScalarTower k (O k) W] [Module.Finite k W] : length (O k) W = finrank k W := by
  have h := IsLocalRing.length_restrictScalars k (O k) W
  rw [Module.length_eq_of_surjective (M:=ResidueField (O k)) (same_residue k)] at h
  simpa [Module.length_eq_finrank] using h.symm
#print axioms actual_length
end DivisorG3

module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Data.Fin.Rev
public import Gerstenhaber.DP2.LinearRow.RelativeDuality

/-!
The coefficient Frobenius functional of an arbitrary monic polynomial quotient.
Its multiplication pairing is proved bijective by a unit triangular Gram matrix.
No nondegeneracy hypothesis or domain hypothesis on the coefficient ring is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Gerstenhaber.DP2.LinearRow

open Module Polynomial

variable {B : Type*} [CommRing B] [Nontrivial B] {P : B[X]}

/-- Coefficient of X^(degree P-1) in the canonical monic remainder. -/
def monicCoeffTrace (hP : P.Monic) : AdjoinRoot P →ₗ[B] B :=
  (Polynomial.lcoeff B (P.natDegree-1)).comp (AdjoinRoot.modByMonicHom hP)

omit [Nontrivial B] in
@[simp] theorem monicCoeffTrace_apply (hP : P.Monic) (a : AdjoinRoot P) :
    monicCoeffTrace hP a =
      (AdjoinRoot.modByMonicHom hP a).coeff (P.natDegree-1) := rfl

omit [Nontrivial B] in
@[simp] theorem monicCoeffTrace_mk (hP : P.Monic) (q : B[X]) :
    monicCoeffTrace hP (AdjoinRoot.mk P q) =
      (q %ₘ P).coeff (P.natDegree-1) := rfl

/-- The actual B-linear multiplication pairing, with no perfectness assumption. -/
def monicFrobeniusPairing (hP : P.Monic) :
    AdjoinRoot P →ₗ[B] Module.Dual B (AdjoinRoot P) where
  toFun a :=
    { toFun := fun b => monicCoeffTrace hP (a*b)
      map_add' := by intro b c; simp [mul_add]
      map_smul' := by intro b c; simp }
  map_add' a b := by ext c; simp [add_mul]
  map_smul' b a := by ext c; simp

omit [Nontrivial B] in
@[simp] theorem monicFrobeniusPairing_apply (hP : P.Monic) (a b : AdjoinRoot P) :
    monicFrobeniusPairing hP a b = monicCoeffTrace hP (a*b) := rfl

theorem monicCoeffTrace_root_pow (hP : P.Monic) {n : ℕ} (hn : n<P.natDegree) :
    monicCoeffTrace hP (AdjoinRoot.root P ^ n) =
      if P.natDegree-1=n then 1 else 0 := by
  have hpow : AdjoinRoot.mk P (X^n) = AdjoinRoot.root P ^ n := by simp
  rw [← hpow, monicCoeffTrace_mk,
    (Polynomial.modByMonic_eq_self_iff hP).mpr]
  · exact Polynomial.coeff_X_pow _ _
  · rw [Polynomial.degree_X_pow, Polynomial.degree_eq_natDegree hP.ne_zero]
    exact_mod_cast hn

theorem monicCoeffTrace_root_top (hP : P.Monic) (hd : 0<P.natDegree) :
    monicCoeffTrace hP (AdjoinRoot.root P ^ (P.natDegree-1))=1 := by
  rw [monicCoeffTrace_root_pow hP (by omega)]
  simp

def monicPowerBasis (hP : P.Monic) : Basis (Fin P.natDegree) B (AdjoinRoot P) :=
  (AdjoinRoot.powerBasis' hP).basis

def monicReversePowerBasis (hP : P.Monic) : Basis (Fin P.natDegree) B (AdjoinRoot P) :=
  (monicPowerBasis hP).reindex Fin.revPerm

omit [Nontrivial B] in
@[simp] theorem monicPowerBasis_apply (hP : P.Monic) (i : Fin P.natDegree) :
    monicPowerBasis hP i = AdjoinRoot.root P ^ i.val := by
  exact (AdjoinRoot.powerBasis' hP).basis_eq_pow i

omit [Nontrivial B] in
@[simp] theorem monicReversePowerBasis_apply (hP : P.Monic) (i : Fin P.natDegree) :
    monicReversePowerBasis hP i = AdjoinRoot.root P ^ i.rev.val := by
  simp [monicReversePowerBasis, Basis.reindex_apply, Fin.revPerm_symm]

/-- Gram matrix after reversing one of the power bases. -/
def monicReverseGram (hP : P.Monic) : Matrix (Fin P.natDegree) (Fin P.natDegree) B :=
  fun i j => monicCoeffTrace hP (AdjoinRoot.root P ^ (i.val+j.rev.val))

theorem monicReverseGram_lowerTriangular (hP : P.Monic) :
    (monicReverseGram hP).IsLowerTriangular := by
  intro i j hij
  have hij' : i.val<j.val := hij
  have hsum : i.val+j.rev.val<P.natDegree-1 := by
    simp only [Fin.val_rev]
    omega
  change monicCoeffTrace hP (AdjoinRoot.root P ^ (i.val+j.rev.val))=0
  rw [monicCoeffTrace_root_pow hP (by omega)]
  exact ite_eq_right (ne_of_gt hsum)

@[simp] theorem monicReverseGram_diagonal (hP : P.Monic) (i : Fin P.natDegree) :
    monicReverseGram hP i i=1 := by
  have hsum : i.val+i.rev.val=P.natDegree-1 := by
    simp only [Fin.val_rev]
    omega
  change monicCoeffTrace hP (AdjoinRoot.root P ^ (i.val+i.rev.val))=1
  rw [monicCoeffTrace_root_pow hP (by omega)]
  exact ite_eq_left hsum.symm

theorem monicReverseGram_det (hP : P.Monic) :
    (monicReverseGram hP).det=1 := by
  rw [Matrix.det_of_isLowerTriangular _ (monicReverseGram_lowerTriangular hP)]
  simp

omit [Nontrivial B] in
theorem monicFrobeniusPairing_matrix (hP : P.Monic) :
    LinearMap.toMatrix (monicReversePowerBasis hP) (monicPowerBasis hP).dualBasis
      (monicFrobeniusPairing hP) = monicReverseGram hP := by
  ext i j
  rw [LinearMap.toMatrix_apply, Basis.dualBasis_repr,
    monicFrobeniusPairing_apply, monicReversePowerBasis_apply, monicPowerBasis_apply,
    ← pow_add]
  change monicCoeffTrace hP (AdjoinRoot.root P ^ (j.rev.val+i.val)) =
    monicCoeffTrace hP (AdjoinRoot.root P ^ (i.val+j.rev.val))
  rw [Nat.add_comm]

/-- The coefficient multiplication pairing is genuinely perfect over any commutative base. -/
theorem monicFrobeniusPairing_bijective (hP : P.Monic) :
    Function.Bijective (monicFrobeniusPairing hP) := by
  have hdet : IsUnit (LinearMap.toMatrix (monicReversePowerBasis hP)
      (monicPowerBasis hP).dualBasis (monicFrobeniusPairing hP)).det := by
    rw [monicFrobeniusPairing_matrix, monicReverseGram_det]
    exact isUnit_one
  exact (LinearEquiv.ofIsUnitDet hdet).bijective

/-- The actual linear equivalence supplied by the coefficient Frobenius pairing. -/
def monicFrobeniusEquiv (hP : P.Monic) :
    AdjoinRoot P ≃ₗ[B] Module.Dual B (AdjoinRoot P) :=
  LinearEquiv.ofBijective (monicFrobeniusPairing hP) (monicFrobeniusPairing_bijective hP)

@[simp] theorem monicFrobeniusEquiv_apply (hP : P.Monic) (a b : AdjoinRoot P) :
    monicFrobeniusEquiv hP a b=monicCoeffTrace hP (a*b) := rfl

omit [Nontrivial B] in
theorem monicFrobeniusPairing_eq_frobeniusPairing (hP : P.Monic) :
    monicFrobeniusPairing hP = frobeniusPairing (monicCoeffTrace hP) := by
  ext a b
  rfl

/-- The proved monic pairing supplies the hypothesis of the generic adjunction API. -/
theorem frobeniusPairing_monicCoeffTrace_bijective (hP : P.Monic) :
    Function.Bijective (frobeniusPairing (monicCoeffTrace hP)) := by
  rw [← monicFrobeniusPairing_eq_frobeniusPairing]
  exact monicFrobeniusPairing_bijective hP

end Gerstenhaber.DP2.LinearRow

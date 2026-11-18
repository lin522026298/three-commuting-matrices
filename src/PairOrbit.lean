import JordanOrbitCore
noncomputable section
namespace GKGauge
open JordanPrimitive Module Matrix Finset
variable {k F : Type} [Field k] [Infinite k] [Field F] [Algebra k F] {d : ℕ} (m : Fin d → ℕ)

theorem pair_given_shape (hsingle : ∀ (a : ℕ) (Q : Matrix (Fin a) (Fin a) F),
      IsNilpotent Q → FieldParams (k:=k) Q (a^2-a))
    (A B : Matrix (Ix m) (Ix m) F)
    (hc : Commute A B) (hB : IsNilpotent B)
    (hg : ∃ E : Matrix _ _ F, E.det ≠ 0 ∧ A*E=E*matrixJ m) :
    ∃ u : Finset F, u.card ≤ Fintype.card (Ix m)^2-∑ h, m h ∧
      (∀ i j, A i j ∈ IntermediateField.adjoin k (u : Set F)) ∧
      (∀ i j, B i j ∈ IntermediateField.adjoin k (u : Set F)) := by
  classical
  obtain ⟨s,H,hs,hdet,he,hH,hA⟩ := orbit_parameters A _ hg (jordan_entries_base (k:=k) m)
  have h1 := Matrix.nonsing_inv_mul H (isUnit_iff_ne_zero.mpr hdet)
  have h2 := Matrix.mul_nonsing_inv H (isUnit_iff_ne_zero.mpr hdet)
  let Z := H⁻¹ * B * H
  have hb : B * H = H * Z := by
    dsimp [Z]; simp only [←mul_assoc,h2,one_mul]
  have hj : matrixJ (K:=F) m = H⁻¹ * A * H := by
    rw [mul_assoc,he,←mul_assoc,h1,one_mul]
  have clean (X Y : Matrix (Ix m) (Ix m) F) :
      H⁻¹ * X * H * (H⁻¹ * Y * H) = H⁻¹ * (X*Y) * H := by
    calc
      _ = (H⁻¹ * X) * (H*H⁻¹) * Y * H := by simp only [mul_assoc]
      _ = _ := by rw [h2,mul_one]; simp only [mul_assoc]
  have hcomm : Commute Z (matrixJ m) := by
    rw [hj]; change H⁻¹ * B * H * (H⁻¹ * A * H) = H⁻¹ * A * H * (H⁻¹ * B * H)
    calc
      _ = H⁻¹ * (B*A) * H := by rw [clean]
      _ = H⁻¹ * (A*B) * H := by rw [hc.eq]
      _ = _ := by rw [clean]
  have hnil : IsNilpotent Z := by
    obtain ⟨t,ht⟩ := hB
    have hgpow (n : ℕ) : Z^n = H⁻¹*B^n*H := by
      induction n with
      | zero => simp [h1]
      | succ n ih =>
        rw [pow_succ,pow_succ,ih]; dsimp [Z]
        exact clean _ _
    exact ⟨t,by simp [hgpow,ht]⟩
  obtain ⟨w,hw⟩ := fixed_shape_budget_of_single_matrix (k:=k) m hsingle Z hcomm hnil
  let v := Finset.univ.image w
  let u := s ∪ v
  let L := IntermediateField.adjoin k (u : Set F)
  have hsL : IntermediateField.adjoin k (s : Set F) ≤ L :=
    IntermediateField.adjoin_le_iff.mpr (fun x hx => IntermediateField.subset_adjoin k _ (Finset.mem_union_left _ hx))
  have hZL := hw L (fun i => IntermediateField.subset_adjoin k _ (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)))
  refine ⟨u,?_,fun i j => hsL (hA i j),recovery_mem L B H Z (fun i j => hsL (hH i j)) hZL hdet hb⟩
  have hvc : v.card ≤ finrank F (Cent (K:=F) m) - ∑ h, m h := by
    simpa [v] using (Finset.card_image_le (s:=Finset.univ) (f:=w))
  have hc1 : finrank F (Cent (K:=F) m) ≤ Fintype.card (Ix m)^2 := by
    rw [(jCentEquiv (F:=F) m).finrank_eq]
    apply le_trans (Submodule.finrank_le _)
    simp [Module.finrank_matrix,pow_two]
  have hc2 : (∑ h, m h) ≤ finrank F (Cent (K:=F) m) := by
    have he := primitive_rank_nullity (K:=F) m
    have hb' : (∑ h, m h) ≤ ∑ h, m h^2 := by
      apply Finset.sum_le_sum; intro i _; exact Nat.le_self_pow (by decide) _
    omega
  rw [← (jCentEquiv (F:=F) m).finrank_eq, ←pow_two] at hs
  exact (Finset.card_union_le _ _).trans (by omega)
end GKGauge
#print axioms GKGauge.pair_given_shape

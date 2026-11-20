module

public import GaugeParameters

@[expose] public section

noncomputable section
namespace GKGauge
open Module Matrix
universe u
variable {k F : Type u} [Field k] [Infinite k] [Field F] [Algebra k F]
variable {n : Type u} [Fintype n] [DecidableEq n]

def intertwiner (A J : Matrix n n F) : Submodule F (Matrix n n F) where
  carrier := {H | A * H = H * J}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy; change A * (x+y)=(x+y)*J
    rw [mul_add,add_mul,hx,hy]
  smul_mem' := by
    intro a x hx; change A*(a • x)=(a • x)*J
    rw [Matrix.mul_smul,Matrix.smul_mul,hx]

@[simp] theorem mem_intertwiner (A J H : Matrix n n F) :
  H ∈ intertwiner A J ↔ A * H = H * J := Iff.rfl

def centralizerIso (A J H : Matrix n n F) (hH : H.det ≠ 0) (hc : A * H = H * J) :
  intertwiner J J ≃ₗ[F] intertwiner A J := by
  let hi : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hH)
  let hi' : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hH)
  have hc' : J * H⁻¹ = H⁻¹ * A := by
    calc
      J * H⁻¹ = (H⁻¹*H) * (J*H⁻¹) := by rw [hi,one_mul]
      _ = H⁻¹ * (H*J) * H⁻¹ := by simp only [mul_assoc]
      _ = H⁻¹ * A := by rw [← hc]; simp only [mul_assoc,hi',mul_one]
  exact {
    toFun := fun x => ⟨H*x.1, by
      change A*(H*x.val)=(H*x.val)*J
      rw [← mul_assoc,hc,mul_assoc,x.property,← mul_assoc]⟩
    invFun := fun x => ⟨H⁻¹*x.1,by
      change J*(H⁻¹*x.val)=(H⁻¹*x.val)*J
      rw [← mul_assoc,hc',mul_assoc,x.property,←mul_assoc]⟩
    left_inv := fun x => by
      apply Subtype.ext; change H⁻¹ * (H * x.val)=x.val
      rw [←mul_assoc,hi,one_mul]
    right_inv := fun x => by
      apply Subtype.ext; change H * (H⁻¹ * x.val)=x.val
      rw [←mul_assoc,hi',one_mul]
    map_add' := fun x y => by apply Subtype.ext; exact mul_add _ _ _
    map_smul' := fun a x => by apply Subtype.ext; exact Matrix.mul_smul _ _ _
  }

/-- No rational section of a homogeneous space is assumed: the selected
conjugating matrix and the resulting true conjugate use the same r²−c entries. -/
theorem orbit_parameters (A J : Matrix n n F)
    (h : ∃ H : Matrix n n F, H.det ≠ 0 ∧ A * H = H * J)
    (hJ : ∀ i j, J i j ∈ (algebraMap k F).range) :
    ∃ (s : Finset F) (H : Matrix n n F), s.card ≤
        Fintype.card n * Fintype.card n - finrank F (intertwiner J J) ∧
      H.det ≠ 0 ∧ A*H=H*J ∧
      (∀ i j, H i j ∈ IntermediateField.adjoin k (s : Set F)) ∧
      ∀ i j, A i j ∈ IntermediateField.adjoin k (s : Set F) := by
  obtain ⟨P,hp,he⟩ := h
  have hd := (centralizerIso A J P hp he).finrank_eq
  obtain ⟨z,hz,s,hs,hm⟩ := gauge_parameters (k:=k) (intertwiner A J) ⟨⟨P,he⟩,hp⟩
  rw [← hd] at hs
  refine ⟨s,z.val,hs,hz,z.property,hm,recovery_mem _ A z.val J hm ?_ hz z.property⟩
  intro i j
  obtain ⟨a,ha⟩ := hJ i j
  exact ha ▸ IntermediateField.algebraMap_mem _ a
end GKGauge
#print axioms GKGauge.centralizerIso
#print axioms GKGauge.orbit_parameters

module

public import JordanMatrix

@[expose] public section
noncomputable section
namespace JordanPrimitive
open Module
variable {K : Type*} [Field K] {H : ℕ} (m : Fin H → ℕ)

def gen (h : Fin H) (a : Fin (m h)) : V K m :=
  coordBasis m ⟨h,Fin.last h.val,a⟩

theorem gen_level (h : Fin H) (p : Fin (h.val+1)) (a : Fin (m h)) :
    ((J m ^ (h.val-p.val)) (gen (K:=K) m h a)) = coordBasis m ⟨h,p,a⟩ := by
  funext l q
  rw [Jpow,gen,coord_apply,coord_apply]
  by_cases he : l=h
  · subst l
    by_cases hq : q=p
    · subst q
      have hu : p.val + (h.val-p.val) = h.val := by have := p.isLt; omega
      simp [hu,Pi.single_eq_same]
      exact Pi.single_eq_same _ _
    · have hne : q.val + (h.val-p.val) ≠ h.val := by
        have := p.isLt
        have hqp : q.val ≠ p.val := fun e => hq (Fin.ext e)
        omega
      simp only [Pi.single_eq_same,Pi.single_eq_of_ne hq]
      split_ifs with hc
      · exact Pi.single_eq_of_ne (fun e => hne (congrArg Fin.val e)) _
      · rfl
  · split_ifs <;> rw [Pi.single_eq_of_ne he] <;> simp [Pi.single_eq_of_ne he]

theorem gen_killed (h : Fin H) (a : Fin (m h)) :
    ((J m ^ (h.val+1)) (gen (K:=K) m h a)) = 0 := by
  funext l q
  rw [Jpow,gen,coord_apply]
  by_cases he : l=h
  · subst l; rw [dite_eq_right (by omega)]; rfl
  · split_ifs <;> simp [Pi.single_eq_of_ne he]

abbrev Coeff (K : Type*) [Field K] {H : ℕ} (m : Fin H → ℕ) :=
  (h : Fin H) → Fin (m h) → LinearMap.ker (J (K:=K) m ^ (h.val+1))

def ofCoeff (f : Coeff K m) : Module.End K (V K m) :=
  (coordBasis (K:=K) m).constr K
    (fun i => (J m ^ (i.1.val-i.2.1.val)) (f i.1 i.2.2).1)

theorem coeff_at (f : Coeff K m) (h : Fin H) (p : Fin (h.val+1)) (a : Fin (m h)) :
    ofCoeff m f (coordBasis m ⟨h,p,a⟩) = (J m ^ (h.val-p.val)) (f h a).1 := by
  apply Basis.constr_basis

theorem ofCoeff_comm (f : Coeff K m) : Commute (ofCoeff m f) (J m) := by
  apply (coordBasis m).ext
  rintro ⟨h,p,a⟩
  change ofCoeff m f (J m (coordBasis m ⟨h,p,a⟩)) =
    J m (ofCoeff m f (coordBasis m ⟨h,p,a⟩))
  rw [coeff_at,← gen_level]
  have step (k : ℕ) (v : V K m) : J m ((J m ^ k) v) = (J m ^ (k+1)) v := by
    rw [pow_succ',mul_apply_eq_comp]
  rw [step,step]
  by_cases hp : p.val=0
  · rw [hp,Nat.sub_zero,gen_killed,map_zero]
    exact (f h a).2.symm
  · let q : Fin (h.val+1) := ⟨p.val-1,by have := p.isLt; omega⟩
    have hq : h.val-p.val+1 = h.val-q.val := by dsimp [q]; have := p.isLt; omega
    rw [hq,gen_level,coeff_at]

def coeffOf (z : Cent (K:=K) m) : Coeff K m :=
  fun h a => ⟨z.1 (gen m h a),by
    change (J m ^ (h.val+1)) (z.1 (gen m h a)) = 0
    have he := congrArg (fun g : Module.End K (V K m) => g (gen m h a))
      ((commJ m z).pow_right (h.val+1)).eq.symm
    simpa [mul_apply_eq_comp,gen_killed] using he⟩

def toCent (f : Coeff K m) : Cent (K:=K) m := ⟨ofCoeff m f,by
  apply (Subalgebra.mem_centralizer_iff K).mpr
  rintro _ ⟨rfl⟩
  exact (ofCoeff_comm m f).eq.symm⟩

def coefficientEquiv : Cent (K:=K) m ≃ₗ[K] Coeff K m where
  toFun := coeffOf m
  invFun := toCent m
  left_inv z := by
    apply Subtype.ext
    apply (coordBasis m).ext
    rintro ⟨h,p,a⟩
    change ofCoeff m (coeffOf m z) (coordBasis m ⟨h,p,a⟩) =
      z.1 (coordBasis m ⟨h,p,a⟩)
    rw [coeff_at,← gen_level]
    exact congrArg (fun g : Module.End K (V K m) => g (gen m h a))
      ((commJ m z).pow_right _).eq.symm
  right_inv f := by
    funext h a
    apply Subtype.ext
    change ofCoeff m f (coordBasis m ⟨h,Fin.last h.val,a⟩) = (f h a).1
    simp [coeff_at]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end JordanPrimitive

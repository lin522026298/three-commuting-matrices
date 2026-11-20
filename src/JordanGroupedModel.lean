module

public import JordanPID
public import JordanGroupSites
public import JordanStrings

@[expose] public section

noncomputable section
set_option maxHeartbeats 110000
open Module Polynomial JordanPrimitive
namespace ActualJordan
variable {K : Type*} [Field K] {d : ℕ} (s : Fin d → ℕ)
def rt (n : ℕ) : Tr K n := AdjoinRoot.root ((X : K[X])^n)
theorem rt_pow (n : ℕ) : (rt (K:=K) n)^n = 0 := by
  simpa [rt,Polynomial.eval₂_pow,Polynomial.eval₂_X] using AdjoinRoot.eval₂_root ((X : K[X])^n)
def tb (n : ℕ) : Basis (Fin n) K (Tr K n) :=
  let pb := AdjoinRoot.powerBasis' ((Polynomial.monic_X : (X : K[X]).Monic).pow n)
  pb.basis.reindex (finCongr (by simp [pb]))
theorem tb_pow (n : ℕ) (j : Fin n) : tb (K:=K) n j = (rt n)^j.val := by
  rw [tb,Basis.reindex_apply,PowerBasis.basis_eq_pow]; rfl

def productBasis : Basis (Uix s) K ((i : Fin d) → Tr K (s i)) :=
  Pi.basis (fun i => tb (s i))

def groupedToProduct : V K (multiplicity s) ≃ₗ[K] ((i : Fin d) → Tr K (s i)) :=
  (coordBasis (K:=K) (multiplicity s)).equiv (productBasis s) (powerEquiv s)

theorem grouped_basis_value (h : Fin (height s)) (p : Fin (h.val+1)) (a : Fin (multiplicity s h)) :
    groupedToProduct (K:=K) s (coordBasis _ ⟨h,p,a⟩) =
      Pi.single (pick s h a).val ((rt (s (pick s h a).val))^(h.val-p.val)) := by
  rw [groupedToProduct,Basis.equiv_apply,productBasis,Pi.basis_apply,tb_pow]
  congr 2
  change p.rev.val = h.val - p.val
  rw [Fin.val_rev]
  omega

def timesRoot : Module.End K ((i : Fin d) → Tr K (s i)) where
  toFun v i := rt (s i) * v i
  map_add' v w := by funext i; exact mul_add _ _ _
  map_smul' u v := by
    funext i
    change rt (s i) * (u • v i) = u • (rt (s i) * v i)
    exact Algebra.mul_smul_comm u (rt (s i)) (v i)

theorem root_single (i : Fin d) (u : Tr K (s i)) :
    timesRoot s (Pi.single i u) = Pi.single i (rt _ * u) := by
  funext j
  change rt (s j) * (Pi.single i u : (l : Fin d) → Tr K (s l)) j = _
  by_cases hj : j=i
  · subst j; simp
  · simp [Pi.single_eq_of_ne hj]

theorem shift_basis {N : ℕ} (m : Fin N → ℕ) (h : Fin N)
    (p : Fin (h.val+1)) (a : Fin (m h)) :
    J (K:=K) m (coordBasis m ⟨h,p,a⟩) =
      if hp : p.val = 0 then 0 else
        coordBasis m ⟨h,⟨p.val-1,by have := p.isLt; omega⟩,a⟩ := by
  rw [← gen_level (K:=K) m h p a]
  change ((J (K:=K) m * J (K:=K) m ^ (h.val-p.val)) (gen (K:=K) m h a)) = _
  rw [← pow_succ']
  split_ifs with hp
  · rw [hp,Nat.sub_zero,gen_killed]
  · let q : Fin (h.val+1) := ⟨p.val-1,by have := p.isLt; omega⟩
    have hq : h.val-p.val+1 = h.val-q.val := by dsimp [q]; have := p.isLt; omega
    rw [hq,gen_level]

theorem grouped_on_basis (h : Fin (height s)) (p : Fin (h.val+1)) (a : Fin (multiplicity s h)) :
    groupedToProduct (K:=K) s (J (multiplicity s) (coordBasis (multiplicity s) ⟨h,p,a⟩)) =
    timesRoot (K:=K) s (groupedToProduct (K:=K) s (coordBasis (multiplicity s) ⟨h,p,a⟩)) := by
  rw [grouped_basis_value s h p a,root_single,← pow_succ' (rt (K:=K) (s (pick s h a).val)) _]
  rw [shift_basis]
  split_ifs with hp
  · have hz : (rt (K:=K) (s (pick s h a).val))^(h.val+1) = 0 := by
      simpa only [(pick s h a).2] using rt_pow (K:=K) (s (pick s h a).val)
    rw [hp,Nat.sub_zero,map_zero,hz,Pi.single_zero]
  · rw [grouped_basis_value]
    have hq : h.val-(p.val-1)=h.val-p.val+1 := by have := p.isLt; omega
    exact congrArg (fun n : ℕ => (Pi.single (pick s h a).val ((rt (K:=K) (s (pick s h a).val))^n) : (i : Fin d) → Tr K (s i))) hq

attribute [local irreducible] groupedToProduct timesRoot in
theorem grouped_intertwine : (groupedToProduct (K:=K) s).toLinearMap.comp (J (multiplicity s)) =
    (timesRoot (K:=K) s).comp (groupedToProduct (K:=K) s).toLinearMap := by
  exact (coordBasis (K:=K) (multiplicity s)).ext fun ⟨h,p,a⟩ => grouped_on_basis (K:=K) s h p a

variable {M : Type*} [AddCommGroup M] [Module K M] [Module.Finite K M]
theorem exists_grouped (T : Module.End K M) (hn : IsNilpotent T) :
    ∃ (H : ℕ) (m : Fin H → ℕ) (e : V K m ≃ₗ[K] M), ∀ v, T (e v) = e (J m v) := by
  obtain ⟨d,s,f,hf⟩ := exists_truncated_model T hn
  refine ⟨height s,multiplicity s,(groupedToProduct s).trans f.symm,?_⟩
  intro v
  apply f.injective
  change f (T (f.symm (groupedToProduct s v))) = f (f.symm (groupedToProduct s (J _ v)))
  rw [f.apply_symm_apply]
  have he := congrArg (fun g => (g : V K (multiplicity s) →ₗ[K] ((i : Fin d) → Tr K (s i))) v)
    (grouped_intertwine (K:=K) s)
  funext i
  rw [hf,f.apply_symm_apply]
  exact (congrFun he i).symm

end ActualJordan

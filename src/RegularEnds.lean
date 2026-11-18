import Gerstenhaber.FourBlocks.MinimalSource.KernelHeadDuality
import Gerstenhaber.FourBlocks.MinimalSource.CyclicOperator

noncomputable section
namespace DVRMinimal
open Module LinearMap
open Gerstenhaber.FourBlocks.HeadBounds Gerstenhaber.FourBlocks.MinimalSource
open Gerstenhaber.CanonicalExtension
variable {k A W : Type*} [Field k] [CommRing A] [Algebra k A]
  [AddCommGroup W] [Module A W] [Module k W] [IsScalarTower k A W]

def Cyc (A W : Type*) [CommRing A] [AddCommGroup W] [Module A W] : Prop :=
  ∃ w : W, ∀ x : W, ∃ a : A, a • w = x

theorem liftCyclic [Module.Finite k W] (t : A) (ht : IsNilpotent t)
    (h : Cyc A (ActualHead (M := W) t)) : Cyc A W := by
  obtain ⟨q,hq⟩ := h
  obtain ⟨w,rfl⟩ := headProjection_surjective t q
  let P : Submodule A W := Submodule.span A {w}
  let J : Ideal A := Ideal.span {t}
  letI : Module.Finite A W := Module.Finite.of_restrictScalars_finite k _ _
  have hJ : J ≤ Ring.jacobson A := by
    apply le_trans _ (nilradical_le_jacobson _)
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (mem_nilradical.mpr ht))
  have hh : (⊤ : Submodule A W) ≤ P ⊔ J • ⊤ := by
    intro x _
    obtain ⟨a,ha⟩ := hq (headProjection t x)
    have hz : x-a•w ∈ tImage t := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change headProjection t (x-a•w)=0
      rw [map_sub,map_smul,ha,sub_self]
    obtain ⟨y,hy⟩ := hz
    apply Submodule.mem_sup.mpr
    refine ⟨a•w,P.smul_mem _ (Submodule.mem_span_singleton_self w),t•y,?_,?_⟩
    · exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton t)) Submodule.mem_top
    · change t • y=x-a•w at hy
      rw [hy]; abel
  have hP := Submodule.le_of_le_smul_of_le_jacobson Module.Finite.fg_top hJ hh
  exact ⟨w, fun x => Submodule.mem_span_singleton.mp (hP (Submodule.mem_top (x:=x)))⟩

theorem cyc_of_dim_one [Module.Finite k W] (h : finrank k W=1) : Cyc A W := by
  obtain ⟨w,hw⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (show 0<finrank k W by omega)
  have hh := (finrank_eq_one_iff_of_ne_zero w hw).mp h
  refine ⟨w,fun x => ?_⟩
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (show x ∈ Submodule.span k {w} by rw [hh]; trivial)
  exact ⟨algebraMap k A c, by simpa only [IsScalarTower.algebraMap_smul] using hc⟩

theorem cyclic_payment [Module.Finite k W] (h : Cyc A W) :
    finrank k (actualActionImage (K:=k) (A:=A) (M:=W)) ≤ finrank k W := by
  obtain ⟨w,hw⟩ := h
  let E := actualActionImage (K:=k) (A:=A) (M:=W)
  let f : E →ₗ[k] W := (LinearMap.applyₗ w).comp E.val.toLinearMap
  apply LinearMap.finrank_le_finrank_of_injective (f:=f)
  rintro ⟨p,⟨a,rfl⟩⟩ ⟨q,⟨b,rfl⟩⟩ hab
  apply Subtype.ext
  ext v
  obtain ⟨c,rfl⟩ := hw v
  change a • w = b • w at hab
  change a • (c • w) = b • (c • w)
  rw [smul_comm a c,hab,smul_comm b c]

theorem regular_head_pay [Module.Finite k W] (t y : A)
    (ht : IsNilpotent t) (hy : IsNilpotent y)
    (h : finrank k (Algebra.lsmul k k (ActualHead (M:=W) t) y).ker = 1) :
    finrank k (actualActionImage (K:=k) (A:=A) (M:=W)) ≤ finrank k W := by
  apply cyclic_payment
  apply liftCyclic (k:=k) t ht
  apply liftCyclic (k:=k) y hy
  apply cyc_of_dim_one (k:=k)
  rw [actualHead_finrank]; exact h

local instance (priority := 50) : Module A (Module.Dual k W) := positiveDualModule
local instance (priority := 50) : IsScalarTower k A (Module.Dual k W) := positiveDual_tower

theorem regular_tail_pay [Module.Finite k W] (t y : A)
    (ht : IsNilpotent t) (hy : IsNilpotent y)
    (h : finrank k (Algebra.lsmul k k (tKernel (M:=W) t) y).ker = 1) :
    finrank k (actualActionImage (K:=k) (A:=A) (M:=W)) ≤ finrank k W := by
  let H := ActualHead (M:=Module.Dual k W) t
  letI : Module A (Module.Dual k H) := positiveDualModule
  letI : IsScalarTower k A (Module.Dual k H) := positiveDual_tower
  letI : FiniteDimensional k (tKernel (M:=W) t) := FiniteDimensional.of_injective ((tKernel (M:=W) t).subtype.restrictScalars k) (tKernel (M:=W) t).injective_subtype
  let e := (kernelDualHeadEquiv (K:=k) (M:=W) t).restrictScalars k
  have same : finrank k (Algebra.lsmul k k (tKernel (M:=W) t) y).ker =
      finrank k (Algebra.lsmul k k (Module.Dual k H) y).ker := by
    apply le_antisymm
    · apply finrank_ker_le_of_injective_intertwining _ _ e.toLinearMap e.injective
      intro x; exact (kernelDualHeadEquiv (K:=k) (M:=W) t).map_smul y x
    · apply finrank_ker_le_of_injective_intertwining _ _ e.symm.toLinearMap e.symm.injective
      intro x; exact (kernelDualHeadEquiv (K:=k) (M:=W) t).symm.map_smul y x
  have hH : finrank k (Algebra.lsmul k k H y).ker=1 := by
    rw [← positiveDual_first_kernel_finrank (K:=k) (M:=H) y,←same,h]
  have hh := regular_head_pay (k:=k) (W:=Module.Dual k W) t y ht hy hH
  rw [positiveDual_actionImage_finrank,Subspace.dual_finrank_eq] at hh
  exact hh

#print axioms regular_head_pay
#print axioms regular_tail_pay
end DVRMinimal

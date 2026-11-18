module

public import Gerstenhaber.FourBlocks.MinimalSource.CyclicParent

/-!
A one-dimensional actual cokernel of a nilpotent operator gives a
literal cyclic module over its polynomial algebra. Every commuting
operator is then an actual polynomial in that operator.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace Gerstenhaber.FourBlocks.MinimalSource

open Module LinearMap
open scoped IsMulCommutative

variable {K N : Type*} [Field K] [AddCommGroup N] [Module K N]

abbrev UnaryAlgebra (f : Module.End K N) := Algebra.adjoin K ({f} : Set (Module.End K N))

instance unaryAlgebra_commRing (f : Module.End K N) : CommRing (UnaryAlgebra f) := inferInstance

instance unaryAlgebra_tower (f : Module.End K N) : IsScalarTower K (UnaryAlgebra f) N :=
  ⟨fun _ _ _ => rfl⟩

def unaryRoot (f : Module.End K N) : UnaryAlgebra f :=
  ⟨f,Algebra.subset_adjoin (Set.mem_singleton _)⟩

theorem unaryRoot_nilpotent (f : Module.End K N) (hnil : IsNilpotent f) :
    IsNilpotent (unaryRoot f) :=
  (IsNilpotent.map_iff (f := (UnaryAlgebra f).val) Subtype.val_injective).mp hnil

/-- Finite Nakayama is applied to the actual polynomial algebra of f. -/
theorem unary_cyclic_of_spanning_cokernel [FiniteDimensional K N]
    (f : Module.End K N) (hnil : IsNilpotent f) (v : N)
    (hspan : Submodule.span K ({(LinearMap.range f).mkQ v} : Set (N ⧸ LinearMap.range f))=⊤) :
    Submodule.span (UnaryAlgebra f) ({v} : Set N)=⊤ := by
  let I : Ideal (UnaryAlgebra f) := Ideal.span {unaryRoot f}
  let C : Submodule (UnaryAlgebra f) N := Submodule.span (UnaryAlgebra f) {v}
  let : Module.Finite (UnaryAlgebra f) N := Module.Finite.of_restrictScalars_finite K _ _
  have hI : I ≤ Ring.jacobson (UnaryAlgebra f) := by
    apply le_trans _ (nilradical_le_jacobson _)
    apply Ideal.span_le.mpr
    intro a ha
    have ha' : a=unaryRoot f := Set.mem_singleton_iff.mp ha
    rw [ha']
    exact mem_nilradical.mpr (unaryRoot_nilpotent f hnil)
  have htop : (⊤ : Submodule (UnaryAlgebra f) N) ≤ C ⊔ I • ⊤ := by
    intro x _
    have hx : (LinearMap.range f).mkQ x ∈
        Submodule.span K ({(LinearMap.range f).mkQ v} : Set (N ⧸ LinearMap.range f)) := by
      rw [hspan]
      trivial
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hx
    have hmem : x-c • v ∈ LinearMap.range f := by
      apply (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).mp
      change (LinearMap.range f).mkQ (x-c • v)=0
      rw [map_sub,map_smul,hc,sub_self]
    obtain ⟨y,hy⟩ := hmem
    apply Submodule.mem_sup.mpr
    refine ⟨c • v,((C.restrictScalars K).smul_mem c (Submodule.mem_span_singleton_self v)),
      f y,?_,?_⟩
    · exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton _)) Submodule.mem_top
    · rw [hy]
      abel
  exact top_unique (Submodule.le_of_le_smul_of_le_jacobson Module.Finite.fg_top hI htop)

theorem exists_unary_cyclic_of_cokernel_finrank_one [FiniteDimensional K N]
    (f : Module.End K N) (hnil : IsNilpotent f)
    (hdim : finrank K (N ⧸ LinearMap.range f)=1) :
    ∃ v : N, Submodule.span (UnaryAlgebra f) ({v} : Set N)=⊤ := by
  obtain ⟨q,hq⟩ := (Module.finrank_pos_iff_exists_ne_zero).mp (show 0 < finrank K
    (N ⧸ LinearMap.range f) by omega)
  obtain ⟨v,rfl⟩ := (LinearMap.range f).mkQ_surjective q
  exact ⟨v,unary_cyclic_of_spanning_cokernel f hnil v
    ((finrank_eq_one_iff_of_ne_zero _ hq).mp hdim)⟩

theorem commuting_operator_mem_unary (f g : Module.End K N) (hcomm : Commute f g)
    (v : N) (hgen : Submodule.span (UnaryAlgebra f) ({v} : Set N)=⊤) :
    g ∈ UnaryAlgebra f := by
  have hle : UnaryAlgebra f ≤ Subalgebra.centralizer K ({g} : Set (Module.End K N)) := by
    apply Algebra.adjoin_le
    intro a ha
    have ha' : a=f := Set.mem_singleton_iff.mp ha
    rw [ha']
    change ∀ b ∈ ({g} : Set (Module.End K N)), b*f=f*b
    intro b hb
    have hb' : b=g := Set.mem_singleton_iff.mp hb
    rw [hb']
    exact hcomm.eq.symm
  have hgr (r : UnaryAlgebra f) : g*(r : Module.End K N)=(r : Module.End K N)*g := by
    have hmem := hle r.2
    change ∀ b ∈ ({g} : Set (Module.End K N)),
      b*(r : Module.End K N)=(r : Module.End K N)*b at hmem
    exact hmem g (Set.mem_singleton _)
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp
    (show g v ∈ Submodule.span (UnaryAlgebra f) {v} by rw [hgen]; trivial)
  have heq : g=(a : Module.End K N) := by
    apply LinearMap.ext
    intro x
    obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp
      (show x ∈ Submodule.span (UnaryAlgebra f) {v} by rw [hgen]; trivial)
    calc
      g x = g (r • v) := congrArg g hr.symm
      _ = r • g v := LinearMap.congr_fun (hgr r) v
      _ = r • (a • v) := congrArg (fun y => r • y) ha.symm
      _ = a • (r • v) := by rw [← mul_smul,mul_comm,mul_smul]
      _ = (a : Module.End K N) x := congrArg (fun y => a • y) hr
  rw [heq]
  exact a.2

theorem commuting_operator_polynomial (f g : Module.End K N) (hcomm : Commute f g)
    (v : N) (hgen : Submodule.span (UnaryAlgebra f) ({v} : Set N)=⊤) :
    ∃ p : Polynomial K, Polynomial.aeval f p=g := by
  have hg := commuting_operator_mem_unary f g hcomm v hgen
  change g ∈ Algebra.adjoin K ({f} : Set (Module.End K N)) at hg
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hg
  exact hg

theorem unaryEvaluation_bijective (f : Module.End K N) (v : N)
    (hgen : Submodule.span (UnaryAlgebra f) ({v} : Set N)=⊤) :
    Function.Bijective (cyclicEvaluation (K := K) (A := UnaryAlgebra f) v) := by
  constructor
  · intro a b hab
    change a • v=b • v at hab
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp
      (show x ∈ Submodule.span (UnaryAlgebra f) {v} by rw [hgen]; trivial)
    calc
      (a : Module.End K N) x = a • (r • v) := congrArg (fun y => a • y) hr.symm
      _ = r • (a • v) := by rw [← mul_smul,mul_comm,mul_smul]
      _ = r • (b • v) := congrArg (fun y => r • y) hab
      _ = b • (r • v) := by rw [← mul_smul,mul_comm,mul_smul]
      _ = (b : Module.End K N) x := congrArg (fun y => b • y) hr
  · intro x
    exact Submodule.mem_span_singleton.mp
      (show x ∈ Submodule.span (UnaryAlgebra f) {v} by rw [hgen]; trivial)

theorem unary_finrank_eq_of_cyclic (f : Module.End K N) (v : N)
    (hgen : Submodule.span (UnaryAlgebra f) ({v} : Set N)=⊤) :
    finrank K (UnaryAlgebra f)=finrank K N :=
  (LinearEquiv.ofBijective (cyclicEvaluation (K := K) (A := UnaryAlgebra f) v)
    (unaryEvaluation_bijective f v hgen)).finrank_eq

section ActualAlgebra

variable {A : Type*} [CommRing A] [Algebra K A] [Module A N] [IsScalarTower K A N]

theorem actualActionImage_eq_unary_of_cyclic (t : A) (v : N)
    (hgen : Submodule.span (UnaryAlgebra (Algebra.lsmul K K N t)) ({v} : Set N)=⊤) :
    actualActionImage (K := K) (A := A) (M := N) = UnaryAlgebra (Algebra.lsmul K K N t) := by
  apply le_antisymm
  · rintro g ⟨a,rfl⟩
    apply commuting_operator_mem_unary _ _ _ v hgen
    change Algebra.lsmul K K N t*Algebra.lsmul K K N a =
      Algebra.lsmul K K N a*Algebra.lsmul K K N t
    rw [← map_mul,← map_mul,mul_comm]
  · apply Algebra.adjoin_le
    intro f hf
    have hf' : f=Algebra.lsmul K K N t := Set.mem_singleton_iff.mp hf
    exact ⟨t,hf'.symm⟩

theorem actualActionImage_eq_unary_of_cokernel_one [FiniteDimensional K N] (t : A)
    (hnil : IsNilpotent (Algebra.lsmul K K N t))
    (hdim : finrank K (N ⧸ LinearMap.range (Algebra.lsmul K K N t))=1) :
    actualActionImage (K := K) (A := A) (M := N) = UnaryAlgebra (Algebra.lsmul K K N t) := by
  obtain ⟨v,hv⟩ := exists_unary_cyclic_of_cokernel_finrank_one _ hnil hdim
  exact actualActionImage_eq_unary_of_cyclic t v hv

end ActualAlgebra

end Gerstenhaber.FourBlocks.MinimalSource

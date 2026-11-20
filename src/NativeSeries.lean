module

public import OriginActor
public import DVRMinors
public import Mathlib.RingTheory.PowerSeries.Trunc

@[expose] public section
noncomputable section
namespace DivisorG3
open Module LinearMap Matrix PowerSeries
open scoped Matrix
variable {k ι W : Type*} [Field k] [Fintype ι] [DecidableEq ι]
    [AddCommGroup W] [Module k W] [Module (O k) W] [IsScalarTower k (O k) W]
abbrev seriesAct (k W : Type*) [Field k] [AddCommGroup W] [Module k W] [Module (O k) W]
    [IsScalarTower k (O k) W] : O k →ₐ[k] End k W := Algebra.lsmul k k W
omit [Module (O k) W] [IsScalarTower k (O k) W] in
theorem finite_series_range (ρ : O k →ₐ[k] End k W) (e : ℕ) (nil : ρ X ^ e=0) :
    ρ.range=Algebra.adjoin k ({ρ X}:Set _) := by
  apply le_antisymm _ (Algebra.adjoin_le fun _ h => Set.mem_singleton_iff.mp h ▸ ⟨X,rfl⟩)
  rintro _ ⟨s,rfl⟩
  let p := trunc e s
  have divi : (X:O k)^e ∣ s-(p:O k) := by
    apply X_pow_dvd_iff.mpr
    intro i hi
    simp [p,Polynomial.coeff_coe,coeff_trunc,hi]
  obtain ⟨g,hg⟩ := divi
  have eq : ρ s=ρ (p:O k) := by rw [←sub_eq_zero,←map_sub,hg,map_mul,map_pow,nil,zero_mul]
  let incl : Polynomial k →ₐ[k] O k := Polynomial.coeToPowerSeries.algHom k
  have inclEq : (ρ.comp incl) = Polynomial.aeval (ρ X) := by
    apply Polynomial.algHom_ext
    simp [incl]
  change ρ s ∈ Algebra.adjoin k ({ρ X}:Set _)
  rw [eq,Algebra.adjoin_singleton_eq_range_aeval]
  refine ⟨p,?_⟩
  rw [←inclEq]
  simp [incl]

theorem native_nil (P : Matrix ι ι (O k)) (hp : P.det≠0) :
    IsNilpotent (seriesAct k (QP P) X) := by
  let e := P.det.order.toNat
  have he : Ideal.span ({P.det}:Set (O k)) = Ideal.span ({(X : O k)^e}:Set _) := by
    conv_lhs => rw [← X_pow_order_mul_divXPowOrder (f:=P.det)]
    exact Ideal.span_singleton_mul_right_unit (isUnit_divided_by_X_pow_order hp) _
  have dvd : P.det ∣ (X : O k)^e :=
    Ideal.mem_span_singleton.mp (he ▸ Ideal.subset_span (Set.mem_singleton _))
  have kill (w : QP P) : P.det • w=0 := by
    obtain ⟨v,rfl⟩ := P.mulVecLin.range.mkQ_surjective w
    rw [←map_smul]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨P.adjugate *ᵥ v,?_⟩
    change P *ᵥ (P.adjugate *ᵥ v)=P.det • v
    rw [mulVec_mulVec,mul_adjugate,smul_mulVec,one_mulVec]
  obtain ⟨c,hc⟩ := dvd
  refine ⟨e,LinearMap.ext fun w => ?_⟩
  rw [←map_pow]
  change (X:O k)^e • w=0
  rw [hc,mul_smul,kill]

theorem native_graph (P Y Y' Z Z' C : Matrix ι ι (O k)) (hp : P.det≠0) (sy : Y*P=P*Y')
    (sz : Z*P=P*Z') (sc : Y*Z-Z*Y=P*C) :
    let T := seriesAct k (QP P) X
    let y := (liftEnd P Y Y' sy).restrictScalars k
    let z := (liftEnd P Z Z' sz).restrictScalars k
    FiniteDimensional k (QP P) ∧ IsNilpotent T ∧ Commute T y ∧ Commute T z ∧ Commute y z ∧
      length (O k) (QP P)=finrank k (QP P) ∧
      length (O k) (actor P Y Y' Z Z' sy sz)=finrank k (triple T y z) := by
  obtain ⟨_,_,_,_,fin⟩ := smith_colength P _root_.id (by exact hp)
  let _ : FiniteDimensional k (QP P) := fin
  let ρ := seriesAct k (QP P)
  have hn := native_nil P hp
  obtain ⟨e,he⟩ := hn
  refine ⟨fin,⟨e,he⟩,?_,?_,?_,actual_length k (QP P),?_⟩
  · apply LinearMap.ext; intro w; exact ((liftEnd P Y Y' sy).map_smul X w).symm
  · apply LinearMap.ext; intro w; exact ((liftEnd P Z Z' sz).map_smul X w).symm
  · exact LinearMap.ext fun w => LinearMap.congr_fun (lift_comm _ _ _ _ _ _ sy sz sc).eq w
  · exact origin_actor_length ρ (ρ X) rfl (finite_series_range ρ e he) (fun _ _ => rfl) _ _
#print axioms finite_series_range
#print axioms native_nil
#print axioms native_graph
end DivisorG3

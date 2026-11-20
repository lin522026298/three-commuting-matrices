module

public import PoleCoordinates

@[expose] public section
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 900000
noncomputable section
namespace GKDivisor
universe u

/-- Concrete output from the pole selection. Coefficients of the input-point ring never
have to embed into the new DVR: the common ground field k and the original graph do. -/
structure BadPole (k : Type u) [Field k] (r : ℕ) (h : GKGraph.ring k r) where
  V : Type u
  [cr : CommRing V]
  [dom : IsDomain V]
  [dvr : IsDiscreteValuationRing V]
  [alg : Algebra k V]
  f : GKGraph.ring k r →ₐ[k] V
  inj : Function.Injective f
  w : V
  nonunit : ¬ IsUnit w
  equation : w * f h = (f (GKGraph.gdelta k r))^(r-1)
  count :
    let ψ := (IsScalarTower.toAlgHom k V (IsLocalRing.ResidueField V)).comp f
    Algebra.trdeg k (Algebra.adjoin k (Set.range (ψ ∘ GKGraph.gcoord k r))) + 1 = (3*r*r : ℕ)

theorem realizePole (k : Type u) [Field k] (r : ℕ) (h : GKGraph.ring k r)
    (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] [Algebra (GKGraph.ring k r) A]
    [IsScalarTower k (GKGraph.ring k r) A]
    (inj : Function.Injective (algebraMap (GKGraph.ring k r) A)) (q : A)
    (he : q * algebraMap _ A h = algebraMap _ A ((GKGraph.gdelta k r)^(r-1)))
    (H : CenterData k (GKGraph.ring k r) A q (3*r*r)) : Nonempty (BadPole k r h) := by
  obtain ⟨P,hp,hm,-,hv,-,hc⟩ := H
  letI := hp
  let N := Norm A
  let V := Localization.AtPrime P
  letI : IsDiscreteValuationRing V := hv
  let g := (IsScalarTower.toAlgHom k N V).comp (IsScalarTower.toAlgHom k A N)
  let f := g.comp (IsScalarTower.toAlgHom k (GKGraph.ring k r) A)
  have hin : Function.Injective (IsScalarTower.toAlgHom k A N) := fun a b e =>
    IsFractionRing.injective A (FractionRing A) (congrArg Subtype.val e)
  have hiv : Function.Injective (IsScalarTower.toAlgHom k N V) :=
    IsLocalization.injective V P.primeCompl_le_nonZeroDivisors
  refine ⟨{ V := V
            f := f
            inj := hiv.comp (hin.comp inj)
            w := g q
            nonunit := ?_
            equation := ?_
            count := ?_ }⟩
  · exact (IsLocalization.AtPrime.to_map_mem_maximal_iff V P _).mpr hm
  · change g q * g (algebraMap _ A h) = (g ((algebraMap _ A) (GKGraph.gdelta k r)))^(r-1)
    rw [←map_mul, he, map_pow, map_pow]
  · have ht := six_coordinate_count k r A N P
    exact (congrArg (· + 1) ht).trans hc

theorem trueGraph_concrete_pole (k : Type u) [Field k] [CharZero k] (r : ℕ)
    {O : Type*} [CommRing O] [IsDomain O] [Algebra k O]
    (T : Fin 6 → GKGraph.Mat O r) (ht : (T 0).det ≠ 0) (hT : GKGraph.Relations r T)
    (h : GKGraph.ring k r) (hd : GKGraph.point k r T ht hT h ≠ 0)
    (w : O) (hw : w * GKGraph.point k r T ht hT h = (T 0).det^(r-1)) (hn : ¬IsUnit w) :
    Nonempty (BadPole k r h) := by
  have hne : h ≠ 0 := fun e => hd (by rw [e,map_zero])
  exact realizePole k r h (invGraph k r h)
    (fun x y e => Subtype.ext (congrArg (fun z : invGraph k r h => (z : GKGraph.K k r)) e))
    (invCoord k r h) (GKRational.qmul _ _ hne) (trueGraph_pole_center k r T ht hT h hd w hw hn)

#print axioms GKDivisor.trueGraph_concrete_pole
end GKDivisor

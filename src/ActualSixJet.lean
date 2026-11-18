import DVRJetTransfer
import PrecisionRepair
import GKGraphMinor
noncomputable section
namespace DVRMinimal
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
open scoped Matrix
open GKGraph PowerSeries IsDiscreteValuationRing IsLocalRing

variable {V : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable (r : ℕ)

theorem six_jet_over (F : Type*) [Field F] (ρ : V →+* F)
    (T : Fin 6 → GKGraph.Mat V r) (hT : Relations r T) (s : selectCols r)
    (u : V) (hu : Irreducible u) (a d N : ℕ) (hA : addVal V (T 0).det=a)
    (hD : addVal V (fullMinor r (T 0) (T 1) (T 2) s)=d)
    (ha : a<N) (hd : d<N)
    (e : V ⧸ JetI u N ≃+* PowerSeries F ⧸ JetI X N)
    (et : e (jetMk u N u)=jetMk X N X)
    (ec : ∀ (x : V) (v : PowerSeries F), e (jetMk u N x)=jetMk X N v → constantCoeff v=ρ x) :
    ∃ S : Fin 6 → GKGraph.Mat (PowerSeries F) r,
      Relations r S ∧ (S 0).det.order=a ∧ (fullMinor r (S 0) (S 1) (S 2) s).order=d ∧
        ∀ l i j, constantCoeff (S l i j) = ρ (T l i j) := by
  classical
  let O := PowerSeries F
  let g := e.toRingHom.comp (jetMk u N)
  let f := jetMk (X : O) N
  choose L hL using fun x : V => (Ideal.Quotient.mk_surjective (g x))
  let A : Fin 6 → GKGraph.Mat O r := fun i => (T i).map L
  have h (i) : f.mapMatrix (A i) = g.mapMatrix (T i) := Matrix.ext fun b c => hL (T i b c)
  have ea : e (jetMk u N (T 0).det) = f (A 0).det := by
    change g (T 0).det=f (A 0).det
    simp only [RingHom.map_det,h]
  have ed : e (jetMk u N (fullMinor r (T 0) (T 1) (T 2) s)) =
      f (fullMinor r (A 0) (A 1) (A 2) s) := by
    change g _=f _
    simp only [fullMinor_map,h]
  have hdet := exact_preserved_order (F:=F) (t:=u) (N:=N) hu e et ea hA ha
  have hminor := exact_preserved_order (F:=F) (t:=u) (N:=N) hu e et ed hD hd
  have hz (B : GKGraph.Mat O r) (hh : f.mapMatrix B=0) :
      ∀ i j,(X : O)^N ∣ B i j := by
    intro i j
    apply Ideal.mem_span_singleton.mp
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    exact congrArg (fun M : GKGraph.Mat _ r => M i j) hh
  have y : f.mapMatrix (A 1*A 0-A 0*A 3)=0 := by
    rw [map_sub,map_mul,map_mul,h,h,h,←map_mul,←map_mul,hT.y,sub_self]
  have z : f.mapMatrix (A 2*A 0-A 0*A 4)=0 := by
    rw [map_sub,map_mul,map_mul,h,h,h,←map_mul,←map_mul,hT.z,sub_self]
  have c : f.mapMatrix (A 1*A 2-A 2*A 1-A 0*A 5)=0 := by
    rw [map_sub,map_sub,map_mul,map_mul,map_mul,h,h,h,h,←map_mul,←map_mul,←map_sub,←map_mul,hT.comm,sub_self]
  obtain ⟨B,D,C,hB,hD',hC,dB,dD,dC⟩ := repairSix (X : O) (A 0) (A 1) (A 2)
    (A 3) (A 4) (A 5) N (exact_order_precision _ N (hdet ▸ ENat.natCast_lt_natCast.mpr ha))
    (hz _ y) (hz _ z) (hz _ c)
  let S : Fin 6 → GKGraph.Mat O r := ![A 0,A 1,A 2,B,D,C]
  have hec (l i j) : constantCoeff (A l i j)=ρ (T l i j) :=
    ec _ _ (hL _).symm
  have pres (i j : Fin r) (X' : GKGraph.Mat O r) (l) (hx : ∀ i j, X ∣ (X'-A l) i j) :
      constantCoeff (X' i j)=ρ (T l i j) := by
    have hh := X_dvd_iff.mp (hx i j)
    change constantCoeff (X' i j-A l i j)=0 at hh
    rw [map_sub,sub_eq_zero] at hh
    exact hh.trans (hec l i j)
  refine ⟨S,⟨hB.symm,hD'.symm,hC.symm⟩,hdet,hminor,?_⟩
  intro l i j
  fin_cases l
  · exact hec 0 i j
  · exact hec 1 i j
  · exact hec 2 i j
  · exact pres i j B 3 dB
  · exact pres i j D 4 dD
  · exact pres i j C 5 dC

theorem actual_six_jet (k : Type*) [Field k] [CharZero k] [Algebra k V]
    (T : Fin 6 → GKGraph.Mat V r) (hT : Relations r T) (s : selectCols r)
    (u : V) (hu : Irreducible u) (a d N : ℕ) (hA : addVal V (T 0).det=a)
    (hD : addVal V (fullMinor r (T 0) (T 1) (T 2) s)=d)
    (ha : a<N) (hd : d<N) :
    ∃ S : Fin 6 → GKGraph.Mat (PowerSeries (ResidueField V)) r,
      Relations r S ∧ (S 0).det.order=a ∧ (fullMinor r (S 0) (S 1) (S 2) s).order=d ∧
        ∀ l i j, constantCoeff (S l i j) = residue V (T l i j) := by
  let m := IsLocalRing.maximalIdeal V
  have hm : m=Ideal.span {u} := (irreducible_iff_uniformizer u).mp hu
  obtain ⟨e,et,ec⟩ := dvrJetTransfer k u hu m hm N (by omega)
  exact six_jet_over r (ResidueField V) (residue V) T hT s u hu a d N hA hD ha hd e et ec

#print axioms actual_six_jet
end DVRMinimal

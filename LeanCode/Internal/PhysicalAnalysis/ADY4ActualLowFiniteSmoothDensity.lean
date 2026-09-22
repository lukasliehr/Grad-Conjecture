import ADY3ActualLowRadialRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularLowEnergy
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace
open Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

def lowModeEncodedValue (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    WeightedRadialH1 1 lower →L[ℝ] CollarL2 (ComplexEuclidean 1) lower :=
  ((collarScalar 1 lower (lowStorageWeight lower positive)).restrictScalars ℝ).comp
    ((collarH1Coordinate (ComplexEuclidean 1) lower 0).comp (weightedToOrdinary 1 lower positive bounded.le))

def lowModeEncodedSlope (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (index : LowAnnularIndex) : WeightedRadialH1 1 lower →L[ℝ] CollarL2 (ComplexEuclidean 1) lower :=
  ((collarScalar 1 lower (lowStorageWeight lower positive)).restrictScalars ℝ).comp
    (((collarScalar 1 lower (lowMuInverseCurve lower length positive index.2.val.2)).restrictScalars ℝ).comp
      ((collarH1Coordinate (ComplexEuclidean 1) lower 1).comp (weightedToOrdinary 1 lower positive bounded.le)))

/-- A single actual radial H1 function is encoded with exactly the BE18 weights. -/
def lowModeCoordinates (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (index : LowAnnularIndex) : WeightedRadialH1 1 lower →L[ℝ] LowEnergyAmbient lower :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => LowEnergyBulk lower)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![
      (lp.singleContinuousLinearMap ℝ (fun _ : LowAnnularIndex => CollarL2 (ComplexEuclidean 1) lower) 2 index).comp
        (lowModeEncodedValue lower positive bounded),
      (lp.singleContinuousLinearMap ℝ (fun _ : LowAnnularIndex => CollarL2 (ComplexEuclidean 1) lower) 2 index).comp
        (lowModeEncodedSlope lower length positive bounded index)])

theorem lowModeCoordinates_mem (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (index : LowAnnularIndex) (radial : WeightedRadialH1 1 lower) :
    lowModeCoordinates lower length positive bounded index radial ∈ lowEnergyGraph lower length positive := by
  intro other
  change CollarWeakDerivative lower
    (collarScalar 1 lower (lowStorageInverse lower positive)
      ((lp.single 2 index (lowModeEncodedValue lower positive bounded radial) : LowEnergyBulk lower) other))
    (collarScalar 1 lower (lowMuCurve lower length positive other.2.val.2)
      (collarScalar 1 lower (lowStorageInverse lower positive)
        ((lp.single 2 index (lowModeEncodedSlope lower length positive bounded index radial) : LowEnergyBulk lower) other)))
  by_cases same : other = index
  · subst other
    simp only [lp.single_apply, Pi.single_eq_same]
    change CollarWeakDerivative lower
      (collarScalar 1 lower (lowStorageInverse lower positive)
        (collarScalar 1 lower (lowStorageWeight lower positive)
          (collarH1Coordinate (ComplexEuclidean 1) lower 0 (weightedToOrdinary 1 lower positive bounded.le radial))))
      (collarScalar 1 lower (lowMuCurve lower length positive index.2.val.2)
        (collarScalar 1 lower (lowStorageInverse lower positive)
          (collarScalar 1 lower (lowStorageWeight lower positive)
            (collarScalar 1 lower (lowMuInverseCurve lower length positive index.2.val.2)
              (collarH1Coordinate (ComplexEuclidean 1) lower 1 (weightedToOrdinary 1 lower positive bounded.le radial))))))
    rw [lowStorage_decode_encode, lowStorage_decode_encode, lowMu_decode_encode]
    exact weightedRadial_weak 1 lower positive bounded.le radial
  · simp only [lp.single_apply, Pi.single_eq_of_ne same, map_zero]
    intro test vector
    simp only [map_zero, neg_zero]

/-- Finite Fourier support and infinitely smooth radial inputs, with no free trace data. -/
def lowFiniteSmoothCore (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    (LowAnnularIndex →₀ SmoothRadialCore 1) →ₗ[ℝ] LowEnergyAmbient lower :=
  Finsupp.lsum ℝ (fun index => (lowModeCoordinates lower length positive bounded index).toLinearMap.comp
    (weightedRadialCoreInto 1 lower))

theorem lowFiniteSmoothCore_single (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (index : LowAnnularIndex) (core : SmoothRadialCore 1) :
    lowFiniteSmoothCore lower length positive bounded (Finsupp.single index core) =
      lowModeCoordinates lower length positive bounded index (weightedRadialCoreInto 1 lower core) := by
  rw [lowFiniteSmoothCore, Finsupp.lsum_single]
  rfl

theorem lowFiniteSmoothCore_mem (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) :
    lowFiniteSmoothCore lower length positive bounded core ∈ lowEnergyGraph lower length positive := by
  rw [lowFiniteSmoothCore, Finsupp.lsum_apply, Finsupp.sum]
  exact (lowEnergyGraph lower length positive).sum_mem
    (fun index _ => lowModeCoordinates_mem lower length positive bounded index (weightedRadialCoreInto 1 lower (core index)))

def lowAmbientSingle (lower : ℝ) (index : LowAnnularIndex) (field : LowEnergyAmbient lower) :
    LowEnergyAmbient lower :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => LowEnergyBulk lower)).symm
    (fun coordinate => lp.single 2 index (field coordinate index))

theorem lowModeCoordinates_recover (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    lowModeCoordinates lower length positive bounded index (lowEnergyRadialGraph lower length positive bounded field index) =
      lowAmbientSingle lower index field.val := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · change (lp.single 2 index (lowModeEncodedValue lower positive bounded
      (lowEnergyRadialGraph lower length positive bounded field index)) : LowEnergyBulk lower) = _
    congr 1
    change collarScalar 1 lower (lowStorageWeight lower positive)
      (collarH1Coordinate (ComplexEuclidean 1) lower 0
        (weightedToOrdinary 1 lower positive bounded.le (lowEnergyRadialGraph lower length positive bounded field index))) = _
    rw [lowEnergyRadialGraph_value]
    exact lowStorage_encode_decode lower positive (field.val 0 index)
  · change (lp.single 2 index (lowModeEncodedSlope lower length positive bounded index
      (lowEnergyRadialGraph lower length positive bounded field index)) : LowEnergyBulk lower) = _
    congr 1
    change collarScalar 1 lower (lowStorageWeight lower positive)
      (collarScalar 1 lower (lowMuInverseCurve lower length positive index.2.val.2)
        (collarH1Coordinate (ComplexEuclidean 1) lower 1
          (weightedToOrdinary 1 lower positive bounded.le (lowEnergyRadialGraph lower length positive bounded field index)))) = _
    rw [lowEnergyRadialGraph_slope, lowEnergy_normalized_derivative, lowStorage_encode_decode]
    rfl

theorem lowAmbientSingle_hasSum (lower : ℝ) (field : LowEnergyAmbient lower) :
    HasSum (fun index => lowAmbientSingle lower index field) field := by
  let equivalence := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => LowEnergyBulk lower)
  have sums : HasSum (fun index => fun coordinate : Fin 2 =>
      (lp.single 2 index (field coordinate index) : LowEnergyBulk lower)) (fun coordinate => field coordinate) :=
    Pi.hasSum.mpr (fun coordinate => lp.hasSum_single (by norm_num) (field coordinate))
  exact equivalence.symm.toContinuousLinearMap.hasSum sums

/-- The complete independently specified weak graph is exactly the closure
of finite genuinely smooth fields. This proves density, rather than assuming it. -/
theorem lowFiniteSmoothCore_closure (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    (LinearMap.range (lowFiniteSmoothCore lower length positive bounded)).topologicalClosure =
      (lowEnergyGraph lower length positive).restrictScalars ℝ := by
  let subspace := (LinearMap.range (lowFiniteSmoothCore lower length positive bounded)).topologicalClosure
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨core, rfl⟩
      exact lowFiniteSmoothCore_mem lower length positive bounded core
    · exact lowEnergyGraph_closed lower length positive
  · intro value member
    let field : lowEnergyGraph lower length positive := ⟨value, member⟩
    have singleMember (index : LowAnnularIndex) (radial : WeightedRadialH1 1 lower) :
        lowModeCoordinates lower length positive bounded index radial ∈ subspace := by
      apply isClosed_property (weightedRadialCoreInto_denseRange 1 lower)
        ((LinearMap.range (lowFiniteSmoothCore lower length positive bounded)).isClosed_topologicalClosure.preimage
          (lowModeCoordinates lower length positive bounded index).continuous) _ radial
      intro core
      apply Submodule.le_topologicalClosure
      exact ⟨Finsupp.single index core, lowFiniteSmoothCore_single lower length positive bounded index core⟩
    have convergence : HasSum (fun index : LowAnnularIndex =>
        lowModeCoordinates lower length positive bounded index (lowEnergyRadialGraph lower length positive bounded field index)) value := by
      exact (lowAmbientSingle_hasSum lower field.val).congr_fun
        (fun index => lowModeCoordinates_recover lower length positive bounded field index)
    exact (LinearMap.range (lowFiniteSmoothCore lower length positive bounded)).isClosed_topologicalClosure.mem_of_tendsto
      convergence (Filter.Eventually.of_forall (fun support =>
        subspace.sum_mem (fun index _ => singleMember index (lowEnergyRadialGraph lower length positive bounded field index))))

end Grad.AnnularLowEnergy

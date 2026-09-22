import AJI20ActualUnknownInputCoefficients
import AEM19ExactHighLowPhysicalStorage

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.AnnularCrossMaps Grad.AnnularCurrentLow Grad.AnnularHighTilt Grad.AnnularTiltedReference
open Grad.AnnularFluxTrace Grad.AnnularVariational Grad.PhaseAlgebra Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The genuine continuous H1 representative retains its exact sqrt(r)
stored coordinate, rather than merely a bound on an unrelated representative. -/
theorem weightedSection_originalStorage (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : WeightedRadialH1 1 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      weightedRadialCoordinate 1 lower 0 field radius =
        Real.sqrt radius • weightedRadialSection 1 lower positive bounded field (radialClamp lower bounded.le radius) := by
  rw [weightedRadialCoordinate_eq_sqrt 1 lower positive bounded.le 0 field]
  filter_upwards [radialSqrtMap_ae 1 lower
    (collarH1Coordinate (ComplexEuclidean 1) lower 0 (weightedToOrdinary 1 lower positive bounded.le field)),
    weightedRadialSection_ae 1 lower positive bounded field] with radius stored representative
  rw [stored]
  exact congrArg (fun value : ComplexEuclidean 1 => Real.sqrt radius • value) representative.symm

theorem originalHighSection_storageFactor (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    lowRhoPhysicalWeight parameters lower positive radius mode *
      highPowerCurve lower highTiltExponent positive radius * annularInversePhase parameters mode.2 radius = Real.sqrt radius := by
  have radiusPositive := positive.trans_le inside.1
  rw [crossPhysicalStorageWeight parameters lower positive radius inside mode,
    highPowerCurve_physical lower highTiltExponent positive radius inside]
  change (radius ^ (-annularTiltExponent) *
    (Real.sqrt radius * Real.exp (radialPhase parameters radius mode.2) * 1)) *
      radius ^ annularTiltExponent * Real.exp (-radialPhase parameters radius mode.2) = Real.sqrt radius
  rw [Real.rpow_neg radiusPositive.le, Real.exp_neg]
  field_simp [(Real.rpow_pos_of_pos radiusPositive annularTiltExponent).ne',
    (Real.exp_pos (radialPhase parameters radius mode.2)).ne']

theorem originalHighSection_storageSmul (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) (value : ComplexEuclidean 1) :
    (lowRhoPhysicalWeight parameters lower positive radius mode : ℂ) •
      (highPowerCurve lower highTiltExponent positive radius • (annularInversePhase parameters mode.2 radius • value)) =
        Real.sqrt radius • value := by
  apply PiLp.ext
  intro coordinate
  change (lowRhoPhysicalWeight parameters lower positive radius mode : ℂ) *
    ((highPowerCurve lower highTiltExponent positive radius : ℂ) *
      ((annularInversePhase parameters mode.2 radius : ℂ) * value coordinate)) = (Real.sqrt radius : ℂ) * value coordinate
  have scalarLaw : (lowRhoPhysicalWeight parameters lower positive radius mode : ℂ) *
      (highPowerCurve lower highTiltExponent positive radius : ℂ) * (annularInversePhase parameters mode.2 radius : ℂ) =
      (Real.sqrt radius : ℂ) := by
    exact_mod_cast originalHighSection_storageFactor parameters lower positive radius inside mode
  calc
    _ = ((lowRhoPhysicalWeight parameters lower positive radius mode : ℂ) *
      (highPowerCurve lower highTiltExponent positive radius : ℂ) * (annularInversePhase parameters mode.2 radius : ℂ)) * value coordinate := by ring
    _ = _ := congrArg (fun scalar : ℂ => scalar * value coordinate) scalarLaw

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)

theorem actualHighXiSection_stored (field : annularEnergySpace lower length positive) (mode : HighAnnularMode) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      (lowRhoPhysicalWeight parameters lower positive radius mode.val : ℂ) •
        (highPowerCurve lower highTiltExponent positive radius •
          annularPhysicalValueSection parameters lower length positive bounded mode field (radialClamp lower bounded.le radius)) =
        annularEnergyValue lower length positive field mode radius := by
  filter_upwards [weightedSection_originalStorage lower positive bounded
    (annularModeRadialH1 lower length positive mode field), ae_restrict_mem measurableSet_Icc] with radius stored inside
  change weightedRadialCoordinate 1 lower 0 (annularModeRadialH1 lower length positive mode field) radius = _ at stored
  rw [← annularModeRadialH1_value lower length positive mode field]
  rw [stored]
  let vector : ComplexEuclidean 1 := weightedRadialSection 1 lower positive bounded
    (annularModeRadialH1 lower length positive mode field) (radialClamp lower bounded.le radius)
  change (lowRhoPhysicalWeight parameters lower positive radius mode.val : ℂ) •
    (highPowerCurve lower highTiltExponent positive radius •
      (annularInversePhase parameters mode.val.2 (radialClamp lower bounded.le radius).val • vector)) = Real.sqrt radius • vector
  rw [radialClamp_eq lower bounded.le radius inside]
  exact originalHighSection_storageSmul parameters lower positive radius inside mode.val _

omit length in
theorem actualHighXSection_stored (field : annularFluxWeakGraph lower positive) (mode : HighAnnularMode) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      (lowRhoPhysicalWeight parameters lower positive radius mode.val : ℂ) •
        (highPowerCurve lower highTiltExponent positive radius •
          actualFluxPhysicalSection lower positive bounded parameters field mode (radialClamp lower bounded.le radius)) =
        field.val.1 mode radius := by
  filter_upwards [weightedSection_originalStorage lower positive bounded
    (annularFluxRadialGraph lower positive bounded field mode), ae_restrict_mem measurableSet_Icc] with radius stored inside
  rw [← annularFluxRadialGraph_value lower positive bounded field mode]
  rw [stored]
  let vector : ComplexEuclidean 1 := weightedRadialSection 1 lower positive bounded
    (annularFluxRadialGraph lower positive bounded field mode) (radialClamp lower bounded.le radius)
  change (lowRhoPhysicalWeight parameters lower positive radius mode.val : ℂ) •
    (highPowerCurve lower highTiltExponent positive radius •
      (annularInversePhase parameters mode.val.2 (radialClamp lower bounded.le radius).val • vector)) = Real.sqrt radius • vector
  rw [radialClamp_eq lower bounded.le radius inside]
  exact originalHighSection_storageSmul parameters lower positive radius inside mode.val _

end Grad.AnnularSmoothCore

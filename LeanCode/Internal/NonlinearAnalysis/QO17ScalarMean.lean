import QO15ChartFirstJet
import RadialDifferential

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 800000

open Set MeasureTheory
open scoped ContDiff Interval

namespace Grad.NonlinearRange

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.NonlinearQuotient Grad.PhysicalFamily
open Grad.GaugeCoefficients.Radial

variable {parameters : PhaseParameters}

def rotationJet {dimension : ℕ} (field : ClosedJet dimension) : ClosedJet dimension :=
  coordinateJet 0 (partialJet 1 field) - coordinateJet 1 (partialJet 0 field)

theorem rotationJet_global_value {dimension : ℕ} (mapping : SpatialPlane → ComplexEuclidean dimension)
    (smooth : ContDiff ℝ ∞ mapping) (point : ClosedDisk) :
    (rotationJet (globalClosedJet mapping smooth)).value point =
      fderiv ℝ mapping point.val (planeQuarterTurn point.val) := by
  change (coordinateJet 0 (partialJet 1 (globalClosedJet mapping smooth)) -
    coordinateJet 1 (partialJet 0 (globalClosedJet mapping smooth))).value point = _
  rw [sub_eq_add_neg, closedJet_value_add, closedJet_value_neg, ContinuousMap.add_apply,
    ContinuousMap.neg_apply, coordinateJet_value, coordinateJet_value,
    partialJet_global_value, partialJet_global_value]
  conv_rhs => arg 2; rw [disk_basis_decomposition (planeQuarterTurn point.val)]
  rw [map_add, map_smul, map_smul]
  change point.val 0 • fderiv ℝ mapping point.val (spatialBasis 1) +
      -(point.val 1 • fderiv ℝ mapping point.val (spatialBasis 0)) =
    (-point.val 1) • fderiv ℝ mapping point.val (spatialBasis 0) +
      point.val 0 • fderiv ℝ mapping point.val (spatialBasis 1)
  module

theorem rotationJet_extension_value {dimension : ℕ} (field : ClosedJet dimension) (point : ClosedDisk) :
    (rotationJet field).value point = fderiv ℝ (smoothClosedExtension field) point.val
      (planeQuarterTurn point.val) := by
  have equality := rotationJet_global_value (smoothClosedExtension field) (smoothClosedExtension_smooth field) point
  rw [smoothClosedExtension_restricts] at equality
  exact equality

theorem planeRotationAction_hasDerivAt (point : SpatialPlane) (angle : ℝ) :
    HasDerivAt (fun angle => planeRotationAction angle point)
      (planeQuarterTurn (planeRotationAction angle point)) angle := by
  have derivative := ((Real.hasDerivAt_cos angle).smul_const point).add
    ((Real.hasDerivAt_sin angle).smul_const (planeQuarterTurn point))
  have turned : planeQuarterTurn (planeRotationAction angle point) =
      (-Real.sin angle) • point + Real.cos angle • planeQuarterTurn point := by
    rw [planeRotationAction_eq_cos_sin]
    change quarterTurnCLM (Real.cos angle • point + Real.sin angle • planeQuarterTurn point) = _
    rw [map_add, map_smul, map_smul, quarterTurnCLM_apply, quarterTurnCLM_apply, quarterTurn_twice]
    module
  rw [turned]
  change HasDerivAt (fun angle => Real.cos angle • point + Real.sin angle • planeQuarterTurn point)
    ((-Real.sin angle) • point + Real.cos angle • planeQuarterTurn point) angle at derivative
  simpa only [← planeRotationAction_eq_cos_sin] using derivative

/-- The literal angular average kills the Cartesian rotation derivative;
this is the fundamental theorem over one complete original angular period. -/
theorem angularCore_rotationCore_zero {dimension : ℕ} (field : ACore parameters dimension) :
    angularCore parameters 0 (rotationCore parameters field) = 0 := by
  apply acore_ext
  intro cell point
  change (angularClosedJet 0 (rotationJet (field.val cell))).value point = 0
  rw [angularClosedJet_value]
  simp only [angularCharacter_zero_mode, one_smul]
  let primitive : ℝ → ComplexEuclidean dimension := fun angle =>
    smoothClosedExtension (field.val cell) (planeRotationAction angle point.val)
  have derivative (angle : ℝ) : HasDerivAt primitive
      ((rotationJet (field.val cell)).value (Grad.GaugeCoefficients.Radial.rotatedPoint angle point)) angle := by
    have outer := (((smoothClosedExtension_smooth (field.val cell)).differentiable (by simp)).differentiableAt
      (x := planeRotationAction angle point.val)).hasFDerivAt
    have composed := outer.comp_hasDerivAt angle (planeRotationAction_hasDerivAt point.val angle)
    rw [rotationJet_extension_value]
    simpa only [primitive, Function.comp_def, Grad.GaugeCoefficients.Radial.rotatedPoint,
      physicalRotation_eq_orthogonal, planeRotationEquiv_apply] using composed
  have derivativeContinuous : Continuous (fun angle =>
      (rotationJet (field.val cell)).value (Grad.GaugeCoefficients.Radial.rotatedPoint angle point)) := by
    simpa only [angularCharacter_zero_mode, one_smul] using
      angularValueIntegrand_continuous 0 (rotationJet (field.val cell)) point
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun angle _ => derivative angle)
    (derivativeContinuous.intervalIntegrable 0 (2 * Real.pi))]
  have periodic : primitive (2 * Real.pi) = primitive 0 := by
    dsimp only [primitive]
    congr 1
    simpa only [zero_add] using physicalRotation_periodic point.val 0
  rw [periodic, sub_self, smul_zero]

theorem tameSeedScalar_mean_zero (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) :
    angularCore parameters 0 (tameSeedScalar parameters seed inside) = 0 := by
  rw [tameSeedScalar, map_smul, angularCore_rotationCore_zero, smul_zero]

theorem normalizedChart_mean_zero (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (state : ChartState parameters) (scalarMean : angularCore parameters 0 state.2.2 = 0) :
    angularCore parameters 0 (normalizedChart parameters seed inside state).2 = 0 := by
  change angularCore parameters 0 (tameSeedScalar parameters seed inside + state.2.2) = 0
  rw [map_add, tameSeedScalar_mean_zero, scalarMean, add_zero]

end Grad.NonlinearRange

import GC18CartesianMean
import AXL11AngularFourier

noncomputable section

set_option maxHeartbeats 1400000

open scoped Topology BigOperators Interval

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Radial Grad.NonlinearRange Grad.ChartAxisLift

theorem coreValue_constraintValueMap {parameters : PhaseParameters} {input output : ℕ}
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (field : ACore parameters input) (point : ClosedDisk) (angle : ℝ) :
    coreValue (Grad.Constraints.valueMapCore mapping parameters field) point angle = mapping (coreValue field point angle) := by
  unfold coreValue
  simp_rw [Grad.Constraints.valueMapCore_apply, valueMapJet_value, ← map_smul]
  exact (mapping.map_tsum (coreValue_summable field point angle)).symm

theorem coreValue_orthogonalCore {parameters : PhaseParameters} {dimension : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (field : ACore parameters dimension)
    (point : ClosedDisk) (angle : ℝ) :
    coreValue (orthogonalCore parameters orthogonal field) point angle =
      coreValue field (orthogonalClosedPoint orthogonal point) angle := by
  apply tsum_congr
  intro cell
  rfl

theorem coreValue_subtract {parameters : PhaseParameters} {dimension : ℕ}
    (first second : ACore parameters dimension) (point : ClosedDisk) (angle : ℝ) :
    coreValue (first - second) point angle = coreValue first point angle - coreValue second point angle := by
  have negate : -second = (-1 : ℂ) • second := (neg_one_smul ℂ second).symm
  rw [sub_eq_add_neg, negate, coreValue_add, coreValue_smul, neg_one_smul, ← sub_eq_add_neg]

theorem coreValue_equivariantAverageCore {parameters : PhaseParameters}
    (field : ACore parameters 2) (point : ClosedDisk) (angle : ℝ) :
    coreValue (equivariantAverageCore parameters field) point angle =
      closedEquivariantValue (fun other => coreValue field other angle) point := by
  change coreValue (Grad.Constraints.valueMapCore positiveHelicity parameters (angularCore parameters 1 field) +
    Grad.Constraints.valueMapCore negativeHelicity parameters (angularCore parameters (-1) field)) point angle = _
  rw [coreValue_add, coreValue_constraintValueMap, coreValue_constraintValueMap,
    coreValue_angularCore, coreValue_angularCore,
    closedEquivariantValue, closedCharacterProjection_integral, closedCharacterProjection_integral]

theorem coreValue_tangentialCore {parameters : PhaseParameters}
    (field : ACore parameters 2) (point : ClosedDisk) (angle : ℝ) :
    coreValue (tangentialCore parameters field) point angle =
      closedTangentialValue (fun other => coreValue field other angle) point := by
  change coreValue ((1 / 2 : ℂ) • (equivariantAverageCore parameters field -
    Grad.Constraints.valueMapCore reflectionValueMap parameters
      (orthogonalCore parameters cartesianReflectionEquiv (equivariantAverageCore parameters field)))) point angle = _
  rw [coreValue_smul, coreValue_subtract, coreValue_constraintValueMap, coreValue_orthogonalCore,
    coreValue_equivariantAverageCore, coreValue_equivariantAverageCore]
  rfl

/-- The nonsingular Cartesian C0 value formula is the full, untruncated
Fourier realization of the existing original all-grade core projection. -/
theorem coreValue_fixedComplementCore {parameters : PhaseParameters}
    (field : ACore parameters 3) (point : ClosedDisk) (angle : ℝ) :
    coreValue (fixedComplementCore parameters field) point angle =
      cartesianComplementValue (fun other => coreValue field other angle) point := by
  change coreValue (Grad.Constraints.valueMapCore planarInclusionMap parameters
      (tangentialCore parameters (Grad.Constraints.valueMapCore planarPartMap parameters field)) +
    Grad.Constraints.valueMapCore toroidalInclusionMap parameters
      (angularCore parameters 0 (Grad.Constraints.valueMapCore toroidalPartMap parameters field))) point angle = _
  rw [coreValue_add, coreValue_constraintValueMap, coreValue_constraintValueMap,
    coreValue_tangentialCore, coreValue_angularCore]
  simp_rw [coreValue_constraintValueMap]
  rw [cartesianComplementValue, closedCharacterProjection_integral]

end Grad.GaugeCoefficients.Physical.RadialLedger

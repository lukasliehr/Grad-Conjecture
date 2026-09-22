import GC18CartesianValue

noncomputable section

set_option maxHeartbeats 1400000

open Set MeasureTheory
open scoped Topology BigOperators Interval

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Radial Grad.PhysicalFamily

theorem closedRotation_continuous {Target : Type} [TopologicalSpace Target]
    (field : ClosedDisk → Target) (continuous : Continuous field) (point : ClosedDisk) :
    Continuous (fun angle : ℝ => field (Grad.GaugeCoefficients.Radial.rotatedPoint angle point)) := by
  have pairContinuous : Continuous (fun angle : ℝ => (angle, point)) :=
    continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => point))
  have orbit := Grad.GaugeCoefficients.Radial.continuous_rotatedPoint_joint.comp pairContinuous
  exact continuous.comp orbit

theorem closedCharacterIntegrand_continuous {dimension : ℕ} (mode : ℤ)
    (field : ClosedDisk → ComplexEuclidean dimension) (continuous : Continuous field) (point : ClosedDisk) :
    Continuous (fun angle : ℝ => angularCharacter mode angle • field (Grad.GaugeCoefficients.Radial.rotatedPoint angle point)) :=
  (angularCharacter_smooth mode).continuous.smul (closedRotation_continuous field continuous point)

theorem closedCharacterProjection_integral {dimension : ℕ} (mode : ℤ)
    (field : ClosedDisk → ComplexEuclidean dimension) (point : ClosedDisk) :
    closedCharacterProjection mode field point =
      (2 * Real.pi)⁻¹ • ∫ angle in (0 : ℝ)..2 * Real.pi,
        angularCharacter mode angle • field (Grad.GaugeCoefficients.Radial.rotatedPoint angle point) := by
  unfold closedCharacterProjection angularProjectionValue
  congr 1
  apply intervalIntegral.integral_congr
  intro angle _
  have identity := closedFieldExtension_value field (Grad.GaugeCoefficients.Radial.rotatedPoint angle point)
  simpa only [physicalRotation_eq_orthogonal, planeRotationEquiv_apply,
    Grad.GaugeCoefficients.Radial.rotatedPoint] using
      congrArg (fun value : ComplexEuclidean dimension => angularCharacter mode angle • value) identity

theorem closedCharacterProjection_mapped_integral {input output : ℕ}
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output) (mode : ℤ)
    (field : ClosedDisk → ComplexEuclidean input) (continuous : Continuous field) (point : ClosedDisk) :
    mapping (closedCharacterProjection mode field point) =
      (2 * Real.pi)⁻¹ • ∫ angle in (0 : ℝ)..2 * Real.pi,
        mapping (angularCharacter mode angle • field (Grad.GaugeCoefficients.Radial.rotatedPoint angle point)) := by
  rw [closedCharacterProjection_integral,
    mapping.intervalIntegral_comp_comm ((closedCharacterIntegrand_continuous mode field continuous point).intervalIntegrable _ _)]
  exact (mapping.restrictScalars ℝ).map_smul _ _

theorem closedEquivariantValue_integral (field : ClosedDisk → ComplexEuclidean 2)
    (continuous : Continuous field) (point : ClosedDisk) :
    closedEquivariantValue field point =
      (2 * Real.pi)⁻¹ • ∫ angle in (0 : ℝ)..2 * Real.pi,
        rotationValueMap (-angle) (field (Grad.GaugeCoefficients.Radial.rotatedPoint angle point)) := by
  rw [closedEquivariantValue, closedCharacterProjection_mapped_integral positiveHelicity 1 field continuous,
    closedCharacterProjection_mapped_integral negativeHelicity (-1) field continuous, ← smul_add]
  have firstIntegrable : IntervalIntegrable
      (fun angle => positiveHelicity (angularCharacter 1 angle • field (Grad.GaugeCoefficients.Radial.rotatedPoint angle point)))
      volume 0 (2 * Real.pi) := (positiveHelicity.continuous.comp
    (closedCharacterIntegrand_continuous 1 field continuous point)).intervalIntegrable (0 : ℝ) (2 * Real.pi)
  have secondIntegrable : IntervalIntegrable
      (fun angle => negativeHelicity (angularCharacter (-1) angle • field (Grad.GaugeCoefficients.Radial.rotatedPoint angle point)))
      volume 0 (2 * Real.pi) := (negativeHelicity.continuous.comp
    (closedCharacterIntegrand_continuous (-1) field continuous point)).intervalIntegrable (0 : ℝ) (2 * Real.pi)
  rw [← intervalIntegral.integral_add firstIntegrable secondIntegrable]
  congr 1
  apply intervalIntegral.integral_congr
  intro angle _
  simpa only [map_smul] using
    (rotationValueMap_character angle (field (Grad.GaugeCoefficients.Radial.rotatedPoint angle point))).symm

theorem closedEquivariantIntegrand_continuous (field : ClosedDisk → ComplexEuclidean 2)
    (continuous : Continuous field) (point : ClosedDisk) :
    Continuous (fun angle : ℝ => rotationValueMap (-angle) (field (Grad.GaugeCoefficients.Radial.rotatedPoint angle point))) := by
  have first := positiveHelicity.continuous.comp (closedCharacterIntegrand_continuous 1 field continuous point)
  have second := negativeHelicity.continuous.comp (closedCharacterIntegrand_continuous (-1) field continuous point)
  convert first.add second using 1
  funext angle
  simpa only [Function.comp_def, Pi.add_apply, map_smul] using
    rotationValueMap_character angle (field (Grad.GaugeCoefficients.Radial.rotatedPoint angle point))

end Grad.GaugeCoefficients.Physical.RadialLedger

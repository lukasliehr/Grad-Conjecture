import AKBE8LiteralRadialProjectionFidelity
import AKAY39ExactRawQradWeakTranspose

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped Interval ContDiff
namespace Grad.ActualCartesianWeakEquations
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.SourceCollarFullSource Grad.BoundaryTrace

private theorem rotated_symmetric_value (angle : ℝ) (value : ComplexEuclidean 2) :
    (1/2 : ℂ) • (rotationValueMap angle value + reflectionValueMap (rotationValueMap (-angle) value)) =
      value 0 • polarRadialVector angle := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [rotationValueMap_apply,reflectionValueMap,reflectionValueLinear,polarRadialVector] <;> ring

theorem closedEquivariantValue_axis_radial (field : ClosedDisk → ComplexEuclidean 2)
    (continuousField : Continuous field) (radius : ℝ) (bounded : |radius| ≤ 1) :
    closedEquivariantValue field (axisClosedPoint radius bounded) 0 =
      angularCoefficient (fun polar => polarRadialComponent polar
        (field (Grad.Constraints.polarClosedPoint radius bounded polar))) 0 := by
  have periodic : Function.Periodic (fun polar => polarRadialComponent polar
      (field (Grad.Constraints.polarClosedPoint radius bounded polar))) (2*Real.pi) := by
    intro polar
    simp only [polarClosedPoint_periodic radius bounded polar,polarRadialComponent,Real.cos_add_two_pi,Real.sin_add_two_pi]
  rw [originalAngularMean_interval _ periodic,closedEquivariantValue_integral field continuousField]
  let point := axisClosedPoint radius bounded
  let integrand := fun angle => rotationValueMap (-angle) (field (Grad.GaugeCoefficients.Radial.rotatedPoint angle point))
  have integrable : IntervalIntegrable integrand volume 0 (2*Real.pi) :=
    (closedEquivariantIntegrand_continuous field continuousField point).intervalIntegrable _ _
  change planarCoordinateMap 0 ((2*Real.pi)⁻¹ • ∫ angle in (0 : ℝ)..2*Real.pi,integrand angle) = _
  rw [(planarCoordinateMap 0).map_smul_of_tower,
    ← (planarCoordinateMap 0).intervalIntegral_comp_comm integrable]
  congr 1
  apply intervalIntegral.integral_congr
  intro angle _
  simp [integrand,point,planarCoordinateMap,rotationValueMap_apply,polarRadialComponent,Grad.Constraints.polarClosedPoint]
  rfl

/-- Literal I-(I+S)A/2 equals the SAME original radial mean removal. -/
theorem closedRadialReflection_polar (field : ClosedDisk → ComplexEuclidean 2)
    (continuousField : Continuous field) (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ) :
    field (Grad.Constraints.polarClosedPoint radius bounded angle) - (1/2 : ℂ) •
      (closedEquivariantValue field (Grad.Constraints.polarClosedPoint radius bounded angle) +
        reflectionValueMap (closedEquivariantValue field
          (orthogonalClosedPoint cartesianReflectionEquiv (Grad.Constraints.polarClosedPoint radius bounded angle)))) =
      closedOriginalRadialProjection field (Grad.Constraints.polarClosedPoint radius bounded angle) := by
  rw [reflectedPoint_polar]
  change field (Grad.Constraints.polarClosedPoint radius bounded angle) - (1/2 : ℂ) •
      (closedEquivariantValue field (Grad.GaugeCoefficients.Radial.rotatedPoint angle (axisClosedPoint radius bounded)) +
        reflectionValueMap (closedEquivariantValue field (Grad.GaugeCoefficients.Radial.rotatedPoint (-angle) (axisClosedPoint radius bounded)))) = _
  rw [closedEquivariantValue_rotation,closedEquivariantValue_rotation,rotated_symmetric_value,
    closedEquivariantValue_axis_radial field continuousField,closedOriginalRadialProjection_fourier field continuousField]

end Grad.ActualCartesianWeakEquations

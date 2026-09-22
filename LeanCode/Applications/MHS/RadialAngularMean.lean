import PolarAngularMean

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace Grad.Constraints

open Grad.ClosedJets Grad.GaugeCoefficients.Radial

def polarRadialComponent (angle : ℝ) (value : ComplexEuclidean 2) : ℂ :=
  (Real.cos angle : ℂ) * value 0 + (Real.sin angle : ℂ) * value 1

def polarRadialMean (field : ClosedJet 2) (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ) : ℂ :=
  (2 * Real.pi)⁻¹ • ∫ shift in (0 : ℝ)..2 * Real.pi,
    polarRadialComponent (shift + angle)
      (field.value (polarClosedPoint radius bounded (shift + angle)))

theorem polarRadialMean_independent (field : ClosedJet 2) (radius : ℝ)
    (bounded : |radius| ≤ 1) (angle : ℝ) :
    polarRadialMean field radius bounded angle = polarRadialMean field radius bounded 0 := by
  let integrand := fun theta => polarRadialComponent theta
    (field.value (polarClosedPoint radius bounded theta))
  have periodic : Function.Periodic integrand (2 * Real.pi) := by
    intro theta
    simp only [integrand, polarClosedPoint_periodic radius bounded theta,
      polarRadialComponent, Real.sin_add_two_pi, Real.cos_add_two_pi]
  change (2 * Real.pi)⁻¹ • (∫ shift in (0 : ℝ)..2 * Real.pi, integrand (shift + angle)) =
    (2 * Real.pi)⁻¹ • (∫ shift in (0 : ℝ)..2 * Real.pi, integrand (shift + 0))
  rw [intervalIntegral.integral_comp_add_right]
  simp only [zero_add, add_zero]
  congr 1
  simpa only [zero_add, add_comm] using periodic.intervalIntegral_add_eq angle 0

theorem equivariantAverage_axis_radial (field : ClosedJet 2) (radius : ℝ)
    (bounded : |radius| ≤ 1) :
    (equivariantAverageJet field).value (axisClosedPoint radius bounded) 0 =
      polarRadialMean field radius bounded 0 := by
  rw [equivariantAverageJet_value_negative]
  let point := axisClosedPoint radius bounded
  let integrand := fun angle => rotationValueMap (-angle) (field.value (rotatedPoint angle point))
  have integrable : IntervalIntegrable integrand volume 0 (2 * Real.pi) :=
    (equivariantIntegrand_continuous field point).intervalIntegrable _ _
  change planarCoordinateMap 0 ((2 * Real.pi)⁻¹ • ∫ angle in (0 : ℝ)..2 * Real.pi, integrand angle) = _
  have scalarLaw := ((planarCoordinateMap 0).restrictScalars ℝ).map_smul
    ((2 * Real.pi)⁻¹) (∫ angle in (0 : ℝ)..2 * Real.pi, integrand angle)
  change planarCoordinateMap 0 ((2 * Real.pi)⁻¹ • ∫ angle in (0 : ℝ)..2 * Real.pi, integrand angle) =
    (2 * Real.pi)⁻¹ • planarCoordinateMap 0 (∫ angle in (0 : ℝ)..2 * Real.pi, integrand angle) at scalarLaw
  rw [scalarLaw, ← (planarCoordinateMap 0).intervalIntegral_comp_comm integrable]
  unfold polarRadialMean
  congr 1
  apply intervalIntegral.integral_congr
  intro angle _
  simp [integrand, point, planarCoordinateMap, rotationValueMap_apply,
    polarRadialComponent, polarClosedPoint]
  rfl

/-- The first identity in N4: the actual equivariant average separates the
two literal polar angular means. -/
theorem equivariantAverageJet_polar_formula (field : ClosedJet 2) (radius : ℝ)
    (bounded : |radius| ≤ 1) (angle : ℝ) :
    (equivariantAverageJet field).value (polarClosedPoint radius bounded angle) =
      polarRadialMean field radius bounded angle • polarRadialVector angle +
        polarTangentialMean field radius bounded angle • polarTangentialVector angle := by
  rw [equivariantAverageJet_polar_value,
    polarRadialMean_independent field radius bounded angle,
    polarTangentialMean_independent field radius bounded angle,
    ← equivariantAverage_axis_radial, ← equivariantAverage_axis_tangential]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [rotationValueMap_apply, polarRadialVector, polarTangentialVector] <;> ring

end Grad.Constraints

import TangentialPolar

noncomputable section

open Set MeasureTheory
open scoped Interval Topology

namespace Grad.Constraints

open Grad.ClosedJets Grad.GaugeCoefficients.Radial

def planarCoordinateMap (coordinate : Fin 2) : ComplexEuclidean 2 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun value => value coordinate
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem equivariantIntegrand_continuous (field : ClosedJet 2) (point : ClosedDisk) :
    Continuous (fun angle : ℝ => rotationValueMap (-angle) (field.value (rotatedPoint angle point))) := by
  have first := positiveHelicity.continuous.comp (angularValueIntegrand_continuous 1 field point)
  have second := negativeHelicity.continuous.comp (angularValueIntegrand_continuous (-1) field point)
  convert first.add second using 1
  funext angle
  simpa only [Function.comp_def, Pi.add_apply, map_smul] using
    rotationValueMap_character angle (field.value (rotatedPoint angle point))

/-- The literal angular mean of the tangential component, on the circle of
radius r. The Cartesian projection itself never divides by r. -/
def polarTangentialMean (field : ClosedJet 2) (radius : ℝ) (bounded : |radius| ≤ 1)
    (angle : ℝ) : ℂ :=
  (2 * Real.pi)⁻¹ • ∫ shift in (0 : ℝ)..2 * Real.pi,
    polarTangentialComponent (shift + angle)
      (field.value (polarClosedPoint radius bounded (shift + angle)))

theorem polarTangentialMean_independent (field : ClosedJet 2) (radius : ℝ)
    (bounded : |radius| ≤ 1) (angle : ℝ) :
    polarTangentialMean field radius bounded angle = polarTangentialMean field radius bounded 0 := by
  let integrand := fun theta => polarTangentialComponent theta
    (field.value (polarClosedPoint radius bounded theta))
  have periodic : Function.Periodic integrand (2 * Real.pi) := by
    intro theta
    simp only [integrand, polarClosedPoint_periodic radius bounded theta,
      polarTangentialComponent, Real.sin_add_two_pi, Real.cos_add_two_pi]
  change (2 * Real.pi)⁻¹ • (∫ shift in (0 : ℝ)..2 * Real.pi, integrand (shift + angle)) =
    (2 * Real.pi)⁻¹ • (∫ shift in (0 : ℝ)..2 * Real.pi, integrand (shift + 0))
  rw [intervalIntegral.integral_comp_add_right]
  simp only [zero_add, add_zero]
  congr 1
  simpa only [zero_add, add_comm] using periodic.intervalIntegral_add_eq angle 0

theorem equivariantAverage_axis_tangential (field : ClosedJet 2) (radius : ℝ)
    (bounded : |radius| ≤ 1) :
    (equivariantAverageJet field).value (axisClosedPoint radius bounded) 1 =
      polarTangentialMean field radius bounded 0 := by
  rw [equivariantAverageJet_value_negative]
  let point := axisClosedPoint radius bounded
  let integrand := fun angle => rotationValueMap (-angle) (field.value (rotatedPoint angle point))
  have integrable : IntervalIntegrable integrand volume 0 (2 * Real.pi) :=
    (equivariantIntegrand_continuous field point).intervalIntegrable _ _
  change planarCoordinateMap 1 ((2 * Real.pi)⁻¹ • ∫ angle in (0 : ℝ)..2 * Real.pi, integrand angle) = _
  have scalarLaw := ((planarCoordinateMap 1).restrictScalars ℝ).map_smul
    ((2 * Real.pi)⁻¹) (∫ angle in (0 : ℝ)..2 * Real.pi, integrand angle)
  change planarCoordinateMap 1 ((2 * Real.pi)⁻¹ • ∫ angle in (0 : ℝ)..2 * Real.pi, integrand angle) =
    (2 * Real.pi)⁻¹ • planarCoordinateMap 1 (∫ angle in (0 : ℝ)..2 * Real.pi, integrand angle) at scalarLaw
  rw [scalarLaw, ← (planarCoordinateMap 1).intervalIntegral_comp_comm integrable]
  unfold polarTangentialMean
  congr 1
  apply intervalIntegral.integral_congr
  intro angle _
  simp [integrand, point, planarCoordinateMap, rotationValueMap_apply,
    polarTangentialComponent, polarClosedPoint]
  rfl

/-- N4: the Cartesian N3 projection equals e_theta times the literal
angular mean of f dot e_theta on every nonzero circle in the closed disk. -/
theorem tangentialJet_polar_formula (field : ClosedJet 2) (radius : ℝ)
    (bounded : |radius| ≤ 1) (angle : ℝ) :
    (tangentialJet field).value (polarClosedPoint radius bounded angle) =
      polarTangentialMean field radius bounded angle • polarTangentialVector angle := by
  rw [tangentialJet_polar_axis_value, equivariantAverage_axis_tangential,
    polarTangentialMean_independent field radius bounded angle]

theorem tangentialJet_polar_radial_zero (field : ClosedJet 2) (radius : ℝ)
    (bounded : |radius| ≤ 1) (angle : ℝ) :
    (Real.cos angle : ℂ) * (tangentialJet field).value (polarClosedPoint radius bounded angle) 0 +
      (Real.sin angle : ℂ) * (tangentialJet field).value (polarClosedPoint radius bounded angle) 1 = 0 := by
  rw [tangentialJet_polar_formula]
  simp [polarTangentialVector]
  ring

end Grad.Constraints

import GC18CartesianMean

noncomputable section

set_option maxHeartbeats 1400000

open Set MeasureTheory
open scoped Topology BigOperators Interval

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Radial Grad.PhysicalFamily

def closedPolarTangentialMean (field : ClosedDisk → ComplexEuclidean 2)
    (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ) : ℂ :=
  (2 * Real.pi)⁻¹ • ∫ shift in (0 : ℝ)..2 * Real.pi,
    polarTangentialComponent (shift + angle) (field (polarClosedPoint radius bounded (shift + angle)))

theorem closedPolarTangentialMean_independent (field : ClosedDisk → ComplexEuclidean 2)
    (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ) :
    closedPolarTangentialMean field radius bounded angle = closedPolarTangentialMean field radius bounded 0 := by
  let integrand := fun theta => polarTangentialComponent theta (field (polarClosedPoint radius bounded theta))
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

theorem closedEquivariantValue_axis_tangential (field : ClosedDisk → ComplexEuclidean 2)
    (continuous : Continuous field) (radius : ℝ) (bounded : |radius| ≤ 1) :
    closedEquivariantValue field (axisClosedPoint radius bounded) 1 =
      closedPolarTangentialMean field radius bounded 0 := by
  rw [closedEquivariantValue_integral field continuous]
  let point := axisClosedPoint radius bounded
  let integrand := fun angle => rotationValueMap (-angle) (field (Grad.GaugeCoefficients.Radial.rotatedPoint angle point))
  have integrable : IntervalIntegrable integrand volume 0 (2 * Real.pi) :=
    (closedEquivariantIntegrand_continuous field continuous point).intervalIntegrable _ _
  change planarCoordinateMap 1 ((2 * Real.pi)⁻¹ • ∫ angle in (0 : ℝ)..2 * Real.pi, integrand angle) = _
  have scalarLaw := ((planarCoordinateMap 1).restrictScalars ℝ).map_smul
    ((2 * Real.pi)⁻¹) (∫ angle in (0 : ℝ)..2 * Real.pi, integrand angle)
  change planarCoordinateMap 1 ((2 * Real.pi)⁻¹ • ∫ angle in (0 : ℝ)..2 * Real.pi, integrand angle) =
    (2 * Real.pi)⁻¹ • planarCoordinateMap 1 (∫ angle in (0 : ℝ)..2 * Real.pi, integrand angle) at scalarLaw
  rw [scalarLaw, ← (planarCoordinateMap 1).intervalIntegral_comp_comm integrable]
  unfold closedPolarTangentialMean
  congr 1
  apply intervalIntegral.integral_congr
  intro angle _
  simp [integrand, point, planarCoordinateMap, rotationValueMap_apply,
    polarTangentialComponent, polarClosedPoint]
  rfl

theorem closedTangentialValue_polar_formula (field : ClosedDisk → ComplexEuclidean 2)
    (continuous : Continuous field) (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ) :
    closedTangentialValue field (polarClosedPoint radius bounded angle) =
      closedPolarTangentialMean field radius bounded angle • polarTangentialVector angle := by
  rw [closedTangentialValue_polar, closedEquivariantValue_axis_tangential field continuous,
    closedPolarTangentialMean_independent field radius bounded angle]

theorem closedAngularMean_interval {Target : Type} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (field : ClosedDisk → Target) (point : ClosedDisk) :
    closedAngularMean field point =
      (2 * Real.pi)⁻¹ • ∫ angle in (0 : ℝ)..2 * Real.pi,
        field (Grad.GaugeCoefficients.Radial.rotatedPoint angle point) := by
  rw [closedAngularMean, normalizedAngularIntegral
    (fun angle => field (Grad.GaugeCoefficients.Radial.rotatedPoint angle point)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]

theorem storedTangentDot_polar (field : ClosedDisk → ComplexEuclidean 3)
    (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ) :
    storedTangentDot (polarClosedPoint radius bounded angle) (field (polarClosedPoint radius bounded angle)) =
      (radius : ℂ) • polarTangentialComponent angle (planarPartMap (field (polarClosedPoint radius bounded angle))) := by
  rw [storedTangentDot, polarClosedPoint_coordinates]
  change -((radius * Real.sin angle : ℝ) : ℂ) * (field (polarClosedPoint radius bounded angle)) 0 +
    ((radius * Real.cos angle : ℝ) : ℂ) * (field (polarClosedPoint radius bounded angle)) 1 =
    (radius : ℂ) * (-(Real.sin angle : ℂ) * (field (polarClosedPoint radius bounded angle)) 0 +
      (Real.cos angle : ℂ) * (field (polarClosedPoint radius bounded angle)) 1)
  push_cast
  ring

theorem closedMean_tangentDot_polar (field : ClosedDisk → ComplexEuclidean 3)
    (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ) :
    closedAngularMean (fun other => storedTangentDot other (field other)) (polarClosedPoint radius bounded angle) =
      (radius : ℂ) • closedPolarTangentialMean (fun other => planarPartMap (field other)) radius bounded angle := by
  rw [closedAngularMean_interval]
  simp_rw [rotatedPoint_polar, storedTangentDot_polar]
  rw [intervalIntegral.integral_smul]
  exact smul_comm ((2 * Real.pi)⁻¹ : ℝ) (radius : ℂ)
    (∫ shift in (0 : ℝ)..2 * Real.pi,
      polarTangentialComponent (shift + angle) (planarPartMap (field (polarClosedPoint radius bounded (shift + angle)))))

end Grad.GaugeCoefficients.Physical.RadialLedger

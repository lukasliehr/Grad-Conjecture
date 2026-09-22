import AngularSmoothProjection

noncomputable section

open Set MeasureTheory
open scoped ContDiff Interval Topology

namespace Grad.Constraints

open Grad.ClosedJets Grad.PhysicalFamily

theorem angularProjectionValue_rotation {dimension : ℕ} (mode : ℤ)
    (field : SpatialPlane → ComplexEuclidean dimension) (angle : ℝ) (point : SpatialPlane) :
    angularProjectionValue mode field (planeRotationAction angle point) =
      angularCharacter mode (-angle) • angularProjectionValue mode field point := by
  let integrand : ℝ → ComplexEuclidean dimension := fun theta =>
    angularCharacter mode theta • field (planeRotationAction theta point)
  have periodic : Function.Periodic integrand (2 * Real.pi) := by
    intro theta
    simp only [integrand, angularCharacter_periodic mode theta, physicalRotation_periodic point theta]
  have shiftedIntegral :
      (∫ theta in (0 : ℝ)..2 * Real.pi,
        angularCharacter mode theta • field (planeRotationAction (theta + angle) point)) =
      angularCharacter mode (-angle) • ∫ theta in (0 : ℝ)..2 * Real.pi, integrand theta := by
    calc
      _ = ∫ theta in (0 : ℝ)..2 * Real.pi,
          angularCharacter mode (-angle) • integrand (theta + angle) := by
        apply intervalIntegral.integral_congr
        intro theta _
        simp only [integrand, ← mul_smul, angularCharacter_inverse_factor]
      _ = angularCharacter mode (-angle) •
          ∫ theta in angle..(2 * Real.pi + angle), integrand theta := by
        rw [intervalIntegral.integral_smul, intervalIntegral.integral_comp_add_right]
        simp only [zero_add]
      _ = _ := by
        congr 1
        simpa only [zero_add, add_comm] using periodic.intervalIntegral_add_eq angle 0
  unfold angularProjectionValue
  simp_rw [physicalRotation_add]
  rw [shiftedIntegral]
  exact smul_comm _ _ _

theorem angularProjectionValue_projection {dimension : ℕ} (first second : ℤ)
    (field : SpatialPlane → ComplexEuclidean dimension) (point : SpatialPlane) :
    angularProjectionValue first (angularProjectionValue second field) point =
      if first = second then angularProjectionValue first field point else 0 := by
  rw [angularProjectionValue]
  simp_rw [angularProjectionValue_rotation, angularCharacter_neg_angle,
    ← mul_smul, angularCharacter_mul]
  rw [angularCharacter_normalized_integral]
  by_cases equalModes : first = second
  · subst second
    simp
  · simp [equalModes, add_neg_eq_zero]

theorem angularProjectionValue_congr_closed {dimension : ℕ} (mode : ℤ)
    {first second : SpatialPlane → ComplexEuclidean dimension}
    (agree : ∀ point : ClosedDisk, first point.val = second point.val) (point : ClosedDisk) :
    angularProjectionValue mode first point.val = angularProjectionValue mode second point.val := by
  unfold angularProjectionValue
  congr 1
  apply intervalIntegral.integral_congr
  intro angle _
  apply congrArg (fun value => angularCharacter mode angle • value)
  have equality := agree (Grad.GaugeCoefficients.Radial.rotatedPoint angle point)
  simpa only [physicalRotation_eq_orthogonal,
    Grad.GaugeCoefficients.Radial.planeRotationEquiv_apply,
    Grad.GaugeCoefficients.Radial.rotatedPoint] using equality

theorem angularClosedJet_projection {dimension : ℕ} (first second : ℤ)
    (field : ClosedJet dimension) :
    angularClosedJet first (angularClosedJet second field) =
      if first = second then angularClosedJet first field else 0 := by
  have extensionEquality : ∀ point : ClosedDisk,
      smoothClosedExtension (angularClosedJet second field) point.val =
        angularProjectionValue second (smoothClosedExtension field) point.val := by
    intro point
    rw [smoothClosedExtension_value]
    rfl
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change angularProjectionValue first
    (smoothClosedExtension (angularClosedJet second field)) point.val = _
  rw [angularProjectionValue_congr_closed first extensionEquality,
    angularProjectionValue_projection]
  by_cases equalModes : first = second <;> simp [equalModes, angularClosedJet, globalClosedJet_value]

end Grad.Constraints

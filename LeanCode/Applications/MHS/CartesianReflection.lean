import AngularCore

noncomputable section

open Set MeasureTheory
open scoped ContDiff Interval Topology

namespace Grad.Constraints

open Grad.ClosedJets Grad.PhysicalFamily Grad.GaugeCoefficients.Radial

/-- The manuscript's S=diag(1,-1), distinct from the coordinate-exchange
reflection used by the generic coefficient infrastructure. -/
def cartesianReflection (point : SpatialPlane) : SpatialPlane :=
  WithLp.toLp 2 ![point 0, -point 1]

theorem cartesianReflection_norm (point : SpatialPlane) :
    ‖cartesianReflection point‖ = ‖point‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  simp only [Fin.sum_univ_two]
  change Real.sqrt (‖point 0‖ ^ 2 + ‖-point 1‖ ^ 2) = _
  rw [norm_neg]

def cartesianReflectionEquiv : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane where
  toFun := cartesianReflection
  map_add' first second := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp [cartesianReflection]
    ring
  map_smul' scalar point := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp [cartesianReflection]
  norm_map' := cartesianReflection_norm
  invFun := cartesianReflection
  left_inv point := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp [cartesianReflection]
  right_inv point := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp [cartesianReflection]

theorem rotation_reflection (angle : ℝ) (point : SpatialPlane) :
    planeRotationAction angle (cartesianReflection point) =
      cartesianReflection (planeRotationAction (-angle) point) := by
  simp only [physicalRotation_eq_orthogonal, planeRotationEquiv_apply]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [planeRotation, cartesianReflection]
  ring

theorem cartesianReflection_involutive (point : SpatialPlane) :
    cartesianReflection (cartesianReflection point) = point :=
  cartesianReflectionEquiv.left_inv point

theorem periodic_intervalIntegral_neg {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (field : ℝ → Value) (period : ℝ)
    (periodic : Function.Periodic field period) :
    (∫ angle in (0 : ℝ)..period, field (-angle)) =
      ∫ angle in (0 : ℝ)..period, field angle := by
  rw [intervalIntegral.integral_comp_neg, neg_zero]
  simpa only [neg_add_cancel, zero_add] using periodic.intervalIntegral_add_eq (-period) 0

theorem angularProjectionValue_reflection {dimension : ℕ} (mode : ℤ)
    (field : SpatialPlane → ComplexEuclidean dimension) (point : SpatialPlane) :
    angularProjectionValue mode field (cartesianReflection point) =
      angularProjectionValue (-mode) (fun source => field (cartesianReflection source)) point := by
  let integrand : ℝ → ComplexEuclidean dimension := fun angle =>
    angularCharacter (-mode) angle • field (cartesianReflection (planeRotationAction angle point))
  have periodic : Function.Periodic integrand (2 * Real.pi) := by
    intro angle
    simp only [integrand, angularCharacter_periodic (-mode) angle, physicalRotation_periodic point angle]
  unfold angularProjectionValue
  simp_rw [rotation_reflection]
  have equality : (fun angle => angularCharacter mode angle •
      field (cartesianReflection (planeRotationAction (-angle) point))) =
      fun angle => integrand (-angle) := by
    funext angle
    simp only [integrand, angularCharacter_neg_angle, neg_neg]
  rw [equality, periodic_intervalIntegral_neg integrand _ periodic]

theorem angularClosedJet_reflection {dimension : ℕ} (mode : ℤ) (field : ClosedJet dimension) :
    orthogonalJet cartesianReflectionEquiv (angularClosedJet mode field) =
      angularClosedJet (-mode) (orthogonalJet cartesianReflectionEquiv field) := by
  have extensionEquality : ∀ point : ClosedDisk,
      smoothClosedExtension (orthogonalJet cartesianReflectionEquiv field) point.val =
        smoothClosedExtension field (cartesianReflection point.val) := by
    intro point
    rw [smoothClosedExtension_value]
    exact (smoothClosedExtension_value field
      (orthogonalClosedPoint cartesianReflectionEquiv point)).symm
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change angularProjectionValue mode (smoothClosedExtension field) (cartesianReflection point.val) =
    angularProjectionValue (-mode)
      (smoothClosedExtension (orthogonalJet cartesianReflectionEquiv field)) point.val
  rw [angularProjectionValue_reflection]
  exact (angularProjectionValue_congr_closed (-mode) extensionEquality point).symm

end Grad.Constraints

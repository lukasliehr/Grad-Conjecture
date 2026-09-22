import AKAE2SameSpatialCartesianField

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter
open scoped Topology ContDiff
namespace Grad.ActualCartesianDescent
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.BoundaryLift Grad.SourceCollarDivision
open Grad.CircularHighRegularity Grad.BoundaryTrace Grad.PhysicalFamily

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : ℝ × (ℝ × ℝ) → E) (lower upper : ℝ)
    (smooth : ContDiffOn ℝ ∞ field (Ioo lower upper ×ˢ (univ : Set (ℝ × ℝ))))
    (periodic : ∀ radius axial,Function.Periodic (fun polar => field (radius,polar,axial)) (2*Real.pi))
    (radius : ℝ) (positive : 0 < radius) (inside : radius ∈ Ioo lower upper) (polar axial : ℝ)
include smooth periodic positive inside

 theorem cartesianPhysicalField_smoothAt_polar :
    ContDiffAt ℝ ∞ (cartesianPhysicalField field) (polarPlane (radius,polar),axial) := by
  apply cartesianPhysicalField_smoothAt field lower upper smooth periodic _
  · apply norm_ne_zero_iff.mp
    rw [polarPlane_norm,abs_of_pos positive]
    exact positive.ne'
  · simpa only [polarPlane_norm,abs_of_pos positive] using inside

/-- Actual radial differentiation through the same Cartesian field. -/
theorem cartesianPhysicalField_radial_hasDerivAt :
    HasDerivAt (fun current => field (current,polar,axial))
      (fderiv ℝ (cartesianPhysicalField field) (polarPlane (radius,polar),axial)
        (radialDirection polar,0)) radius := by
  have derivative := ((cartesianPhysicalField_smoothAt_polar field lower upper smooth periodic radius positive inside polar axial).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt radius
      ((polarPlane_radial_derivative radius polar).prodMk (hasDerivAt_const radius axial))
  apply derivative.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds positive] with current currentPositive
  exact (cartesianPhysicalField_at_polar field periodic current currentPositive polar axial).symm

/-- The angular direction is exactly r times the quarter-turned radial unit vector. -/
theorem cartesianPhysicalField_angular_hasDerivAt :
    HasDerivAt (fun current => field (radius,current,axial))
      (fderiv ℝ (cartesianPhysicalField field) (polarPlane (radius,polar),axial)
        (radius • planeQuarterTurn (radialDirection polar),0)) polar := by
  have derivative := ((cartesianPhysicalField_smoothAt_polar field lower upper smooth periodic radius positive inside polar axial).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt polar
      ((polarPlane_angular_derivative radius polar).prodMk (hasDerivAt_const polar axial))
  simpa only [Function.comp_def,cartesianPhysicalField_at_polar field periodic radius positive] using derivative

theorem cartesianPhysicalField_axial_hasDerivAt :
    HasDerivAt (fun current => field (radius,polar,current))
      (fderiv ℝ (cartesianPhysicalField field) (polarPlane (radius,polar),axial) (0,1)) axial := by
  have derivative := ((cartesianPhysicalField_smoothAt_polar field lower upper smooth periodic radius positive inside polar axial).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt axial
      ((hasDerivAt_const axial (polarPlane (radius,polar))).prodMk (hasDerivAt_id axial))
  simpa only [Function.comp_def,cartesianPhysicalField_at_polar field periodic radius positive] using derivative

end Grad.ActualCartesianDescent

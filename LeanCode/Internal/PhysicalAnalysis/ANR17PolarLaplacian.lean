import ANR16PolarDerivatives

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.BoundaryTrace
open Grad.NonlinearQuotient Grad.PhysicalFamily

/-- Literal Cartesian Laplacian in polar coordinates. The multiplied form
is valid even at the axis; division is used only on a positive closed collar. -/
theorem polar_laplacian_multiplied {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : SpatialPlane → Value) (smooth : ContDiff ℝ ∞ field) (radius angle : ℝ) :
    radius ^ 2 • diskLaplacian field (polarPlane (radius, angle)) =
      radius ^ 2 • radialIter 2 (field ∘ polarPlane) (radius, angle) +
      radius • radialField (field ∘ polarPlane) (radius, angle) +
      angularJet 2 (field ∘ polarPlane) (radius, angle) := by
  have trace := bilinear_radial_trace (fderiv ℝ (fderiv ℝ field) (polarPlane (radius, angle))) (radialDirection angle)
  rw [radialDirection_norm, one_pow, one_smul] at trace
  have laplacian : fderiv ℝ (fderiv ℝ field) (polarPlane (radius, angle)) (radialDirection angle) (radialDirection angle) +
      fderiv ℝ (fderiv ℝ field) (polarPlane (radius, angle))
        (planeQuarterTurn (radialDirection angle)) (planeQuarterTurn (radialDirection angle)) =
      diskLaplacian field (polarPlane (radius, angle)) := by
    simpa only [diskLaplacian, Fin.sum_univ_two] using trace
  rw [polar_radial_first field smooth, polar_radial_second field smooth, polar_angular_second field smooth,
    ← laplacian]
  module

end Grad.CircularHighRegularity

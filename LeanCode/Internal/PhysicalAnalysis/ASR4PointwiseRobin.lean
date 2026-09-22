import ASR3BoundaryCoefficient

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.ActualSmoothRobin
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.ActualOuterCollar Grad.SourceCollarRestriction
open Grad.SourceCollarDivision Grad.BoundaryTrace Grad.NonlinearRange

local instance : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

/-- Fourier completeness in the actual ordinary boundary measure, followed
by continuity, gives the entire continuous Robin row. -/
theorem sameH1_robin_boundary_zero (parameter : ℝ) (source : highDiskL2) (solution : ClosedJet 1)
    (same : diskCoreInto solution = (highRobinWeakInverse parameter source).val) :
    closedBoundaryValue (robinResidualJet solution) = 0 := by
  have coefficients := sameH1_robin_boundary_coefficients parameter source solution same
  have squared := coreBoundaryL2_fourier_norm_sq (robinResidualJet solution)
  rw [coefficients, norm_zero, zero_pow (by decide), mul_zero] at squared
  have normZero : ‖coreBoundaryL2 (robinResidualJet solution)‖ = 0 := by
    nlinarith [norm_nonneg (coreBoundaryL2 (robinResidualJet solution))]
  apply ContinuousMap.toLp_injective (p := 2) volume (𝕜 := ℂ)
  change coreBoundaryL2 (robinResidualJet solution) = _
  rw [norm_eq_zero.mp normZero, map_zero]

/-- The derivative is evaluated in the outward unit normal, which is the
point itself on the unit circle. The value is that of the original jet. -/
theorem sameH1_pointwise_robin (parameter : ℝ) (source : highDiskL2) (solution : ClosedJet 1)
    (same : diskCoreInto solution = (highRobinWeakInverse parameter source).val) (angle : CellCircle) :
    fderiv ℝ (smoothClosedExtension solution) (boundaryCirclePoint angle) (boundaryCirclePoint angle) +
      (2 : ℝ) • solution.value (boundaryDiskPoint angle) = 0 := by
  have value := congrArg (fun field : C(CellCircle, ComplexEuclidean 1) => field angle)
    (sameH1_robin_boundary_zero parameter source solution same)
  change (robinResidualJet solution).value (boundaryDiskPoint angle) = 0 at value
  unfold robinResidualJet at value
  rw [closedJet_value_add, ContinuousMap.add_apply, closedJet_value_smul, ContinuousMap.smul_apply,
    eulerJet_extension_value] at value
  exact value

end Grad.ActualSmoothRobin

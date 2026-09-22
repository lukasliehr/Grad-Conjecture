import ASR4PointwiseRobin

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.ActualSmoothRobin
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.BoundaryTrace Grad.NonlinearRange
open Grad.OrdinaryDiskFaithfulness Grad.ActualFiniteGlobal

/-- The accepted finite smooth inverse satisfies the complete continuous
Robin boundary equation, for the same selected source and full H1 graph. -/
theorem finiteInverseClosedJet_robin (parameters : PhaseParameters) (modes : Finset ℤ)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core) :
    closedBoundaryValue (robinResidualJet (finiteInverseClosedJet parameters modes parameter source core same)) = 0 :=
  sameH1_robin_boundary_zero parameter (highL2SelectedModes modes source) _
    (finiteInverseClosedJet_H1 parameters modes parameter source core same)

theorem finiteInverseClosedJet_pointwise_robin (parameters : PhaseParameters) (modes : Finset ℤ)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core)
    (angle : CellCircle) :
    let solution := finiteInverseClosedJet parameters modes parameter source core same
    fderiv ℝ (smoothClosedExtension solution) (boundaryCirclePoint angle) (boundaryCirclePoint angle) +
      (2 : ℝ) • solution.value (boundaryDiskPoint angle) = 0 :=
  sameH1_pointwise_robin parameter (highL2SelectedModes modes source) _
    (finiteInverseClosedJet_H1 parameters modes parameter source core same) angle

/-- One actual finite inverse jet, exact full H1 identity, every ordinary
Sobolev representative, and the literal continuous and pointwise Robin law. -/
theorem actualFiniteSmoothRobinInverse (parameters : PhaseParameters) (modes : Finset ℤ)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core) :
    ∃ solution : ClosedJet 1,
      diskCoreInto solution = (highRobinWeakInverse parameter (highL2SelectedModes modes source)).val ∧
      (∀ grade, unitDiskCoreInto grade solution =
        finiteGlobalRepresentative parameters modes parameter source core same grade) ∧
      closedBoundaryValue (robinResidualJet solution) = 0 ∧
      ∀ angle : CellCircle,
        fderiv ℝ (smoothClosedExtension solution) (boundaryCirclePoint angle) (boundaryCirclePoint angle) +
          (2 : ℝ) • solution.value (boundaryDiskPoint angle) = 0 :=
  ⟨finiteInverseClosedJet parameters modes parameter source core same,
    finiteInverseClosedJet_H1 parameters modes parameter source core same,
    finiteInverseClosedJet_grade parameters modes parameter source core same,
    finiteInverseClosedJet_robin parameters modes parameter source core same,
    finiteInverseClosedJet_pointwise_robin parameters modes parameter source core same⟩

end Grad.ActualSmoothRobin

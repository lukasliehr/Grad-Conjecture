import ASP6LiteralScalarEquation
import AUB11ActualSmoothRobinConsumer

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.ActualSmoothPDE
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.BoundaryTrace Grad.ActualSmoothRobin
open Grad.OrdinaryDiskFaithfulness Grad.ActualUniformGlobal Grad.OrdinaryDiskCalculus
attribute [local instance] unitNormedSpace

theorem finiteInverseClosedJet_scalar (parameters : PhaseParameters) (modes : Finset ℤ)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core) :
    scalarResidualJet parameter (finiteInverseClosedJet parameters modes parameter source core same) =
      selectedAngularJet modes core := by
  apply sameH1_scalarResidual parameter (highL2SelectedModes modes source)
  · exact Grad.ActualFiniteGlobal.selectedSource_core modes source core same
  · exact finiteInverseClosedJet_H1 parameters modes parameter source core same

theorem actualSmoothInverse_scalar (parameters : PhaseParameters) (parameter : ℝ)
    (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core) :
    scalarResidualJet parameter (actualSmoothInverse parameters parameter core) = core :=
  sameH1_scalarResidual parameter source core same _
    (actualSmoothInverse_H1_of_high parameters parameter source core same)

theorem actualSmoothInverse_pointwise_scalar (parameters : PhaseParameters) (parameter : ℝ)
    (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core)
    (point : ClosedDisk) :
    -Grad.NonlinearQuotient.diskLaplacian (smoothClosedExtension (actualSmoothInverse parameters parameter core)) point.val +
      ((parameter ^ 2 : ℝ) : ℂ) • (smoothDiskBJet (actualSmoothInverse parameters parameter core)).value point = core.value point :=
  sameH1_pointwise_scalar parameter source core same _
    (actualSmoothInverse_H1_of_high parameters parameter source core same) point

/-- The same actual all-mode smooth inverse has the original uniform
Sobolev gain, exact scalar jet PDE, literal Cartesian equation everywhere,
and the complete continuous and outward pointwise Robin boundary law. -/
theorem actualSmoothStrongRobinInverse (parameters : PhaseParameters) (parameter : ℝ)
    (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core) :
    ∃ solution : ClosedJet 1,
      diskCoreInto solution = (highRobinWeakInverse parameter source).val ∧
      (∀ grade ceiling, |parameter| ≤ ceiling →
        ‖unitDiskCoreInto (grade + 2) solution‖ ≤ finiteInverseConstant grade ceiling * ‖unitDiskCoreInto grade core‖) ∧
      scalarResidualJet parameter solution = core ∧
      (∀ point : ClosedDisk,
        -Grad.NonlinearQuotient.diskLaplacian (smoothClosedExtension solution) point.val +
          ((parameter ^ 2 : ℝ) : ℂ) • (smoothDiskBJet solution).value point = core.value point) ∧
      (∀ mode ∈ lowAngularModes, angularClosedJet mode solution = 0) ∧
      closedBoundaryValue (robinResidualJet solution) = 0 ∧
      ∀ angle : CellCircle,
        fderiv ℝ (smoothClosedExtension solution) (boundaryCirclePoint angle) (boundaryCirclePoint angle) +
          (2 : ℝ) • solution.value (boundaryDiskPoint angle) = 0 := by
  let solution := actualSmoothInverse parameters parameter core
  have exactH1 := actualSmoothInverse_H1_of_high parameters parameter source core same
  refine ⟨solution, exactH1, ?_, actualSmoothInverse_scalar parameters parameter source core same,
    actualSmoothInverse_pointwise_scalar parameters parameter source core same, ?_,
    sameH1_robin_boundary_zero parameter source solution exactH1,
    sameH1_pointwise_robin parameter source solution exactH1⟩
  · intro grade ceiling bounded
    exact actualSmoothInverse_bound grade ceiling parameters parameter bounded core
  · intro mode low
    exact sameH1_low_projection_zero parameter source solution exactH1 mode low

end Grad.ActualSmoothPDE

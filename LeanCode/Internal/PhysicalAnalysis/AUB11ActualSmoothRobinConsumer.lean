import AUB10ActualSmoothInverse
import ASR5ActualFiniteRobin

noncomputable section
set_option maxHeartbeats 1200000
namespace Grad.ActualUniformGlobal
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.OrdinaryDiskFaithfulness Grad.OrdinaryDiskCalculus Grad.ActualSmoothRobin Grad.BoundaryTrace
attribute [local instance] unitNormedSpace

theorem actualSmoothInverse_H1_of_high (parameters : PhaseParameters) (parameter : ℝ)
    (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core) :
    diskCoreInto (actualSmoothInverse parameters parameter core) = (highRobinWeakInverse parameter source).val := by
  have projected : highL2Core core = source := by
    apply Subtype.ext
    change highL2Projection (closedL2Core core) = source.val
    exact (congrArg highL2Projection same.symm).trans (highL2Projection_fixed source)
  exact (actualSmoothInverse_H1 parameters parameter core).trans
    (congrArg (fun field : highDiskL2 => (highRobinWeakInverse parameter field).val) projected)

/-- The actual full high inverse is one smooth closed jet, chosen before all
grades, with the exact original Sobolev gain, full H1 identity, Cartesian
weak PDE, spectral exclusion, and continuous and pointwise Robin equation. -/
theorem actualSmoothHomogeneousRobinInverse (parameters : PhaseParameters) (parameter : ℝ)
    (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core) :
    ∃ solution : ClosedJet 1,
      diskCoreInto solution = (highRobinWeakInverse parameter source).val ∧
      (∀ grade ceiling, |parameter| ≤ ceiling →
        ‖unitDiskCoreInto (grade + 2) solution‖ ≤ finiteInverseConstant grade ceiling * ‖unitDiskCoreInto grade core‖) ∧
      HasDiskWeakLaplacian (closedL2Core solution) (weakLaplacianValue parameter source) ∧
      (∀ mode ∈ lowAngularModes, angularClosedJet mode solution = 0) ∧
      closedBoundaryValue (robinResidualJet solution) = 0 ∧
      ∀ angle : CellCircle,
        fderiv ℝ (smoothClosedExtension solution) (boundaryCirclePoint angle) (boundaryCirclePoint angle) +
          (2 : ℝ) • solution.value (boundaryDiskPoint angle) = 0 := by
  let solution := actualSmoothInverse parameters parameter core
  have exactH1 := actualSmoothInverse_H1_of_high parameters parameter source core same
  have bulk : closedL2Core solution = highDiskBulk (highRobinWeakInverse parameter source) :=
    (Grad.CircularHighWeak.diskBulk_core solution).symm.trans (congrArg diskBulk exactH1)
  refine ⟨solution, exactH1, ?_, ?_, ?_,
    sameH1_robin_boundary_zero parameter source solution exactH1,
    sameH1_pointwise_robin parameter source solution exactH1⟩
  · intro grade ceiling bounded
    exact actualSmoothInverse_bound grade ceiling parameters parameter bounded core
  · exact bulk.symm ▸ weakInverse_distribution parameter source
  · intro mode low
    exact sameH1_low_projection_zero parameter source solution exactH1 mode low

end Grad.ActualUniformGlobal

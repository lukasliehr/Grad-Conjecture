import ASP4SmoothMultiplier
import ASP5WeakSmoothCore

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.ActualSmoothPDE
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.GenericCarriers Grad.NonlinearDivision

/-- Literal scalar operator −Δ+k²B on genuine closed jets. The B jet has
exactly the accepted diskB zero-low extension. -/
def scalarResidualJet (parameter : ℝ) (field : ClosedJet 1) : ClosedJet 1 :=
  -laplacianJet field + ((parameter ^ 2 : ℝ) : ℂ) • smoothDiskBJet field

theorem scalarResidualJet_bulk (parameter : ℝ) (field : ClosedJet 1) :
    closedL2Core (scalarResidualJet parameter field) =
      -closedL2Core (laplacianJet field) + ((parameter ^ 2 : ℝ) : ℂ) • diskB (closedL2Core field) := by
  unfold scalarResidualJet
  rw [map_add, map_neg, map_smul, smoothDiskBJet_bulk]

theorem sameH1_scalarResidual_bulk (parameter : ℝ) (source : highDiskL2) (solution : ClosedJet 1)
    (same : diskCoreInto solution = (highRobinWeakInverse parameter source).val) :
    closedL2Core (scalarResidualJet parameter solution) = source.val := by
  have bulk : closedL2Core solution = highDiskBulk (highRobinWeakInverse parameter source) :=
    (Grad.CircularHighRegularity.diskBulk_core solution).symm.trans (congrArg diskBulk same)
  rw [scalarResidualJet_bulk, sameH1_laplacian_bulk parameter source solution same, bulk]
  unfold weakLaplacianValue
  abel

/-- Exact strong scalar equation for any genuine smooth representative of
the actual H1 inverse and any genuine smooth representative of its source. -/
theorem sameH1_scalarResidual (parameter : ℝ) (source : highDiskL2)
    (core : ClosedJet 1) (sourceSame : source.val = closedL2Core core) (solution : ClosedJet 1)
    (same : diskCoreInto solution = (highRobinWeakInverse parameter source).val) :
    scalarResidualJet parameter solution = core := by
  apply closedL2Core_injective
  exact (sameH1_scalarResidual_bulk parameter source solution same).trans sourceSame

/-- Cartesian pointwise PDE, including the axis. Equality on the closed
disk also gives the requested interior equation directly. -/
theorem sameH1_pointwise_scalar (parameter : ℝ) (source : highDiskL2)
    (core : ClosedJet 1) (sourceSame : source.val = closedL2Core core) (solution : ClosedJet 1)
    (same : diskCoreInto solution = (highRobinWeakInverse parameter source).val) (point : ClosedDisk) :
    -Grad.NonlinearQuotient.diskLaplacian (smoothClosedExtension solution) point.val +
      ((parameter ^ 2 : ℝ) : ℂ) • (smoothDiskBJet solution).value point = core.value point := by
  have value := congrArg (fun jet : ClosedJet 1 => jet.value point)
    (sameH1_scalarResidual parameter source core sourceSame solution same)
  simp only [scalarResidualJet, closedJet_value_add, closedJet_value_neg, closedJet_value_smul,
    ContinuousMap.add_apply, ContinuousMap.neg_apply, ContinuousMap.smul_apply] at value
  rw [laplacianJet_value, laplacianCoefficient_extension] at value
  exact value

end Grad.ActualSmoothPDE

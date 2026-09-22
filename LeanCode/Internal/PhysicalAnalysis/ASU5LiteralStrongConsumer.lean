import ASU4StrongRobinUniqueness
import ASP7ActualStrongConsumer

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open Set MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.SmoothRobinUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.BoundaryTrace
open Grad.CircularHighRegularity Grad.CircularHighWeak Grad.NonlinearDivision Grad.NonlinearRange
open Grad.ActualSmoothPDE Grad.ActualUniformGlobal Grad.ActualSmoothRobin

/-- The scalar expression in the Green identity is exactly the accepted smooth
scalar operator, including its actual nonlocal B and all five excluded modes. -/
theorem strongResidualBulk_scalar (parameter : ℝ) (field : ClosedJet 1) :
    strongResidualBulk parameter field = closedL2Core (scalarResidualJet parameter field) :=
  (scalarResidualJet_bulk parameter field).symm

/-- Same genuine scalar jet PDE and same pointwise Robin data imply uniqueness. -/
theorem scalarRobin_unique (parameter : ℝ) (first second : ClosedJet 1)
    (firstHigh : closedL2Core first ∈ highDiskL2) (secondHigh : closedL2Core second ∈ highDiskL2)
    (samePDE : scalarResidualJet parameter first = scalarResidualJet parameter second)
    (sameRobin : ∀ angle : CellCircle,
      (eulerJet first).value (boundaryDiskPoint angle) + (2 : ℝ) • first.value (boundaryDiskPoint angle) =
        (eulerJet second).value (boundaryDiskPoint angle) + (2 : ℝ) • second.value (boundaryDiskPoint angle)) :
    first = second := by
  apply strongRobin_unique parameter first second firstHigh secondHigh
  · exact (strongResidualBulk_scalar parameter first).trans
      ((congrArg closedL2Core samePDE).trans (strongResidualBulk_scalar parameter second).symm)
  · intro angle
    simpa only [Complex.coe_smul] using! sameRobin angle

private theorem closedL2_same_interior (first second : ClosedJet 1)
    (same : ∀ point : ClosedDisk, ‖point.val‖ < 1 → first.value point = second.value point) :
    closedL2Core first = closedL2Core second := by
  apply Lp.ext
  filter_upwards [closedContinuousToDiskL2_ae first.value, closedContinuousToDiskL2_ae second.value,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point firstLaw secondLaw inside
  change closedContinuousToDiskL2 first.value point = closedContinuousToDiskL2 second.value point
  rw [firstLaw, secondLaw, closedDiskLift, dif_pos (openDiskMembershipClosed point inside),
    closedDiskLift, dif_pos (openDiskMembershipClosed point inside)]
  exact same ⟨point, openDiskMembershipClosed point inside⟩ inside

theorem scalarResidualJet_literal (parameter : ℝ) (field : ClosedJet 1) (point : ClosedDisk) :
    (scalarResidualJet parameter field).value point =
      -Grad.NonlinearQuotient.diskLaplacian (smoothClosedExtension field) point.val +
        ((parameter ^ 2 : ℝ) : ℂ) • (smoothDiskBJet field).value point := by
  simp only [scalarResidualJet, closedJet_value_add, closedJet_value_neg, closedJet_value_smul,
    ContinuousMap.add_apply, ContinuousMap.neg_apply, ContinuousMap.smul_apply]
  rw [laplacianJet_value, laplacianCoefficient_extension]

/-- Full smooth uniqueness only requires the scalar PDE on the OPEN disk;
Robin data use the genuine outward derivative at the complete unit boundary. -/
theorem pointwiseScalarRobin_unique (parameter : ℝ) (first second : ClosedJet 1)
    (firstHigh : closedL2Core first ∈ highDiskL2) (secondHigh : closedL2Core second ∈ highDiskL2)
    (samePDE : ∀ point : ClosedDisk, ‖point.val‖ < 1 →
      -Grad.NonlinearQuotient.diskLaplacian (smoothClosedExtension first) point.val +
        ((parameter ^ 2 : ℝ) : ℂ) • (smoothDiskBJet first).value point =
      -Grad.NonlinearQuotient.diskLaplacian (smoothClosedExtension second) point.val +
        ((parameter ^ 2 : ℝ) : ℂ) • (smoothDiskBJet second).value point)
    (sameRobin : ∀ angle : CellCircle,
      fderiv ℝ (smoothClosedExtension first) (boundaryCirclePoint angle) (boundaryCirclePoint angle) +
        (2 : ℝ) • first.value (boundaryDiskPoint angle) =
      fderiv ℝ (smoothClosedExtension second) (boundaryCirclePoint angle) (boundaryCirclePoint angle) +
        (2 : ℝ) • second.value (boundaryDiskPoint angle)) : first = second := by
  apply scalarRobin_unique parameter first second firstHigh secondHigh
  · apply closedL2Core_injective
    apply closedL2_same_interior
    intro point inside
    exact (scalarResidualJet_literal parameter first point).trans
      ((samePDE point inside).trans (scalarResidualJet_literal parameter second point).symm)
  · intro angle
    rw [eulerJet_extension_value, eulerJet_extension_value]
    exact sameRobin angle

/-- Exact uniqueness consumer for the accepted constructed homogeneous inverse. -/
theorem actualSmoothInverse_unique (parameters : PhaseParameters) (parameter : ℝ)
    (source : highDiskL2) (core : ClosedJet 1) (sourceSame : source.val = closedL2Core core)
    (solution : ClosedJet 1) (high : closedL2Core solution ∈ highDiskL2)
    (pde : scalarResidualJet parameter solution = core)
    (robin : ∀ angle : CellCircle,
      (eulerJet solution).value (boundaryDiskPoint angle) + (2 : ℝ) • solution.value (boundaryDiskPoint angle) = 0) :
    solution = actualSmoothInverse parameters parameter core := by
  have equation : strongResidualBulk parameter solution = source.val :=
    (strongResidualBulk_scalar parameter solution).trans ((congrArg closedL2Core pde).trans sourceSame.symm)
  have same := strongRobin_is_weakInverse parameter source solution high equation (by
    intro angle
    simpa only [Complex.coe_smul] using! robin angle)
  apply diskCoreInto_injective
  exact same.trans (actualSmoothInverse_H1_of_high parameters parameter source core sourceSame).symm

end Grad.SmoothRobinUniqueness

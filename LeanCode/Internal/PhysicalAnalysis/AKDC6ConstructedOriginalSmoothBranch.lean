import AKDC5ActualFiniteIterateContinuity
import AKCZ17OriginalPhysicalBranchSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 3500
open Set
open scoped ContDiff

namespace Grad.NashMoser.OriginalIteration
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.SmoothingFamily Grad.Q24Realization Grad.NashMoser.OriginalLimit Grad.SmoothForward
open Grad.NonlinearQuotientBounds Grad.PhysicalCoordinates Grad.NashMoser.InverseCalculus
open Grad.OriginalParameterEvaluation Grad.ClosedJets

variable {parameters : PhaseParameters} {reference : Seed.Parameters}
    {inside : reference ∈ Seed.parameterDomain} {base loss : ℕ} {cellLength : ℝ}
    {neighborhood : OriginalNewtonNeighborhood parameters reference inside base}
    {inverse : OriginalNewtonInverse neighborhood cellLength loss}

namespace OriginalNewtonScale
variable (scale : OriginalNewtonScale inverse)

theorem parameterLimit_admissible (point : OriginalFiniteParameter) (member : point ∈ scale.openParameterDomain) :
    point.1 ∈ Seed.parameterDomain ∧ ChartAxisCondition (smoothingChartCore parameters (scale.parameterLimit point).val) :=
  ⟨neighborhood.patchInside (neighborhood.seedInside point (scale.openParameterDomain_subset member).1),
    neighborhood.axis _ (scale.parameterLimit_low point member)⟩

theorem parameterLimit_right (point : OriginalFiniteParameter) (member : point ∈ scale.openParameterDomain)
    (source : sourceSmoothRange parameters) :
    literalPhysicalSmoothForward parameters cellLength reference inside point.1 (scale.parameterLimit_admissible point member).1
      (point.2,scale.parameterLimit point) (scale.parameterLimit_admissible point member).2
      (inverse.map point (scale.parameterLimit point) source) = source :=
  inverse.right point (scale.openParameterDomain_subset member).1 (scale.parameterLimit point)
    (scale.parameterLimit_low point member) source

theorem parameterLimit_left (leftLaw : inverse.LeftLaw) (point : OriginalFiniteParameter)
    (member : point ∈ scale.openParameterDomain) (state : stateSmoothRange parameters reference inside) :
    inverse.map point (scale.parameterLimit point)
      (literalPhysicalSmoothForward parameters cellLength reference inside point.1 (scale.parameterLimit_admissible point member).1
        (point.2,scale.parameterLimit point) (scale.parameterLimit_admissible point member).2 state) = state :=
  leftLaw.left point (scale.openParameterDomain_subset member).1 (scale.parameterLimit point)
    (scale.parameterLimit_low point member) state

/-- The SAME original Newton limit is smooth in all completed grades on one
fixed open patch. Finite-stage continuity, exact zeros and the inverse
parameter calculus are all proved; the remaining input is actual PC. -/
theorem parameterLimit_contDiffOn (leftLaw : inverse.LeftLaw) :
    ∀ grade, ContDiffOn ℝ ∞ (fun point => stateSmoothEmbedding parameters reference inside (grade+4)
      (branchGrade_large grade) (scale.parameterLimit point)) scale.openParameterDomain :=
  originalZeroBranch_contDiffOn parameters reference inside scale.parameterLimit scale.openParameterDomain inverse.parameterLoss
    (fun point => inverse.map point (scale.parameterLimit point)) inverse.constant inverse.nonnegative
    (inverse.branch_tame scale.openParameterDomain (fun _point member => (scale.openParameterDomain_subset member).1)
      scale.parameterLimit scale.parameterLimit_low)
    cellLength scale.parameterLimit_admissible scale.parameterLimit_right (scale.parameterLimit_left leftLaw)
    scale.openParameterDomain_isOpen (scale.parameterLimit_continuousOn leftLaw) scale.parameterLimit_exact_zero

/-- Literal physical vector and potential of the SAME constructed original
branch, jointly smooth on the unchanged radius-4/3 collar. No branch,
inverse-smoothness, finite-iterate-continuity or Taylor premise is assumed. -/
theorem parameterLimit_physical_joint_smooth (leftLaw : inverse.LeftLaw) :
    ContDiffOn ℝ ∞ (fun point : OriginalFiniteParameter × SpatialCell =>
      originalExtendedField parameters (originalPhysicalChartBranch parameters reference inside
        (fun parameter => (parameter.1,realJointCoreToJoint parameters reference inside
          (parameter.2,scale.parameterLimit parameter))) point.1).2.1 point.2)
      (scale.openParameterDomain ×ˢ originalOpenCollar) ∧
    ContDiffOn ℝ ∞ (fun point : OriginalFiniteParameter × SpatialCell =>
      originalExtendedField parameters (originalPhysicalChartBranch parameters reference inside
        (fun parameter => (parameter.1,realJointCoreToJoint parameters reference inside
          (parameter.2,scale.parameterLimit parameter))) point.1).2.2 point.2)
      (scale.openParameterDomain ×ˢ originalOpenCollar) :=
  originalZeroBranch_physical_joint_smooth parameters reference inside scale.parameterLimit scale.openParameterDomain inverse.parameterLoss
    (fun point => inverse.map point (scale.parameterLimit point)) inverse.constant inverse.nonnegative
    (inverse.branch_tame scale.openParameterDomain (fun _point member => (scale.openParameterDomain_subset member).1)
      scale.parameterLimit scale.parameterLimit_low)
    cellLength scale.parameterLimit_admissible scale.parameterLimit_right (scale.parameterLimit_left leftLaw)
    scale.openParameterDomain_isOpen (scale.parameterLimit_continuousOn leftLaw) scale.parameterLimit_exact_zero

theorem parameterLimit_zero_branch (point : OriginalFiniteParameter) (member : point ∈ scale.openParameterDomain)
    (zero : originalNonlinearSource parameters cellLength reference inside point 0 = 0) :
    scale.parameterLimit point = 0 := by
  rw [scale.parameterLimit_same point (scale.openParameterDomain_subset member)]
  exact scale.originalLimit_zero_branch ⟨point,scale.openParameterDomain_subset member⟩ zero

end OriginalNewtonScale
end Grad.NashMoser.OriginalIteration

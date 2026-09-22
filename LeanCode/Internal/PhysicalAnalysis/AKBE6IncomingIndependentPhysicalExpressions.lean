import AKBE5SameObservedPacketTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
open scoped ContDiff
namespace Grad.ActualCartesianWeakEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.ActualCartesianEquations Grad.AnnularReconstruction
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.AnnularHighGenerators Grad.AnnularSourceGraph

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (first second : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (field : CoupledSpace lower length positive lengthPositive)
    (curves : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le first field))
    (same : fullStrongSevenInput parameters length lower lengthPositive positive bounded.le first field =
      fullStrongSevenInput parameters length lower lengthPositive positive bounded.le second field)

/-- Changing incoming-data labels while retaining all physical source rows
leaves the actual Cartesian force expression unchanged on the SAME field. -/
theorem sameCartesianRawForce_reindexDatum (radius : ℝ) (inside : radius ∈ Icc lower 1) (polar axial : ℝ) :
    sameCartesianRawForce parameters length compact lower positive bounded lengthPositive state second field
      (reindexPhysicalRow curves same) radius inside polar axial =
      sameCartesianRawForce parameters length compact lower positive bounded lengthPositive state first field
        curves radius inside polar axial := by
  unfold sameCartesianRawForce
  dsimp only
  rw [reindexPhysicalRow_covariantCartesian,reindexPhysicalRow_covariantField,reindexPhysicalRow_originalPhysical]

/-- The same incoming-data transport preserves the literal toroidal equation,
including its full original matrix correction inside polar mean removal. -/
theorem sameCartesianThirdExpression_reindexDatum (radius : ℝ) (inside : radius ∈ Icc lower 1) (polar axial : ℝ) :
    sameCartesianThirdExpression parameters length compact lower positive bounded lengthPositive state second field
      (reindexPhysicalRow curves same) radius inside polar axial =
      sameCartesianThirdExpression parameters length compact lower positive bounded lengthPositive state first field
        curves radius inside polar axial := by
  unfold sameCartesianThirdExpression
  dsimp only
  rw [reindexPhysicalRow_covariantCartesian,reindexPhysicalRow_originalPhysical]

end Grad.ActualCartesianWeakEquations

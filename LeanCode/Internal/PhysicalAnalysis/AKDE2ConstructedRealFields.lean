import AKDE1OriginalRealPhysicalFields
import AXP2PhysicalRaw

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 3500
open Set
open scoped ContDiff

namespace Grad.OriginalCellFamily
open Grad.CartesianState Grad.ClosedJets Grad.Constraints Grad.RealFixedRanges Grad.Q24Realization
open Grad.NonlinearQuotientBounds Grad.PhysicalCoordinates Grad.OriginalParameterEvaluation
open Grad.NashMoser.OriginalIteration Grad.NashMoser.OriginalLimit Grad.NonlinearRange Grad.RawForward
open Grad.OriginalCoreRealization Grad.CompletedReality

variable {parameters : PhaseParameters} {reference : Seed.Parameters}
    {inside : reference ∈ Seed.parameterDomain} {base loss : ℕ} {cellLength : ℝ}
    {neighborhood : OriginalNewtonNeighborhood parameters reference inside base}
    {inverse : OriginalNewtonInverse neighborhood cellLength loss}

/-- The literal corrected chart of the SAME constructed original Newton limit. -/
def constructedPhysicalChart (scale : OriginalNewtonScale inverse) (point : OriginalFiniteParameter) :
    QuotientState parameters :=
  originalPhysicalChartBranch parameters reference inside
    (fun parameter => (parameter.1,realJointCoreToJoint parameters reference inside
      (parameter.2,scale.parameterLimit parameter))) point

theorem constructedPhysicalChart_same (scale : OriginalNewtonScale inverse)
    (point : OriginalFiniteParameter) (member : point ∈ scale.openParameterDomain) :
    constructedPhysicalChart scale point =
      physicalReferenceState parameters reference inside point.1 (scale.parameterLimit_admissible point member).1
        (realJointCoreToJoint parameters reference inside (point.2,scale.parameterLimit point)) :=
  originalPhysicalChartBranch_same parameters reference inside _ point
    (scale.parameterLimit_admissible point member).1

def constructedRealVector (scale : OriginalNewtonScale inverse) (point : OriginalFiniteParameter) :
    SpatialCell → EuclideanSpace ℝ (Fin 3) :=
  originalRealExtendedField parameters (constructedPhysicalChart scale point).2.1

def constructedRealPotential (scale : OriginalNewtonScale inverse) (point : OriginalFiniteParameter) :
    SpatialCell → EuclideanSpace ℝ (Fin 1) :=
  originalRealExtendedField parameters (constructedPhysicalChart scale point).2.2

theorem constructedRealFields_joint_smooth (scale : OriginalNewtonScale inverse) (leftLaw : inverse.LeftLaw) :
    ContDiffOn ℝ ∞ (fun point : OriginalFiniteParameter × SpatialCell =>
      constructedRealVector scale point.1 point.2) (scale.openParameterDomain ×ˢ originalOpenCollar) ∧
    ContDiffOn ℝ ∞ (fun point : OriginalFiniteParameter × SpatialCell =>
      constructedRealPotential scale point.1 point.2) (scale.openParameterDomain ×ˢ originalOpenCollar) := by
  have smooth := scale.parameterLimit_physical_joint_smooth leftLaw
  exact ⟨(physicalRealPart 3).contDiff.comp_contDiffOn smooth.1,
    (physicalRealPart 1).contDiff.comp_contDiffOn smooth.2⟩

theorem constructedPhysicalChart_real (scale : OriginalNewtonScale inverse)
    (point : OriginalFiniteParameter) (member : point ∈ scale.openParameterDomain) :
    cartesianCoreConjugation parameters (constructedPhysicalChart scale point).2.1 =
        (constructedPhysicalChart scale point).2.1 ∧
    cartesianCoreConjugation parameters (constructedPhysicalChart scale point).2.2 =
        (constructedPhysicalChart scale point).2.2 := by
  rw [constructedPhysicalChart_same scale point member]
  refine ⟨actualPhysicalReference_currentReal parameters reference inside point.1
    (scale.parameterLimit_admissible point member).1 (point.2,scale.parameterLimit point)
    (scale.parameterLimit_admissible point member).2, ?_⟩
  change cartesianCoreConjugation parameters
    (tameSeedScalar parameters point.1 (scale.parameterLimit_admissible point member).1 +
      (scale.parameterLimit point).val.2.2) = _
  rw [map_add, tameSeedScalar_real, (stateChart_real parameters reference inside (scale.parameterLimit point)).2.2]
  rfl

theorem constructedRealFields_original (scale : OriginalNewtonScale inverse)
    (point : OriginalFiniteParameter) (member : point ∈ scale.openParameterDomain)
    (disk : ClosedDisk) (cell : ℝ) :
    physicalComplexification 3 (constructedRealVector scale point (assembleSpatialCell disk.val cell)) =
        (originalPhysicalClosedJet parameters (constructedPhysicalChart scale point).2.1).value (disk,(cell : CellCircle)) ∧
    physicalComplexification 1 (constructedRealPotential scale point (assembleSpatialCell disk.val cell)) =
        (originalPhysicalClosedJet parameters (constructedPhysicalChart scale point).2.2).value (disk,(cell : CellCircle)) :=
  ⟨originalRealExtendedField_original parameters _ (constructedPhysicalChart_real scale point member).1 disk cell,
    originalRealExtendedField_original parameters _ (constructedPhysicalChart_real scale point member).2 disk cell⟩

theorem constructedRealFields_periodic (scale : OriginalNewtonScale inverse)
    (point : OriginalFiniteParameter) (disk : EuclideanSpace ℝ (Fin 2)) (cell : ℝ) :
    constructedRealVector scale point (assembleSpatialCell disk (cell+2*Real.pi)) =
        constructedRealVector scale point (assembleSpatialCell disk cell) ∧
    constructedRealPotential scale point (assembleSpatialCell disk (cell+2*Real.pi)) =
        constructedRealPotential scale point (assembleSpatialCell disk cell) :=
  ⟨originalRealExtendedField_periodic parameters _ disk cell,
    originalRealExtendedField_periodic parameters _ disk cell⟩

/-- Zero of the actual constructed quotient source gives the four literal
raw core equations on the whole original disk, by multiplication only. -/
theorem constructedPhysicalChart_raw_zero (scale : OriginalNewtonScale inverse)
    (point : OriginalFiniteParameter) (member : point ∈ scale.openParameterDomain) :
    originalRawRowsCore parameters cellLength (constructedPhysicalChart scale point) = 0 := by
  rw [constructedPhysicalChart_same scale point member]
  change rawPhysicalFixedSliceCore parameters cellLength reference inside point.1
    (scale.parameterLimit_admissible point member).1 (point.2,scale.parameterLimit point) = 0
  rw [← rawPhysicalFixedSliceCore_identity]
  have zero := congrArg Subtype.val (scale.parameterLimit_exact_zero point member)
  rw [originalNonlinearSource_value parameters cellLength reference inside point (scale.parameterLimit point)
    (scale.parameterLimit_admissible point member).1 (scale.parameterLimit_admissible point member).2] at zero
  change physicalFixedSliceMap parameters cellLength reference inside point.1
    (scale.parameterLimit_admissible point member).1
      (realJointCoreToJoint parameters reference inside (point.2,scale.parameterLimit point)) = 0 at zero
  rw [zero, map_zero]

end Grad.OriginalCellFamily

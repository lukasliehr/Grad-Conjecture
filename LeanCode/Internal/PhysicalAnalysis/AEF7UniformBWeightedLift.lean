import AEF6CompletedUniformInnerLift
import AED9ActualPhysicalWeakRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.AnnularUniformBoundary

open Grad.AnnularVariational Grad.AnnularGrades
open Grad.AnnularTiltedReference

/-- The uniformly bounded incoming lift in the literal stored `b_m⁻¹`
coordinates.  Decoding it gives exactly the physical AAG lift. -/
def uniformBInnerLift (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length) :
    AnnularBoundary →L[ℂ] annularEnergySpace lower length positive :=
  (bEnergyNormalize lower length positive).comp
    (uniformInnerLift lower length positive lowerHalf lengthPositive)

@[simp] theorem uniformBInnerLift_decoded (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (boundary : AnnularBoundary) :
    bEnergyDecode lower length positive
      (uniformBInnerLift lower length positive lowerHalf lengthPositive boundary) =
    uniformInnerLift lower length positive lowerHalf lengthPositive boundary := by
  rw [uniformBInnerLift, ContinuousLinearMap.comp_apply, bEnergyDecode_normalize]

theorem uniformBInnerLift_bound (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (boundary : AnnularBoundary) :
    ‖uniformBInnerLift lower length positive lowerHalf lengthPositive boundary‖ ≤
      2 * uniformInnerLiftConstant length * ‖boundary‖ := by
  have diagonal := annularEnergyDiagonal_bound lower length positive bEnergyWeight
    2 (by norm_num) bEnergyWeight_bound
    (uniformInnerLift lower length positive lowerHalf lengthPositive boundary)
  have lift := uniformInnerLift_bound lower length positive lowerHalf lengthPositive boundary
  change ‖bEnergyNormalize lower length positive
    (uniformInnerLift lower length positive lowerHalf lengthPositive boundary)‖ ≤ _
  exact diagonal.trans (by nlinarith [lift, norm_nonneg boundary])

/-- Literal decoded incoming trace, with no residual `b_m` factor. -/
@[simp] theorem uniformBInnerLift_decoded_inner (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (boundary : AnnularBoundary) :
    annularEnergyTrace lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
      (bEnergyDecode lower length positive
        (uniformBInnerLift lower length positive lowerHalf lengthPositive boundary)) = boundary := by
  rw [uniformBInnerLift_decoded, uniformInnerLift_inner]

/-- The same decoded lift contributes no outer boundary datum. -/
@[simp] theorem uniformBInnerLift_decoded_outer (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (boundary : AnnularBoundary) :
    annularEnergyTrace lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 1
      (bEnergyDecode lower length positive
        (uniformBInnerLift lower length positive lowerHalf lengthPositive boundary)) = 0 := by
  rw [uniformBInnerLift_decoded, uniformInnerLift_outer]

end Grad.AnnularUniformBoundary

import AJF12RealSourceApplicationDerivatives
import AJE4OriginalBoundaryCharacters
import AEF6CompletedUniformInnerLift
import AIE3PhysicalIncomingNormalization
import AIZ1ActualEnergyTranslations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
open scoped ContDiff
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularGrades Grad.AnnularCurrentSolution Grad.AnnularUniformBoundary
open Grad.AnnularStrongOrbit Grad.AnnularCoupledOrbit Grad.AnnularKernelOrbit

/-- The true prescribed incoming normalization is a fixed Fourier scalar,
so it commutes with the original boundary character exactly. -/
theorem physicalIncomingNormalize_translation (tau : OrbitParameter) (datum : AnnularBoundary) :
    physicalIncomingNormalize (highIncomingTranslation tau datum) =
      highIncomingTranslation tau (physicalIncomingNormalize datum) := by
  apply lp.ext
  funext index
  rw [physicalIncomingNormalize, realLpDiagonal_apply, highIncomingTranslation_apply,
    highIncomingTranslation_apply, realLpDiagonal_apply]
  exact smul_comm _ _ _

/-- The actual uniformly bounded inner lift uses the same mode in every
stored energy coordinate, including its radial slope and outer trace. -/
theorem uniformInnerLift_translation (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length) (tau : OrbitParameter) (datum : AnnularBoundary) :
    uniformInnerLift lower length positive lowerHalf lengthPositive (highIncomingTranslation tau datum) =
      energyTranslation lower length positive tau (uniformInnerLift lower length positive lowerHalf lengthPositive datum) := by
  apply Subtype.ext
  apply lp.ext
  funext index
  rw [energyTranslation_apply]
  change uniformInnerLiftRaw lower length positive lowerHalf lengthPositive (highIncomingTranslation tau datum) index =
    orbitCharacter tau index.val • uniformInnerLiftRaw lower length positive lowerHalf lengthPositive datum index
  rw [uniformInnerLiftRaw_apply, uniformInnerLiftRaw_apply, highIncomingTranslation_apply, map_smul, map_smul]

def physicalIncomingLift (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length) :
    AnnularBoundary →L[ℂ] annularEnergySpace lower length positive :=
  (uniformInnerLift lower length positive lowerHalf lengthPositive).comp physicalIncomingNormalize

theorem physicalIncomingLift_translation (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length) (tau : OrbitParameter) (datum : AnnularBoundary) :
    physicalIncomingLift lower length positive lowerHalf lengthPositive (highIncomingTranslation tau datum) =
      energyTranslation lower length positive tau (physicalIncomingLift lower length positive lowerHalf lengthPositive datum) := by
  change uniformInnerLift lower length positive lowerHalf lengthPositive (physicalIncomingNormalize (highIncomingTranslation tau datum)) = _
  rw [physicalIncomingNormalize_translation, uniformInnerLift_translation]
  rfl

theorem physicalIncomingLift_bound (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length) (datum : AnnularBoundary) :
    ‖physicalIncomingLift lower length positive lowerHalf lengthPositive datum‖ ≤
      2 * uniformInnerLiftConstant length * ‖datum‖ := by
  exact (uniformInnerLift_bound lower length positive lowerHalf lengthPositive (physicalIncomingNormalize datum)).trans
    ((mul_le_mul_of_nonneg_left (physicalIncomingNormalize_bound datum) (show 0 ≤ uniformInnerLiftConstant length from Real.sqrt_nonneg _)).trans_eq (by unfold uniformInnerLiftConstant; ring))

end Grad.AnnularHighGenerators

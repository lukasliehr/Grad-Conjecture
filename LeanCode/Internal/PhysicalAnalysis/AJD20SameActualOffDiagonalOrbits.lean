import AJD19CompleteActualCrossDataOrbits
import AJB13SameLowInverseSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularCrossMaps Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularHighInverseOrbit Grad.AnnularCoupledInverse
open Grad.AnnularLowOrbit Grad.AnnularCurrentLow Grad.AnnularLowEnergy Grad.AnnularKernelL2
open Grad.AnnularPhysicalSolution Grad.GaugeCoefficients.Physical.Allocation

attribute [local instance] crossDataNormed crossDataSeminormed crossDataRealInner crossDataRealNormed crossDataRealModule
  crossHighNormed crossHighSeminormed crossHighComplexNormed crossHighComplexModule crossHighRealNormed crossHighRealModule
  crossResponseRealNormed crossResponseRealModule lowToHighOperatorRealNormed highToLowOperatorRealNormed

local instance highOffDiagonalRealNormed (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    NormedSpace ℝ (lowEnergyGraph lower L positive →L[ℂ] CrossHighSpace lower L positive lengthPositive) :=
  NormedSpace.restrictScalars ℝ ℂ (lowEnergyGraph lower L positive →L[ℂ] CrossHighSpace lower L positive lengthPositive)
local instance lowOffDiagonalRealNormed (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    NormedSpace ℝ (CrossHighSpace lower L positive lengthPositive →L[ℂ] lowEnergyGraph lower L positive) :=
  NormedSpace.restrictScalars ℝ ℂ (CrossHighSpace lower L positive lengthPositive →L[ℂ] lowEnergyGraph lower L positive)

variable (parameters : PhaseParameters) (L compact lower : ℝ) (lengthPositive : 0 < L)
  (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
  (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
  (state : RetainedInverseState parameters L compact)
  (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters L compact)

def actualHighOffDiagonalOrbit (tau : OrbitParameter) :
    lowEnergyGraph lower L positive →L[ℂ] CrossHighSpace lower L positive lengthPositive :=
  (actualHighCrossResponseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    (coupledPrimitive_highSmall parameters L compact state small) tau).comp
    (lowToHighCrossOrbit parameters L compact lower lengthPositive positive lowerHalf state tau)

theorem actualHighOffDiagonalOrbit_contDiff :
    ContDiff ℝ ∞ (actualHighOffDiagonalOrbit parameters L compact lower lengthPositive positive lowerHalf widthHalf widthLength state small) :=
  complexOperatorComposition_contDiff _ _
    (actualHighCrossResponseOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
      (coupledPrimitive_highSmall parameters L compact state small))
    (lowToHighCrossOrbit_contDiff parameters L compact lower lengthPositive positive lowerHalf state)

theorem actualHighOffDiagonalOrbit_apply (tau : OrbitParameter) (field : lowEnergyGraph lower L positive) :
    actualHighOffDiagonalOrbit parameters L compact lower lengthPositive positive lowerHalf widthHalf widthLength state small tau field =
      highTranslationEquivalence lower L positive lengthPositive tau
        (actualHighOffDiagonal parameters lower L compact lengthPositive positive lowerHalf widthHalf widthLength state
          (coupledPrimitive_highSmall parameters L compact state small) (lowTranslation lower L positive (-tau) field)) := by
  change highTranslationEquivalence lower L positive lengthPositive tau
    (actualHighCrossResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
      (coupledPrimitive_highSmall parameters L compact state small)
      (crossDataTranslation parameters lower (-tau)
        (lowToHighCrossOrbit parameters L compact lower lengthPositive positive lowerHalf state tau field))) = _
  rw [lowToHighCrossOrbit_apply]
  have inverse := crossDataTranslation_inverse parameters lower (-tau)
    (lowToHighCross parameters lower L compact lengthPositive positive lowerHalf state (lowTranslation lower L positive (-tau) field))
  simp only [neg_neg] at inverse
  rw [inverse]
  rfl

def actualLowOffDiagonalOrbit (tau : OrbitParameter) :
    CrossHighSpace lower L positive lengthPositive →L[ℂ] lowEnergyGraph lower L positive :=
  (actualLowInverseOrbit parameters L compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state tau).comp
    (highToLowCrossOrbit parameters L compact lower lengthPositive positive lowerHalf state tau)

include small in
theorem actualLowOffDiagonalOrbit_contDiff :
    ContDiff ℝ ∞ (actualLowOffDiagonalOrbit parameters L compact lower lengthPositive positive lowerHalf state) :=
  complexOperatorComposition_contDiff _ _
    (actualLowInverseOrbit_contDiff parameters L compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state
      (coupledPrimitive_lowSmall parameters L compact state small))
    (highToLowCrossOrbit_contDiff parameters L compact lower lengthPositive positive lowerHalf state)

theorem actualLowOffDiagonalOrbit_apply (tau : OrbitParameter) (field : CrossHighSpace lower L positive lengthPositive) :
    actualLowOffDiagonalOrbit parameters L compact lower lengthPositive positive lowerHalf state tau field =
      lowTranslation lower L positive tau
        (actualLowOffDiagonal parameters lower L compact lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state
          (highTranslationEquivalence lower L positive lengthPositive (-tau) field)) := by
  change actualLowInverseOrbit parameters L compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state tau
    (highToLowCrossOrbit parameters L compact lower lengthPositive positive lowerHalf state tau field) = _
  rw [actualLowInverseOrbit_apply, highToLowCrossOrbit_apply]
  have inverse := (lowDataTranslationEquivalence lower tau).symm_apply_apply
    (highToLowCross parameters lower L compact lengthPositive positive (lowerHalf.trans (by norm_num)) state
      (highTranslationEquivalence lower L positive lengthPositive (-tau) field))
  rw [lowDataTranslation_symm] at inverse
  rw [inverse]
  rfl

end Grad.AnnularCrossOrbit

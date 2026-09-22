import AJD7ActualCrossKnownFunctionalOrbit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularCrossMaps Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit
open Grad.ActualBoundaryPrimitives Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource
open Grad.AnnularReconstruction Grad.AnnularKernelL2 Grad.AnnularHighInverseOrbit
open Grad.AnnularCurrentBoundary Grad.AnnularCurrentInverse Grad.AnnularPhysicalSolution

section Restriction
variable {X W V P : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup V] [NormedSpace ℝ V]

def operatorTestRestriction (inclusion : V →L[ℝ] W) :
    (X →L[ℝ] W →L[ℝ] ℝ) →L[ℝ] (X →L[ℝ] V →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ X (W →L[ℝ] ℝ) (V →L[ℝ] ℝ))
    ((ContinuousLinearMap.compL ℝ V W ℝ).flip inclusion)

variable [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem operatorTestRestriction_contDiff (inclusion : V →L[ℝ] W) (family : P → X →L[ℝ] W →L[ℝ] ℝ)
    (smooth : ContDiff ℝ ∞ family) : ContDiff ℝ ∞ (fun point => operatorTestRestriction inclusion (family point)) := by
  have composed := (ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := X →L[ℝ] W →L[ℝ] ℝ) (F := X →L[ℝ] V →L[ℝ] ℝ)
    (operatorTestRestriction (X := X) (W := W) (V := V) inclusion)).comp smooth
  simpa only [Function.comp_def] using composed
end Restriction

attribute [local instance] Grad.AnnularCrossOrbit.crossDataNormed Grad.AnnularCrossOrbit.crossDataSeminormed
  Grad.AnnularCrossOrbit.crossDataRealInner Grad.AnnularCrossOrbit.crossDataRealNormed Grad.AnnularCrossOrbit.crossDataRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)

/-- Exact pullback of AIQ11's genuine known functional, including the original beta inverse. -/
theorem crossKnownFunctionalOrbit_pullback (tau : OrbitParameter) (datum : CrossHighData parameters lower)
    (test : annularEnergySpace lower L positive) :
    crossKnownFunctionalOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau datum test =
      (crossKnownValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
        (crossDataTranslation parameters lower (-tau) datum) (energyTranslation lower L positive (-tau) test)).re := by
  rw [crossKnownFunctionalOrbit_literal, crossKnownBulkOrbit_apply]
  unfold crossBoundaryValueOrbit
  rw [ContinuousLinearMap.comp_apply, actualBoundaryInverseOrbit_apply]
  rw [orbitLp_inner_move, orbitLp_inner_move]
  rw [← highEnergyTestPacket_translation lower L positive parameters lengthPositive widthHalf widthLength (-tau) test,
    ← actualOuterTrace_translation parameters lower L positive lowerHalf lengthPositive 0 0 (-tau) test]
  rfl

def crossKnownZeroFunctionalOrbit (tau : OrbitParameter) :
    CrossHighData parameters lower →L[ℝ]
      (annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ) :=
  operatorTestRestriction (annularZeroRealInclusion lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive)
    (crossKnownFunctionalOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau)

theorem crossKnownZeroFunctionalOrbit_contDiff :
    ContDiff ℝ ∞ (crossKnownZeroFunctionalOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state) :=
  operatorTestRestriction_contDiff _ _
    (crossKnownFunctionalOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state)

theorem crossKnownZeroFunctionalOrbit_apply (tau : OrbitParameter) (datum : CrossHighData parameters lower)
    (test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive) :
    crossKnownZeroFunctionalOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau datum test =
      (crossKnownValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
        (crossDataTranslation parameters lower (-tau) datum)
        (zeroTestTranslation lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (-tau) test).val).re :=
  crossKnownFunctionalOrbit_pullback parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau datum test.val

end Grad.AnnularCrossOrbit

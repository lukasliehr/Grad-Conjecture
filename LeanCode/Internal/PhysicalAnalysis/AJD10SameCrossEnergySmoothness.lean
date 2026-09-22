import AJD9SameActualHighCrossEnergyOrbit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularCrossMaps Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit
open Grad.ActualBoundaryPrimitives Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource
open Grad.AnnularReconstruction Grad.AnnularKernelL2 Grad.AnnularHighInverseOrbit
open Grad.AnnularCurrentBoundary Grad.AnnularCurrentInverse Grad.AnnularPhysicalSolution Grad.AnnularCurrentSolution

/-- Operator composition in the original complex operator norm is real smooth. -/
theorem complexOperatorComposition_contDiff {P X E F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (outer : P → E →L[ℂ] F) (inner : P → X →L[ℂ] E)
    (outerSmooth : ContDiff ℝ ∞ outer) (innerSmooth : ContDiff ℝ ∞ inner) :
    ContDiff ℝ ∞ (fun point => (outer point).comp (inner point)) :=
  ((ContinuousLinearMap.compL ℂ X E F).bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff.comp₂ outerSmooth innerSmooth

private theorem realOperatorComposition_contDiff {P X E F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (outer : P → E →L[ℝ] F) (inner : P → X →L[ℝ] E)
    (outerSmooth : ContDiff ℝ ∞ outer) (innerSmooth : ContDiff ℝ ∞ inner) :
    ContDiff ℝ ∞ (fun point => (outer point).comp (inner point)) :=
  (ContinuousLinearMap.compL ℝ X E F).isBoundedBilinearMap.contDiff.comp₂ outerSmooth innerSmooth

attribute [local instance] Grad.AnnularCrossOrbit.crossDataNormed Grad.AnnularCrossOrbit.crossDataSeminormed
  Grad.AnnularCrossOrbit.crossDataRealInner Grad.AnnularCrossOrbit.crossDataRealNormed Grad.AnnularCrossOrbit.crossDataRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)

/-- Genuine smoothness of the SAME high cross response, in its original complex operator norm. -/
theorem crossZeroEnergyOrbit_contDiff :
    ContDiff ℝ ∞ (crossZeroEnergyOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) := by
  apply complexOperator_contDiff_of_restrict ∞
  have same : (fun tau => (crossZeroEnergyOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau).restrictScalars ℝ) =
      (fun tau => (currentHighInverseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau).comp
        (crossKnownZeroFunctionalOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau)) :=
    funext (crossZeroEnergyOrbit_sameInverse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
  rw [same]
  exact realOperatorComposition_contDiff _ _
    (currentHighInverseOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (crossKnownZeroFunctionalOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state)

def crossEnergyOrbit (tau : OrbitParameter) :
    CrossHighData parameters lower →L[ℂ] annularEnergySpace lower L positive :=
  (annularZeroInclusion lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive).comp
    (crossZeroEnergyOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau)

theorem crossEnergyOrbit_contDiff :
    ContDiff ℝ ∞ (crossEnergyOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) :=
  complexOperatorComposition_contDiff _ _ contDiff_const
    (crossZeroEnergyOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)

theorem crossEnergyOrbit_apply (tau : OrbitParameter) (datum : CrossHighData parameters lower) :
    crossEnergyOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau datum =
      energyTranslation lower L positive tau
        (crossEnergyValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
          (crossDataTranslation parameters lower (-tau) datum)) := by
  change (zeroTestTranslation lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive tau
    (crossZeroEnergyResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      (crossDataTranslation parameters lower (-tau) datum))).val = _
  exact (zeroTestTranslation_value lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive tau
    (crossZeroEnergyResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      (crossDataTranslation parameters lower (-tau) datum))).trans
    (congrArg (energyTranslation lower L positive tau)
      (crossZeroEnergyResponse_val parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
        (crossDataTranslation parameters lower (-tau) datum)))

end Grad.AnnularCrossOrbit

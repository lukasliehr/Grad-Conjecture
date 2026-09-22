import AJF27SameSharedKnownHighResponse
import AJF28SameSharedKnownLowResponse
import AJC2SharedStrongCoupledInverse
import AJD22SameCoupledInverseFrechetCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
open scoped ContDiff
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularReconstruction Grad.CartesianState Grad.AnnularKernelOrbit
open Grad.AnnularStrongData Grad.AnnularStrongOrbit Grad.AnnularCoupledOrbit Grad.AnnularCoupledInverse
open Grad.AnnularLowEnergy Grad.AnnularLowOrbit Grad.AnnularCurrentLow Grad.AnnularKnownLow
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCurrentSource Grad.AnnularStrongSolution
open Grad.AnnularCrossMaps Grad.AnnularFullSource Grad.AnnularCrossOrbit

section Conjugation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem sameConjugatedInverse_apply (translation : E ≃ₗᵢ[ℂ] E) (inverse conjugate : E →L[ℂ] E)
    (actual : ∀ value, conjugate value = translation (inverse (translation.symm value)))
    (data original : E) (same : data = translation original) :
    conjugate data = translation (inverse original) := by
  rw [actual, same, translation.symm_apply_apply]
end Conjugation

attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  strongCarrierNormed strongCarrierSeminormed strongCarrierRealNormed strongCarrierRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace
  Grad.AnnularCrossOrbit.coupledNormed Grad.AnnularCrossOrbit.coupledSeminormed
  Grad.AnnularCrossOrbit.coupledComplexNormed Grad.AnnularCrossOrbit.coupledComplexModule
  Grad.AnnularCrossOrbit.coupledRealNormed Grad.AnnularCrossOrbit.coupledRealModule
  Grad.AnnularCrossOrbit.coupledOperatorRealNormed Grad.AnnularCrossOrbit.coupledOperatorRealModule

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
  (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
  (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)
  (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters L compact)

/-- Full known high and low responses use exactly one original strong source. -/
def sharedKnownDiagonalOrbit (tau : OrbitParameter) :
    StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 →L[ℝ]
      CoupledSpace lower L positive lengthPositive :=
  realHilbertOperatorPair
    (sharedKnownHighResponseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
      (coupledPrimitive_highSmall parameters L compact state small) tau)
    (sharedKnownLowResponseOrbit parameters L compact lower positive lowerHalf lengthPositive state tau)

theorem sharedKnownDiagonalOrbit_contDiff :
    ContDiff ℝ ∞ (sharedKnownDiagonalOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) :=
  realHilbertOperatorPair_contDiff _ _
    (sharedKnownHighResponseOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
      (coupledPrimitive_highSmall parameters L compact state small))
    (sharedKnownLowResponseOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive state small)

theorem sharedKnownDiagonalOrbit_apply (tau : OrbitParameter)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0) :
    sharedKnownDiagonalOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau data =
      coupledTranslationEquivalence lower L positive lengthPositive tau
        (knownDiagonalResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
          (ActualHighKnownCarrier.toGraphKnownData parameters lower positive (lowerHalf.trans (by norm_num)) 0 0
            (strongToHigh parameters lower positive (lowerHalf.trans (by norm_num)) 0 0
              (strongDataTranslation parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 (-tau) data)))
          (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0
            (strongDataTranslation parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 (-tau) data))) :=
  congrArg₂ (fun (high : CrossHighSpace lower L positive lengthPositive) (low : lowEnergyGraph lower L positive) => WithLp.toLp 2 (high, low))
    (sharedKnownHighResponseOrbit_apply parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
      (coupledPrimitive_highSmall parameters L compact state small) tau data)
    (sharedKnownLowResponseOrbit_apply parameters L compact lower positive lowerHalf lengthPositive state tau data)

/-- The SAME complete AJC source response, expressed as a bounded real
operator whose orbit uses the SAME AIZ coupled inverse. -/
def sharedStrongResponseOrbit (tau : OrbitParameter) :
    StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 →L[ℝ]
      CoupledSpace lower L positive lengthPositive :=
  ((coupledOrbitInverse parameters lower L compact lengthPositive positive lowerHalf widthHalf widthLength state small tau).restrictScalars ℝ).comp
    (sharedKnownDiagonalOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau)

theorem sharedStrongResponseOrbit_contDiff :
    ContDiff ℝ ∞ (sharedStrongResponseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) := by
  have inverse := (ContinuousLinearMap.restrictScalarsIsometry ℂ
    (CoupledSpace lower L positive lengthPositive) (CoupledSpace lower L positive lengthPositive) ℝ ℝ).toContinuousLinearMap.contDiff.comp
    (coupledOrbitInverse_contDiff parameters L compact lower lengthPositive positive lowerHalf widthHalf widthLength state small)
  exact realOperatorComposition_contDiff _ _ inverse
    (sharedKnownDiagonalOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)

/-- Exact operator/source conjugation of the SAME full original inverse.
All component membership and covariance are already proved above. -/
theorem sharedStrongResponseOrbit_apply (tau : OrbitParameter)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0) :
    sharedStrongResponseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau data =
      coupledTranslationEquivalence lower L positive lengthPositive tau
        (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
          (strongDataTranslation parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 (-tau) data)) :=
  sameConjugatedInverse_apply (coupledTranslationEquivalence lower L positive lengthPositive tau)
    (actualCoupledInverse parameters lower L compact lengthPositive positive lowerHalf widthHalf widthLength state small)
    (coupledOrbitInverse parameters lower L compact lengthPositive positive lowerHalf widthHalf widthLength state small tau)
    (coupledOrbitInverse_apply parameters lower L compact lengthPositive positive lowerHalf widthHalf widthLength state small tau)
    _ _ (sharedKnownDiagonalOrbit_apply parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau data)

end Grad.AnnularHighGenerators

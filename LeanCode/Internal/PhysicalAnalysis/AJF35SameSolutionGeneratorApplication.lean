import AJF29SameSharedCoupledResponseOrbit
import AJF12RealSourceApplicationDerivatives
import AJF9SameCoupledInsertedGraphGrade

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
open scoped ContDiff BigOperators
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularReconstruction Grad.CartesianState Grad.AnnularKernelOrbit
open Grad.AnnularStrongData Grad.AnnularStrongOrbit Grad.AnnularCoupledOrbit Grad.AnnularCoupledInverse
open Grad.AnnularLowEnergy Grad.AnnularLowOrbit Grad.AnnularCurrentLow Grad.AnnularKnownLow
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCurrentSource Grad.AnnularStrongSolution
open Grad.AnnularCrossMaps Grad.AnnularFullSource Grad.AnnularCrossOrbit

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

/-- Apply the conjugated response to the genuine translated source. The
opposite translations cancel on that SAME prescribed datum. -/
theorem sharedStrongResponseOrbit_on_translation (tau : OrbitParameter)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0) :
    sharedStrongResponseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau
      (strongDataTranslation parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 tau data) =
    coupledTranslationEquivalence lower L positive lengthPositive tau
      (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) := by
  have first := sharedStrongResponseOrbit_apply parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau
    (strongDataTranslation parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 tau data)
  have inverse : strongDataTranslation parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 (-tau)
      (strongDataTranslation parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 tau data) = data := by
    simpa only [neg_neg] using strongDataTranslation_inverse parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 (-tau) data
  exact first.trans (congrArg (fun source => coupledTranslationEquivalence lower L positive lengthPositive tau
    (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small source)) inverse)

/-- This is an application lemma: the data curve's smoothness is supplied
by the genuine finite source construction in the final consumer. -/
theorem sharedStrongResponse_axis_contDiff
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0) (axis : Bool)
    (dataSmooth : ContDiff ℝ ∞ (fun time : ℝ => strongDataTranslation parameters lower positive
      (lowerHalf.trans (by norm_num)) 0 0 (time • Grad.AnnularInverseCalculus.axisVector axis) data)) :
    ContDiff ℝ ∞ (fun time : ℝ => coupledTranslationEquivalence lower L positive lengthPositive
      (time • Grad.AnnularInverseCalculus.axisVector axis)
      (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)) := by
  have lineSmooth : ContDiff ℝ ∞ (fun time : ℝ => time • Grad.AnnularInverseCalculus.axisVector axis) :=
    contDiff_id.smul contDiff_const
  have operatorSmooth := (sharedStrongResponseOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small).comp
    lineSmooth
  have applied := operatorSmooth.clm_apply dataSmooth
  simpa only [Function.comp_def, sharedStrongResponseOrbit_on_translation] using applied

theorem sharedStrongResponse_axisGenerator_bound
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0) (axis : Bool)
    (dataSmooth : ContDiff ℝ ∞ (fun time : ℝ => strongDataTranslation parameters lower positive
      (lowerHalf.trans (by norm_num)) 0 0 (time • Grad.AnnularInverseCalculus.axisVector axis) data)) (order : ℕ) :
    ‖coupledAxisGenerator lower L positive lengthPositive
      (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) axis order‖ ≤
    ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) *
      ‖iteratedDeriv index (fun time : ℝ => sharedStrongResponseOrbit parameters L compact lower positive lowerHalf
        lengthPositive widthHalf widthLength state small (time • Grad.AnnularInverseCalculus.axisVector axis)) 0‖ *
      ‖iteratedDeriv (order - index) (fun time : ℝ => strongDataTranslation parameters lower positive
        (lowerHalf.trans (by norm_num)) 0 0 (time • Grad.AnnularInverseCalculus.axisVector axis) data) 0‖ := by
  have lineSmooth : ContDiff ℝ ∞ (fun time : ℝ => time • Grad.AnnularInverseCalculus.axisVector axis) :=
    contDiff_id.smul contDiff_const
  have operatorSmooth := (sharedStrongResponseOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small).comp
    lineSmooth
  have estimate := Grad.AnnularOrbitGenerators.iteratedDeriv_realOperatorApplication_bound
    (fun time : ℝ => sharedStrongResponseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      (time • Grad.AnnularInverseCalculus.axisVector axis))
    (fun time : ℝ => strongDataTranslation parameters lower positive (lowerHalf.trans (by norm_num)) 0 0
      (time • Grad.AnnularInverseCalculus.axisVector axis) data) operatorSmooth dataSmooth order 0
  simpa only [sharedStrongResponseOrbit_on_translation, coupledAxisGenerator] using estimate

end Grad.AnnularHighGenerators

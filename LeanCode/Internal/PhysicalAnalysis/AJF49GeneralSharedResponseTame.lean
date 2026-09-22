import AJF47FiniteSharedResponseTame
import AJF48SameSharedResponseContinuity
import AJF10SameCoupledWeightedClosure
import AJF36ActualApplicationTameConvolution
import AJF30AugmentedCoordinateBudget
import AJE54CompleteSourceOneHighBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
open Filter
open scoped ContDiff BigOperators Topology
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

/-- Arbitrary completed independent source data inherit the same graph
estimate by simultaneous finite cutoff and genuine weak-graph closure. -/
theorem generalSharedResponse_inserted_tame (parameters : PhaseParameters) (L compact : ℝ)
    (bound : UniformCoordinateBound (augmentedBudget CoupledCoordinateContext.budget)
      (sharedResponseCoordinateFamily parameters L compact)) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (context : CoupledCoordinateContext parameters L compact)
      (data weighted : StrongDataCarrier parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) 0 0)
      (_actual : StrongInsertedGrade parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) grade data weighted),
      ∃ solutionWeighted : CoupledSpace context.lower L context.positive context.lengthPositive,
        CoupledInsertedGrade context.lower L context.positive context.lengthPositive grade
          (sharedStrongResponse parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive context.widthHalf context.widthLength context.state context.small data) solutionWeighted ∧
        ‖solutionWeighted‖ ≤ constant * (‖weighted‖ + context.budget grade * ‖data‖) := by
  let constant := (finiteSharedResponse_inserted_tame parameters L compact bound grade).choose
  have nonnegative : 0 ≤ constant := (finiteSharedResponse_inserted_tame parameters L compact bound grade).choose_spec.1
  refine ⟨5 * constant, mul_nonneg (by norm_num) nonnegative, ?_⟩
  intro context data weighted actual
  let cut := strongDataCut parameters context.lower context.positive (context.lowerHalf.trans (by norm_num))
  let response := sharedStrongResponse parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive context.widthHalf context.widthLength context.state context.small
  have estimates (support : StrongCutSupport) :=
    (finiteSharedResponse_inserted_tame parameters L compact bound grade).choose_spec.2 context (cut support data) (cut support weighted) support
      (strongDataCut_supported parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) support data)
      (strongDataCut_inserted parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) support grade data weighted actual)
  let approximation : StrongCutSupport → CoupledSpace context.lower L context.positive context.lengthPositive := fun support => response (cut support data)
  let weightedApproximation : StrongCutSupport → CoupledSpace context.lower L context.positive context.lengthPositive := fun support => (estimates support).choose
  have approximationActual (support : StrongCutSupport) :
      CoupledInsertedGrade context.lower L context.positive context.lengthPositive grade (approximation support) (weightedApproximation support) :=
    (estimates support).choose_spec.1
  have approximationBound (support : StrongCutSupport) :
      ‖weightedApproximation support‖ ≤ constant * (‖weighted‖ + context.budget grade * ‖data‖) :=
    (estimates support).choose_spec.2.trans
      (mul_le_mul_of_nonneg_left (add_le_add
        (strongDataCut_bound parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) support weighted)
        (mul_le_mul_of_nonneg_left (strongDataCut_bound parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) support data) (context.budget_nonnegative grade))) nonnegative)
  have converges : Tendsto approximation strongCutFilter (𝓝 (response data)) :=
    ((sharedStrongResponse_continuous parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive context.widthHalf context.widthLength context.state context.small).tendsto data).comp
      (strongDataCut_tendsto parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) data)
  have : NeBot strongCutFilter := by unfold strongCutFilter; infer_instance
  obtain ⟨solutionWeighted, solutionActual, solutionBound⟩ := coupled_insertedGrade_of_bounded_approximation
    strongCutFilter context.lower L context.positive context.lengthPositive grade approximation weightedApproximation (response data) converges approximationActual
    (constant * (‖weighted‖ + context.budget grade * ‖data‖))
    (mul_nonneg nonnegative (add_nonneg (norm_nonneg weighted) (mul_nonneg (context.budget_nonnegative grade) (norm_nonneg data)))) approximationBound
  exact ⟨solutionWeighted, solutionActual, solutionBound.trans_eq (by ring)⟩

end Grad.AnnularHighGenerators

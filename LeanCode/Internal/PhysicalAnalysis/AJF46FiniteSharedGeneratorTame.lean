import AJF35SameSolutionGeneratorApplication
import AJF36ActualApplicationTameConvolution
import AJF30AugmentedCoordinateBudget
import AJE54CompleteSourceOneHighBound

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

def sharedResponseCoordinateFamily (parameters : PhaseParameters) (L compact : ℝ)
    (context : CoupledCoordinateContext parameters L compact) :
    OrbitParameter → StrongDataCarrier parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) 0 0 →L[ℝ]
      CoupledSpace context.lower L context.positive context.lengthPositive :=
  sharedStrongResponseOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive context.widthHalf context.widthLength context.state context.small

/-- The actual response calculus and the checked complete source allocation
combine before the finite-graph Fatou passage. The bound hypothesis is supplied
by the SAME coupled response composition in the final consumer. -/
theorem finiteSharedGenerator_tame (parameters : PhaseParameters) (L compact : ℝ)
    (bound : UniformCoordinateBound (augmentedBudget CoupledCoordinateContext.budget)
      (sharedResponseCoordinateFamily parameters L compact))
    (grade : ℕ) (gradePositive : 0 < grade) (axis : Bool) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (context : CoupledCoordinateContext parameters L compact)
      (data weighted : StrongDataCarrier parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) 0 0)
      (support : StrongCutSupport) (_finite : StrongSupported parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) support data)
      (_actual : StrongInsertedGrade parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) grade data weighted),
      ‖coupledAxisGenerator context.lower L context.positive context.lengthPositive
        (sharedStrongResponse parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive context.widthHalf context.widthLength context.state context.small data) axis grade‖ ≤
      constant * (‖weighted‖ + context.budget grade * ‖data‖) := by
  let coefficient := fun index : ℕ => (bound axis index).choose
  have coefficientNonnegative (index : ℕ) : 0 ≤ coefficient index := (bound axis index).choose_spec.1
  let sourceConstant := 11 * (1 + physicalInterpolationConstant 8 grade)
  have sourceNonnegative : 0 ≤ sourceConstant := by
    have positive := physicalInterpolationConstant_one_le 8 grade
    dsimp only [sourceConstant]
    positivity
  refine ⟨∑ index ∈ Finset.range (grade + 1), (grade.choose index : ℝ) * coefficient index * sourceConstant,
    tameConvolutionConstant_nonnegative grade coefficient (fun _ => sourceConstant) coefficientNonnegative (fun _ => sourceNonnegative), ?_⟩
  intro context data weighted support finite actual
  let operator := fun time : ℝ => sharedResponseCoordinateFamily parameters L compact context
    (time • Grad.AnnularInverseCalculus.axisVector axis)
  let source := fun time : ℝ => strongDataTranslation parameters context.lower context.positive
    (context.lowerHalf.trans (by norm_num)) 0 0 (time • Grad.AnnularInverseCalculus.axisVector axis) data
  have lineSmooth : ContDiff ℝ ∞ (fun time : ℝ => time • Grad.AnnularInverseCalculus.axisVector axis) := contDiff_id.smul contDiff_const
  have operatorSmooth : ContDiff ℝ ∞ operator :=
    (sharedStrongResponseOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive context.widthHalf context.widthLength context.state context.small).comp lineSmooth
  have sourceSmooth : ContDiff ℝ ∞ source :=
    finiteStrongDataOrbit_contDiff parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) data support finite axis
  have operatorBound (index : ℕ) (_below : index ≤ grade) :
      ‖iteratedDeriv index operator 0‖ ≤ coefficient index * coordinateJetWeight (augmentedBudget CoupledCoordinateContext.budget context) index := by
    simpa only [zero_add] using (bound axis index).choose_spec.2 context 0 0
  have mixed (index : ℕ) (below : index ≤ grade) :
      coordinateJetWeight (augmentedBudget CoupledCoordinateContext.budget context) index *
        ‖iteratedDeriv (grade - index) source 0‖ ≤ sourceConstant * (‖weighted‖ + context.budget grade * ‖data‖) := by
    have weight : coordinateJetWeight (augmentedBudget CoupledCoordinateContext.budget context) index ≤ 1 + context.budget index := by
      unfold coordinateJetWeight augmentedBudget
      split_ifs
      · linarith only [context.budget_nonnegative index]
      · rfl
    have sourceBound := strongAxisGenerator_augmented_oneHigh parameters context.lower context.positive
      (context.lowerHalf.trans (by norm_num)) context.state.val.val.field context.state.val.val.rho context.state.val.val.epsilon
      data weighted support finite axis grade index gradePositive below context.budget_zero_le_one actual
    exact (mul_le_mul_of_nonneg_right weight (norm_nonneg _)).trans sourceBound
  have estimate := realApplication_tameConvolution operator source operatorSmooth sourceSmooth grade 0
    (coordinateJetWeight (augmentedBudget CoupledCoordinateContext.budget context)) coefficient (fun _ => sourceConstant)
    coefficientNonnegative (‖weighted‖ + context.budget grade * ‖data‖) operatorBound mixed
  simpa only [operator, source, sharedResponseCoordinateFamily, sharedStrongResponseOrbit_on_translation, coupledAxisGenerator] using estimate

end Grad.AnnularHighGenerators

import AJF46FiniteSharedGeneratorTame
import AJF40FiniteSourceActualGraphGrade
import AJF44StrongInsertedGradeZero
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

/-- The grade-zero source generator has the norm of the SAME datum. -/
theorem strongAxisGenerator_zero_norm (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (data : StrongDataCarrier parameters lower positive bounded 0 0) (axis : Bool) :
    ‖strongAxisGenerator parameters lower positive bounded data axis 0‖ = ‖data‖ := by
  simp only [strongAxisGenerator, iteratedDeriv_zero, zero_smul]
  exact strongDataTranslation_norm parameters lower positive bounded 0 0 0 data

/-- Actual finite-source solutions satisfy the literal original graph tame
bound. Constants precede the inner radius, state, and independent data. -/
theorem finiteSharedResponse_inserted_tame (parameters : PhaseParameters) (L compact : ℝ)
    (bound : UniformCoordinateBound (augmentedBudget CoupledCoordinateContext.budget)
      (sharedResponseCoordinateFamily parameters L compact)) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (context : CoupledCoordinateContext parameters L compact)
      (data weighted : StrongDataCarrier parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) 0 0)
      (support : StrongCutSupport) (_finite : StrongSupported parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) support data)
      (_actual : StrongInsertedGrade parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) grade data weighted),
      ∃ solutionWeighted : CoupledSpace context.lower L context.positive context.lengthPositive,
        CoupledInsertedGrade context.lower L context.positive context.lengthPositive grade
          (sharedStrongResponse parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive context.widthHalf context.widthLength context.state context.small data) solutionWeighted ∧
        ‖solutionWeighted‖ ≤ constant * (‖weighted‖ + context.budget grade * ‖data‖) := by
  let baseConstant := 2 * independentCoupledDataConstant parameters L compact
  have baseNonnegative : 0 ≤ baseConstant := mul_nonneg (by norm_num) (independentCoupledDataConstant_nonnegative parameters L compact)
  by_cases zero : grade = 0
  · subst grade
    refine ⟨baseConstant, baseNonnegative, ?_⟩
    intro context data weighted support finite actual
    have same := strongInsertedGrade_zero_eq parameters context.lower context.positive (context.lowerHalf.trans (by norm_num)) data weighted actual
    subst weighted
    refine ⟨sharedStrongResponse parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive context.widthHalf context.widthLength context.state context.small data, ?_, ?_⟩
    · constructor
      · intro index
        simp only [pow_zero, Complex.ofReal_one, one_smul]
      · constructor <;> intro coordinate index <;> simp only [pow_zero, Complex.ofReal_one, one_smul]
    · exact (sharedStrongResponse_bound parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive context.widthHalf context.widthLength context.state context.small data).trans
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg (context.budget_nonnegative 0) (norm_nonneg data))) baseNonnegative)
  · have gradePositive : 0 < grade := Nat.pos_of_ne_zero zero
    let angular := (finiteSharedGenerator_tame parameters L compact bound grade gradePositive false).choose
    let cell := (finiteSharedGenerator_tame parameters L compact bound grade gradePositive true).choose
    have angularNonnegative : 0 ≤ angular := (finiteSharedGenerator_tame parameters L compact bound grade gradePositive false).choose_spec.1
    have cellNonnegative : 0 ≤ cell := (finiteSharedGenerator_tame parameters L compact bound grade gradePositive true).choose_spec.1
    let sourceConstant := 11 * (1 + physicalInterpolationConstant 8 grade)
    have sourceNonnegative : 0 ≤ sourceConstant := by
      have positive := physicalInterpolationConstant_one_le 8 grade
      dsimp only [sourceConstant]
      positivity
    refine ⟨coupledGeneratorGradeConstant grade * (baseConstant * sourceConstant + angular + cell),
      mul_nonneg (coupledGeneratorGradeConstant_nonnegative grade) (add_nonneg (add_nonneg (mul_nonneg baseNonnegative sourceNonnegative) angularNonnegative) cellNonnegative), ?_⟩
    intro context data weighted support finite actual
    let target := ‖weighted‖ + context.budget grade * ‖data‖
    have sourceEstimate := strongAxisGenerator_augmented_oneHigh parameters context.lower context.positive
      (context.lowerHalf.trans (by norm_num)) context.state.val.val.field context.state.val.val.rho context.state.val.val.epsilon
      data weighted support finite false grade grade gradePositive le_rfl context.budget_zero_le_one actual
    simp only [Nat.sub_self, strongAxisGenerator_zero_norm] at sourceEstimate
    change (1 + context.budget grade) * ‖data‖ ≤ sourceConstant * target at sourceEstimate
    have dataEstimate : ‖data‖ ≤ sourceConstant * target := by
      apply le_trans _ sourceEstimate
      have positive := context.budget_nonnegative grade
      nlinarith only [positive, norm_nonneg data]
    have baseEstimate := (sharedStrongResponse_bound parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive context.widthHalf context.widthLength context.state context.small data).trans
      (mul_le_mul_of_nonneg_left dataEstimate baseNonnegative)
    have angularEstimate := (finiteSharedGenerator_tame parameters L compact bound grade gradePositive false).choose_spec.2 context data weighted support finite actual
    have cellEstimate := (finiteSharedGenerator_tame parameters L compact bound grade gradePositive true).choose_spec.2 context data weighted support finite actual
    let solutionWeighted := (finiteSharedResponse_insertedGrade parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive context.widthHalf context.widthLength context.state context.small data support finite grade).choose
    have solutionActual := (finiteSharedResponse_insertedGrade parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive context.widthHalf context.widthLength context.state context.small data support finite grade).choose_spec.1
    have solutionBound := (finiteSharedResponse_insertedGrade parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive context.widthHalf context.widthLength context.state context.small data support finite grade).choose_spec.2
    refine ⟨solutionWeighted, solutionActual, solutionBound.trans ?_⟩
    calc
      _ ≤ coupledGeneratorGradeConstant grade * (baseConstant * (sourceConstant * target) + angular * target + cell * target) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add baseEstimate angularEstimate) cellEstimate) (coupledGeneratorGradeConstant_nonnegative grade)
      _ = _ := by ring

end Grad.AnnularHighGenerators

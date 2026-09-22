import AEL5ActualHighDualInverse
import AEF7UniformBWeightedLift

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.AnnularCurrentInverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularCurrentEnergy Grad.AnnularUniformBoundary

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  currentZero_normedGroup currentZero_seminormedGroup currentZero_realNormedSpace

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)

/-- Restriction in the test variable of the actual complete current form. -/
def currentHighTestFunctional (field : annularEnergySpace lower L positive) :
    annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ :=
  (currentHighForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field).comp
    (annularZeroRealInclusion lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive)

include small in
theorem currentHighTestFunctional_norm (field : annularEnergySpace lower L positive) :
    ‖currentHighTestFunctional parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field‖ ≤
      5 * ‖field‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro test
  change |currentHighForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field test.val| ≤ _
  rw [currentHighForm_literal]
  exact (Complex.abs_re_le_norm _).trans
    (currentHighFormValue_zeroTest_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small field test)

/-- The original uniform incoming lift is corrected by the actual dual inverse. -/
def currentHighLiftedSolution
    (source : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ)
    (innerValue : AnnularBoundary) : annularEnergySpace lower L positive :=
  uniformInnerLift lower L positive lowerHalf lengthPositive innerValue +
    (currentHighDualInverse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      (source - currentHighTestFunctional parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
        (uniformInnerLift lower L positive lowerHalf lengthPositive innerValue))).val

theorem currentHighLiftedSolution_inner
    (source : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ)
    (innerValue : AnnularBoundary) :
    annularEnergyTrace lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
      (currentHighLiftedSolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small source innerValue) = innerValue := by
  unfold currentHighLiftedSolution
  rw [map_add, uniformInnerLift_inner]
  have zero := (currentHighDualInverse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    (source - currentHighTestFunctional parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
      (uniformInnerLift lower L positive lowerHalf lengthPositive innerValue))).property
  change annularEnergyTrace lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0 _ = 0 at zero
  rw [zero, add_zero]

theorem currentHighLiftedSolution_real
    (source : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ)
    (innerValue : AnnularBoundary)
    (test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive) :
    currentHighForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
      (currentHighLiftedSolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small source innerValue) test.val = source test := by
  let lift := uniformInnerLift lower L positive lowerHalf lengthPositive innerValue
  let residual := source - currentHighTestFunctional parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state lift
  have law := currentHighDualInverse_solves parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small residual test
  change currentHighForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    (currentHighDualInverse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small residual).val test.val =
      source test - currentHighForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state lift test.val at law
  have solutionFormula : currentHighLiftedSolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small source innerValue =
      lift + (currentHighDualInverse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small residual).val := rfl
  have replaced := congrArg
    (fun field : annularEnergySpace lower L positive => currentHighForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field test.val)
    solutionFormula
  have expanded := congrArg
    (fun functional : annularEnergySpace lower L positive →L[ℝ] ℝ => functional test.val)
    ((currentHighForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state).map_add
      lift (currentHighDualInverse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small residual).val)
  change currentHighForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    (lift + (currentHighDualInverse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small residual).val) test.val =
      currentHighForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state lift test.val +
      currentHighForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
        (currentHighDualInverse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small residual).val test.val at expanded
  exact replaced.trans (expanded.trans (by rw [law]; ring))

theorem currentHighLiftedSolution_bound
    (source : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ)
    (innerValue : AnnularBoundary) :
    ‖currentHighLiftedSolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small source innerValue‖ ≤
      32 * ‖source‖ + 161 * uniformInnerLiftConstant L * ‖innerValue‖ := by
  let lift := uniformInnerLift lower L positive lowerHalf lengthPositive innerValue
  let residual := source - currentHighTestFunctional parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state lift
  have residualBound : ‖residual‖ ≤ ‖source‖ + 5 * ‖lift‖ :=
    (norm_sub_le _ _).trans (add_le_add le_rfl
      (currentHighTestFunctional_norm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small lift))
  have correction := currentHighDualInverse_apply_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small residual
  have liftBound := uniformInnerLift_bound lower L positive lowerHalf lengthPositive innerValue
  have triangle := norm_add_le lift
    (currentHighDualInverse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small residual).val
  change ‖currentHighLiftedSolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small source innerValue‖ ≤ _ at triangle
  change ‖lift‖ ≤ uniformInnerLiftConstant L * ‖innerValue‖ at liftBound
  change ‖(currentHighDualInverse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small residual).val‖ ≤ _ at correction
  nlinarith only [residualBound, correction, liftBound, triangle]

end Grad.AnnularCurrentInverse

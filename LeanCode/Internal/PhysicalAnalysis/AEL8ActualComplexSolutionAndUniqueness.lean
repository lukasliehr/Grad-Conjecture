import AEL6ActualLiftedHighSolution

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

/-- Every solution of the actual real variational equation with the same
original incoming trace agrees with the constructed solution. -/
theorem currentHighLiftedSolution_unique
    (source : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ)
    (innerValue : AnnularBoundary) (candidate : annularEnergySpace lower L positive)
    (innerLaw : annularEnergyTrace lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0 candidate = innerValue)
    (equation : ∀ test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive,
      currentHighForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state candidate test.val = source test) :
    candidate = currentHighLiftedSolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small source innerValue := by
  let solution := currentHighLiftedSolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small source innerValue
  let difference : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive :=
    ⟨candidate - solution, by
      change annularEnergyTrace lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0 (candidate - solution) = 0
      rw [map_sub, innerLaw, currentHighLiftedSolution_inner, sub_self]⟩
  have first := equation difference
  have second := currentHighLiftedSolution_real parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small source innerValue difference
  have zeroForm : currentHighZeroForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state difference difference = 0 := by
    change currentHighForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
      (candidate - solution) difference.val = 0
    have expanded := congrArg
      (fun functional : annularEnergySpace lower L positive →L[ℝ] ℝ => functional difference.val)
      ((currentHighForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state).map_sub candidate solution)
    have subtraction : currentHighForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
        (candidate - solution) difference.val =
      currentHighForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state candidate difference.val -
        currentHighForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state solution difference.val := expanded
    exact subtraction.trans (by rw [first, second, sub_self])
  have coercive := currentHighZeroForm_coercive_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small difference
  rw [zeroForm] at coercive
  have zeroNorm : ‖difference‖ = 0 := by nlinarith [norm_nonneg difference]
  have equality := congrArg Subtype.val (norm_eq_zero.mp zeroNorm)
  exact sub_eq_zero.mp equality

/-- The exact full complex equation follows by the genuine iz test. -/
theorem currentHighLiftedSolution_complex
    (source : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ)
    (complexSource : annularEnergySpace lower L positive → ℂ)
    (sourceLiteral : ∀ test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive,
      source test = (complexSource test.val).re)
    (sourceImaginary : ∀ test, complexSource (Complex.I • test) = starRingEnd ℂ Complex.I * complexSource test)
    (innerValue : AnnularBoundary)
    (test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive) :
    currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
      (currentHighLiftedSolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small source innerValue) test.val =
        complexSource test.val := by
  apply currentHighForm_real_implies_complex parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    _ complexSource sourceImaginary
  intro point
  exact (currentHighLiftedSolution_real parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small source innerValue point).trans
    (sourceLiteral point)

theorem currentHighLiftedSolution_complex_unique
    (source : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ)
    (complexSource : annularEnergySpace lower L positive → ℂ)
    (sourceLiteral : ∀ test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive,
      source test = (complexSource test.val).re)
    (innerValue : AnnularBoundary) (candidate : annularEnergySpace lower L positive)
    (innerLaw : annularEnergyTrace lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0 candidate = innerValue)
    (equation : ∀ test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive,
      currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state candidate test.val = complexSource test.val) :
    candidate = currentHighLiftedSolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small source innerValue := by
  apply currentHighLiftedSolution_unique parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small source innerValue candidate innerLaw
  intro test
  rw [currentHighForm_literal, equation, ← sourceLiteral]

end Grad.AnnularCurrentInverse

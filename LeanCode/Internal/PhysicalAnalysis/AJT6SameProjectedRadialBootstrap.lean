import AJT5OriginalMeanFreeSystem

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)

variable (nonzeroLaw : ∀ mode : ℤ × ℤ, mode.1 ≠ 0 → ∀ radius, radius ∈ Icc lower 1 →
    HasDerivWithinAt
      (fun point => hilbertPairCoefficient mode (originalSmoothResponsePairCurve parameters length compact lower
        positive lowerHalf lengthPositive widthHalf widthLength state small core 0 point))
      (hilbertPairCoefficient mode (originalSmoothResponseSystemRHS parameters length compact lower
        positive lowerHalf lengthPositive widthHalf widthLength state small core 0 radius)) (Icc lower 1) radius)
include nonzeroLaw

/-- The nonzero-mode PDE and the actual zero complement give the complete
base Hilbert coordinate derivative after the original sector projection. -/
theorem originalMeanFreeSystem_baseDerivative (mode : ℤ × ℤ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt
      (fun point => hilbertPairCoefficient mode (originalSmoothResponsePairCurve parameters length compact lower
        positive lowerHalf lengthPositive widthHalf widthLength state small core 0 point))
      (hilbertPairCoefficient mode (originalMeanFreeSystemRHS parameters length compact lower
        positive lowerHalf lengthPositive widthHalf widthLength state small core 0 radius)) (Icc lower 1) radius := by
  rcases mode with ⟨angular,cell⟩
  by_cases zero : angular = 0
  · subst angular
    have constant : (fun point => hilbertPairCoefficient (0,cell)
        (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf
          lengthPositive widthHalf widthLength state small core 0 point)) = (fun _ : ℝ => 0) :=
      funext (fun point => originalSmoothResponsePairCurve_coefficient_meanZero parameters length compact lower
        positive lowerHalf lengthPositive widthHalf widthLength state small core 0 point cell)
    rw [constant]
    unfold originalMeanFreeSystemRHS
    rw [physicalPairMeanFree_coefficient_zero]
    exact hasDerivWithinAt_const radius (Icc lower 1) 0
  · unfold originalMeanFreeSystemRHS
    rw [physicalPairMeanFree_coefficient_nonzero parameters (angular,cell) zero]
    exact nonzeroLaw (angular,cell) zero radius inside

/-- Every polynomial grade is a fixed scalar insertion into the SAME base
physical solution and its projected full RHS. -/
theorem originalMeanFreeSystem_allGradeDerivative (grade : ℕ) (mode : ℤ × ℤ)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt
      (fun point => hilbertPairCoefficient mode (originalSmoothResponsePairCurve parameters length compact lower
        positive lowerHalf lengthPositive widthHalf widthLength state small core grade point))
      (hilbertPairCoefficient mode (originalMeanFreeSystemRHS parameters length compact lower
        positive lowerHalf lengthPositive widthHalf widthLength state small core grade radius)) (Icc lower 1) radius := by
  apply coordinateDerivative_of_grade lower (lowerHalf.trans_lt (by norm_num))
    (((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ))
    (fun point => hilbertPairCoefficient mode (originalSmoothResponsePairCurve parameters length compact lower
      positive lowerHalf lengthPositive widthHalf widthLength state small core grade point))
    (fun point => hilbertPairCoefficient mode (originalSmoothResponsePairCurve parameters length compact lower
      positive lowerHalf lengthPositive widthHalf widthLength state small core 0 point))
    (fun point => hilbertPairCoefficient mode (originalMeanFreeSystemRHS parameters length compact lower
      positive lowerHalf lengthPositive widthHalf widthLength state small core grade point))
    (fun point => hilbertPairCoefficient mode (originalMeanFreeSystemRHS parameters length compact lower
      positive lowerHalf lengthPositive widthHalf widthLength state small core 0 point))
  · exact fun point _ => originalSmoothResponsePairCurve_coefficient_grade parameters length compact lower
      positive lowerHalf lengthPositive widthHalf widthLength state small core grade point mode
  · exact (hilbertPairCoefficient mode).continuous.comp_continuousOn
      (originalMeanFreeSystemRHS_continuousOn parameters length compact lower
        positive lowerHalf lengthPositive widthHalf widthLength state small core grade)
  · exact (hilbertPairCoefficient mode).continuous.comp_continuousOn
      (originalMeanFreeSystemRHS_continuousOn parameters length compact lower
        positive lowerHalf lengthPositive widthHalf widthLength state small core 0)
  · exact originalMeanFreeSystemRHS_coefficient_grade parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade mode
  · exact originalMeanFreeSystem_baseDerivative parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core nonzeroLaw mode
  · exact inside

/-- Original projected all-grade system, with the true nonzero Fourier PDE
as its only remaining input. The all-order induction uses the fixed loss two. -/
theorem originalSmoothResponsePairCurve_smooth_of_nonzeroPDE :
    ∀ grade, ContDiffOn ℝ ∞ (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade) (Icc lower 1) := by
  apply physicalPairScale_smooth_of_coordinates lower (lowerHalf.trans_lt (by norm_num))
    (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core)
    (originalMeanFreeSystemSource parameters length compact lower positive lowerHalf lengthPositive state core)
    (originalMeanFreeSystemOperator parameters length compact lower positive lowerHalf state)
  · exact fun grade => (originalSmoothResponsePairCurve_continuous parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade).continuousOn
  · exact originalMeanFreeSystemSource_smooth parameters length compact lower positive lowerHalf lengthPositive state core
  · exact originalMeanFreeSystemOperator_smooth parameters length compact lower positive lowerHalf state
  · intro grade mode radius inside
    have derivative := originalMeanFreeSystem_allGradeDerivative parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core nonzeroLaw grade mode radius inside
    rw [originalMeanFreeSystemRHS_operatorSource] at derivative
    exact derivative.fst
  · intro grade mode radius inside
    have derivative := originalMeanFreeSystem_allGradeDerivative parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core nonzeroLaw grade mode radius inside
    rw [originalMeanFreeSystemRHS_operatorSource] at derivative
    exact derivative.snd

end Grad.AnnularSmoothCore

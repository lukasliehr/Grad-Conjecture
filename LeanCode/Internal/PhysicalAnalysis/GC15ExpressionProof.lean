import GC15ProductBounds

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Allocation

open Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Frame

def referenceExpressionConstant (constants : AtomConstants) (grade : ℕ)
    {input output : ℕ} (expression : CoefficientExpression input output) : ℝ := by
  induction expression generalizing grade with
  | atom input output label => exact constants input output label grade
  | add _ _ firstConstant secondConstant => exact firstConstant grade + secondConstant grade
  | smul scalar _ constant => exact ‖scalar‖ * constant grade
  | comp _ _ outerConstant innerConstant =>
    exact productReferenceConstant outerConstant innerConstant grade

def deviationExpressionConstant (offset : ℕ) (lowBound : ℝ)
    (fixedConstants deviationConstants : AtomConstants) (grade : ℕ)
    {input output : ℕ} (expression : CoefficientExpression input output) : ℝ := by
  induction expression generalizing grade with
  | atom input output label => exact deviationConstants input output label grade
  | add _ _ firstConstant secondConstant => exact firstConstant grade + secondConstant grade
  | smul scalar _ constant => exact ‖scalar‖ * constant grade
  | comp outer inner outerConstant innerConstant =>
    exact productDeviationConstant offset lowBound
      (fun order => referenceExpressionConstant fixedConstants order outer)
      (fun order => referenceExpressionConstant fixedConstants order inner)
      outerConstant innerConstant grade

theorem referenceExpressionConstant_nonnegative (constants : AtomConstants)
    (nonnegative : ∀ input output label grade, 0 ≤ constants input output label grade)
    {input output : ℕ} (expression : CoefficientExpression input output) (grade : ℕ) :
    0 ≤ referenceExpressionConstant constants grade expression := by
  induction expression generalizing grade with
  | atom input output label => exact nonnegative input output label grade
  | add first second firstIH secondIH => exact add_nonneg (firstIH grade) (secondIH grade)
  | smul scalar expression ih => exact mul_nonneg (norm_nonneg _) (ih grade)
  | comp outer inner outerIH innerIH =>
    exact productReferenceConstant_nonnegative _ _ outerIH innerIH grade

theorem deviationExpressionConstant_nonnegative (offset : ℕ) (lowBound : ℝ) (lowNonnegative : 0 ≤ lowBound)
    (fixedConstants deviationConstants : AtomConstants)
    (fixedNonnegative : ∀ input output label grade, 0 ≤ fixedConstants input output label grade)
    (deviationNonnegative : ∀ input output label grade, 0 ≤ deviationConstants input output label grade)
    {input output : ℕ} (expression : CoefficientExpression input output) (grade : ℕ) :
    0 ≤ deviationExpressionConstant offset lowBound fixedConstants deviationConstants grade expression := by
  induction expression generalizing grade with
  | atom input output label => exact deviationNonnegative input output label grade
  | add first second firstIH secondIH => exact add_nonneg (firstIH grade) (secondIH grade)
  | smul scalar expression ih => exact mul_nonneg (norm_nonneg _) (ih grade)
  | comp outer inner outerIH innerIH =>
    exact productDeviationConstant_nonnegative offset lowBound lowNonnegative _ _ _ _
      (referenceExpressionConstant_nonnegative fixedConstants fixedNonnegative outer)
      (referenceExpressionConstant_nonnegative fixedConstants fixedNonnegative inner)
      outerIH innerIH grade

theorem finite_expression_estimates {L ell : ℝ}
    (parameters : PhaseParameters) (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (offset : ℕ) (lowBound : ℝ) (lowNonnegative : 0 ≤ lowBound)
    (field : ACore parameters 3) (rho epsilon : ℝ)
    (low : physicalBudget parameters field rho epsilon offset ≤ lowBound)
    (actual reference : CoefficientAssignment L parameters.sigma0 parameters.gamma ell)
    (actualCoherent : AssignmentCoherent actual) (referenceCoherent : AssignmentCoherent reference)
    (fixedConstants deviationConstants : AtomConstants)
    (fixedNonnegative : ∀ input output label grade, 0 ≤ fixedConstants input output label grade)
    (deviationNonnegative : ∀ input output label grade, 0 ≤ deviationConstants input output label grade)
    (bounds : AtomBounds parameters field rho epsilon offset actual reference fixedConstants deviationConstants)
    {input output : ℕ} (expression : CoefficientExpression input output) :
    (∀ grade, ‖evaluateExpression admissible reference grade expression‖ ≤
      referenceExpressionConstant fixedConstants grade expression) ∧
    (∀ grade, ‖evaluateExpression admissible actual grade expression -
        evaluateExpression admissible reference grade expression‖ ≤
      deviationExpressionConstant offset lowBound fixedConstants deviationConstants grade expression *
        physicalBudget parameters field rho epsilon (offset + grade)) := by
  induction expression with
  | atom input output label =>
    exact ⟨fun grade => (bounds input output label grade).1, fun grade => (bounds input output label grade).2⟩
  | add first second firstIH secondIH =>
    constructor
    · intro grade
      exact (norm_add_le _ _).trans (add_le_add (firstIH.1 grade) (secondIH.1 grade))
    · intro grade
      change ‖(evaluateExpression admissible actual grade first + evaluateExpression admissible actual grade second) -
          (evaluateExpression admissible reference grade first + evaluateExpression admissible reference grade second)‖ ≤ _
      rw [show (evaluateExpression admissible actual grade first + evaluateExpression admissible actual grade second) -
          (evaluateExpression admissible reference grade first + evaluateExpression admissible reference grade second) =
        (evaluateExpression admissible actual grade first - evaluateExpression admissible reference grade first) +
          (evaluateExpression admissible actual grade second - evaluateExpression admissible reference grade second) by abel]
      exact (norm_add_le _ _).trans ((add_le_add (firstIH.2 grade) (secondIH.2 grade)).trans_eq (by
        simp only [deviationExpressionConstant, add_mul]))
  | smul scalar expression ih =>
    constructor
    · intro grade
      exact (coefficientScalarNorm_le scalar _).trans
        (mul_le_mul_of_nonneg_left (ih.1 grade) (norm_nonneg scalar))
    · intro grade
      change ‖scalar • evaluateExpression admissible actual grade expression -
        scalar • evaluateExpression admissible reference grade expression‖ ≤ _
      rw [← smul_sub]
      exact ((coefficientScalarNorm_le scalar _).trans
        (mul_le_mul_of_nonneg_left (ih.2 grade) (norm_nonneg scalar))).trans_eq (by
          simp only [deviationExpressionConstant, mul_assoc])
  | comp outer inner outerIH innerIH =>
    constructor
    · intro grade
      exact composition_reference_bound admissible _ _
        (evaluateExpression_coherent admissible reference referenceCoherent outer)
        (evaluateExpression_coherent admissible reference referenceCoherent inner)
        (fun order => referenceExpressionConstant fixedConstants order outer)
        (fun order => referenceExpressionConstant fixedConstants order inner)
        (referenceExpressionConstant_nonnegative fixedConstants fixedNonnegative outer)
        outerIH.1 innerIH.1 grade
    · intro grade
      exact composition_deviation_bound parameters admissible offset lowBound lowNonnegative field rho epsilon low
        (fun order => evaluateExpression admissible actual order outer)
        (fun order => evaluateExpression admissible reference order outer)
        (fun order => evaluateExpression admissible actual order inner)
        (fun order => evaluateExpression admissible reference order inner)
        (evaluateExpression_coherent admissible actual actualCoherent outer)
        (evaluateExpression_coherent admissible reference referenceCoherent outer)
        (evaluateExpression_coherent admissible actual actualCoherent inner)
        (evaluateExpression_coherent admissible reference referenceCoherent inner)
        (fun order => referenceExpressionConstant fixedConstants order outer)
        (fun order => referenceExpressionConstant fixedConstants order inner)
        (fun order => deviationExpressionConstant offset lowBound fixedConstants deviationConstants order outer)
        (fun order => deviationExpressionConstant offset lowBound fixedConstants deviationConstants order inner)
        (referenceExpressionConstant_nonnegative fixedConstants fixedNonnegative outer)
        (referenceExpressionConstant_nonnegative fixedConstants fixedNonnegative inner)
        (deviationExpressionConstant_nonnegative offset lowBound lowNonnegative fixedConstants deviationConstants
          fixedNonnegative deviationNonnegative outer)
        (deviationExpressionConstant_nonnegative offset lowBound lowNonnegative fixedConstants deviationConstants
          fixedNonnegative deviationNonnegative inner)
        outerIH.1 innerIH.1 outerIH.2 innerIH.2 grade

theorem finiteCoefficientAllocationGoal : FiniteCoefficientAllocationGoal := by
  intro offset grade lowBound lowNonnegative input output expression fixedConstants deviationConstants
    fixedNonnegative deviationNonnegative
  refine ⟨deviationExpressionConstant offset lowBound fixedConstants deviationConstants grade expression,
    deviationExpressionConstant_nonnegative offset lowBound lowNonnegative fixedConstants deviationConstants
      fixedNonnegative deviationNonnegative expression grade, ?_⟩
  intro parameters L ell admissible field rho epsilon actual reference actualCoherent referenceCoherent low bounds
  exact (finite_expression_estimates parameters admissible offset lowBound lowNonnegative field rho epsilon low
    actual reference actualCoherent referenceCoherent fixedConstants deviationConstants fixedNonnegative deviationNonnegative
    bounds expression).2 grade

theorem blockGoal : BlockGoal :=
  ⟨physicalInterpolationGoal, allocatedCompositionGoal, finiteCoefficientAllocationGoal⟩

end Grad.GaugeCoefficients.Physical.Allocation

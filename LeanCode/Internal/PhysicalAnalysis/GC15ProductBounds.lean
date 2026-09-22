import GC15Coherence
import GC15BudgetAllocation

noncomputable section

set_option maxHeartbeats 1200000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Allocation

open Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

def productReferenceConstant (outer inner : ℕ → ℝ) (grade : ℕ) : ℝ :=
  allocatedProductConstant grade * ∑ order : Fin (grade + 1), outer order.val * inner (grade - order.val)

def productDeviationConstant (offset : ℕ) (lowBound : ℝ)
    (outerReference innerReference outerDeviation innerDeviation : ℕ → ℝ) (grade : ℕ) : ℝ :=
  allocatedProductConstant grade * ∑ order : Fin (grade + 1),
    (outerDeviation order.val * innerReference (grade - order.val) +
      outerReference order.val * innerDeviation (grade - order.val) +
      outerDeviation order.val * innerDeviation (grade - order.val) * pairBudgetConstant offset grade lowBound)

theorem productReferenceConstant_nonnegative (outer inner : ℕ → ℝ)
    (outerNonnegative : ∀ grade, 0 ≤ outer grade) (innerNonnegative : ∀ grade, 0 ≤ inner grade)
    (grade : ℕ) : 0 ≤ productReferenceConstant outer inner grade := by
  exact mul_nonneg (allocatedProductConstant_nonnegative _)
    (Finset.sum_nonneg (fun _ _ => mul_nonneg (outerNonnegative _) (innerNonnegative _)))

theorem productDeviationConstant_nonnegative (offset : ℕ) (lowBound : ℝ) (lowNonnegative : 0 ≤ lowBound)
    (outerReference innerReference outerDeviation innerDeviation : ℕ → ℝ)
    (outerReferenceNonnegative : ∀ grade, 0 ≤ outerReference grade)
    (innerReferenceNonnegative : ∀ grade, 0 ≤ innerReference grade)
    (outerDeviationNonnegative : ∀ grade, 0 ≤ outerDeviation grade)
    (innerDeviationNonnegative : ∀ grade, 0 ≤ innerDeviation grade) (grade : ℕ) :
    0 ≤ productDeviationConstant offset lowBound outerReference innerReference outerDeviation innerDeviation grade := by
  apply mul_nonneg (allocatedProductConstant_nonnegative _)
  apply Finset.sum_nonneg
  intro order _
  exact add_nonneg (add_nonneg
    (mul_nonneg (outerDeviationNonnegative _) (innerReferenceNonnegative _))
    (mul_nonneg (outerReferenceNonnegative _) (innerDeviationNonnegative _)))
    (mul_nonneg (mul_nonneg (outerDeviationNonnegative _) (innerDeviationNonnegative _))
      (pairBudgetConstant_nonnegative offset grade lowNonnegative))

theorem composition_reference_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input middle output : ℕ}
    (outer : CoefficientFamily L sigma gamma ell middle output)
    (inner : CoefficientFamily L sigma gamma ell input middle)
    (outerCoherent : FamilyCoherent outer) (innerCoherent : FamilyCoherent inner)
    (outerConstant innerConstant : ℕ → ℝ)
    (outerNonnegative : ∀ grade, 0 ≤ outerConstant grade)
    (outerBound : ∀ grade, ‖outer grade‖ ≤ outerConstant grade)
    (innerBound : ∀ grade, ‖inner grade‖ ≤ innerConstant grade) (grade : ℕ) :
    ‖coefficientComposition admissible grade (outer grade) (inner grade)‖ ≤
      productReferenceConstant outerConstant innerConstant grade := by
  apply (allocated_composition_norm admissible grade outer inner outerCoherent innerCoherent).trans
  apply mul_le_mul_of_nonneg_left _ (allocatedProductConstant_nonnegative _)
  apply Finset.sum_le_sum
  intro order _
  exact mul_le_mul (outerBound _) (innerBound _) (norm_nonneg _) (outerNonnegative _)

theorem mixed_size_bound (offset grade _first second : ℕ) (secondLe : second ≤ grade)
    (parameters : PhaseParameters) (field : ACore parameters 3) (rho epsilon : ℝ)
    (fixed deviation fixedConstant deviationConstant : ℝ)
    (_fixedNonnegative : 0 ≤ fixed) (deviationNonnegative : 0 ≤ deviation)
    (fixedConstantNonnegative : 0 ≤ fixedConstant) (deviationConstantNonnegative : 0 ≤ deviationConstant)
    (fixedBound : fixed ≤ fixedConstant)
    (deviationBound : deviation ≤ deviationConstant * physicalBudget parameters field rho epsilon (offset + second)) :
    fixed * deviation ≤ fixedConstant * deviationConstant * physicalBudget parameters field rho epsilon (offset + grade) := by
  have high := deviationBound.trans (mul_le_mul_of_nonneg_left
    (physicalBudget_monotone parameters field rho epsilon
      (show offset + second ≤ offset + grade by omega)) deviationConstantNonnegative)
  simpa only [mul_assoc] using
    mul_le_mul fixedBound high deviationNonnegative fixedConstantNonnegative

theorem paired_size_bound (offset grade first second : ℕ) (allocated : first + second ≤ grade)
    (parameters : PhaseParameters) (field : ACore parameters 3) (rho epsilon lowBound : ℝ)
    (lowNonnegative : 0 ≤ lowBound) (low : physicalBudget parameters field rho epsilon offset ≤ lowBound)
    (outer inner outerConstant innerConstant : ℝ)
    (_outerNonnegative : 0 ≤ outer) (innerNonnegative : 0 ≤ inner)
    (outerConstantNonnegative : 0 ≤ outerConstant) (innerConstantNonnegative : 0 ≤ innerConstant)
    (outerBound : outer ≤ outerConstant * physicalBudget parameters field rho epsilon (offset + first))
    (innerBound : inner ≤ innerConstant * physicalBudget parameters field rho epsilon (offset + second)) :
    outer * inner ≤ outerConstant * innerConstant * pairBudgetConstant offset grade lowBound *
      physicalBudget parameters field rho epsilon (offset + grade) := by
  calc
    _ ≤ (outerConstant * physicalBudget parameters field rho epsilon (offset + first)) *
        (innerConstant * physicalBudget parameters field rho epsilon (offset + second)) :=
      mul_le_mul outerBound innerBound innerNonnegative
        (mul_nonneg outerConstantNonnegative (physicalBudget_nonnegative _ _ _ _ _))
    _ = (outerConstant * innerConstant) *
        (physicalBudget parameters field rho epsilon (offset + first) *
          physicalBudget parameters field rho epsilon (offset + second)) := by ring
    _ ≤ _ := by
      rw [mul_assoc (outerConstant * innerConstant)]
      exact mul_le_mul_of_nonneg_left
        (physical_budget_pair offset grade first second allocated parameters field rho epsilon lowBound lowNonnegative low)
        (mul_nonneg outerConstantNonnegative innerConstantNonnegative)

theorem composition_deviation_bound {L ell : ℝ}
    (parameters : PhaseParameters) (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (offset : ℕ) (lowBound : ℝ) (lowNonnegative : 0 ≤ lowBound)
    (field : ACore parameters 3) (rho epsilon : ℝ)
    (low : physicalBudget parameters field rho epsilon offset ≤ lowBound)
    {input middle output : ℕ}
    (outer referenceOuter : CoefficientFamily L parameters.sigma0 parameters.gamma ell middle output)
    (inner referenceInner : CoefficientFamily L parameters.sigma0 parameters.gamma ell input middle)
    (outerCoherent : FamilyCoherent outer) (referenceOuterCoherent : FamilyCoherent referenceOuter)
    (innerCoherent : FamilyCoherent inner) (referenceInnerCoherent : FamilyCoherent referenceInner)
    (outerReference innerReference outerDeviation innerDeviation : ℕ → ℝ)
    (outerReferenceNonnegative : ∀ grade, 0 ≤ outerReference grade)
    (innerReferenceNonnegative : ∀ grade, 0 ≤ innerReference grade)
    (outerDeviationNonnegative : ∀ grade, 0 ≤ outerDeviation grade)
    (innerDeviationNonnegative : ∀ grade, 0 ≤ innerDeviation grade)
    (outerReferenceBound : ∀ grade, ‖referenceOuter grade‖ ≤ outerReference grade)
    (innerReferenceBound : ∀ grade, ‖referenceInner grade‖ ≤ innerReference grade)
    (outerDeviationBound : ∀ grade, ‖outer grade - referenceOuter grade‖ ≤
      outerDeviation grade * physicalBudget parameters field rho epsilon (offset + grade))
    (innerDeviationBound : ∀ grade, ‖inner grade - referenceInner grade‖ ≤
      innerDeviation grade * physicalBudget parameters field rho epsilon (offset + grade)) (grade : ℕ) :
    ‖coefficientComposition admissible grade (outer grade) (inner grade) -
        coefficientComposition admissible grade (referenceOuter grade) (referenceInner grade)‖ ≤
      productDeviationConstant offset lowBound outerReference innerReference outerDeviation innerDeviation grade *
        physicalBudget parameters field rho epsilon (offset + grade) := by
  let deltaOuter := fun order => outer order - referenceOuter order
  let deltaInner := fun order => inner order - referenceInner order
  have deltaOuterCoherent : FamilyCoherent deltaOuter := outerCoherent.sub referenceOuterCoherent
  have deltaInnerCoherent : FamilyCoherent deltaInner := innerCoherent.sub referenceInnerCoherent
  have first := allocated_composition_norm admissible grade deltaOuter referenceInner deltaOuterCoherent referenceInnerCoherent
  have second := allocated_composition_norm admissible grade referenceOuter deltaInner referenceOuterCoherent deltaInnerCoherent
  have third := allocated_composition_norm admissible grade deltaOuter deltaInner deltaOuterCoherent deltaInnerCoherent
  have firstSize (order : Fin (grade + 1)) :
      ‖deltaOuter order.val‖ * ‖referenceInner (grade - order.val)‖ ≤
      (outerDeviation order.val * innerReference (grade - order.val)) *
        physicalBudget parameters field rho epsilon (offset + grade) := by
    rw [mul_comm ‖deltaOuter order.val‖ ‖referenceInner (grade - order.val)‖,
      mul_comm (outerDeviation order.val) (innerReference (grade - order.val))]
    exact mixed_size_bound offset grade (grade - order.val) order.val
      (by omega) parameters field rho epsilon ‖referenceInner (grade - order.val)‖ ‖deltaOuter order.val‖
      (innerReference (grade - order.val)) (outerDeviation order.val) (norm_nonneg _) (norm_nonneg _)
      (innerReferenceNonnegative _) (outerDeviationNonnegative _) (innerReferenceBound _) (outerDeviationBound _)
  have secondSize (order : Fin (grade + 1)) :
      ‖referenceOuter order.val‖ * ‖deltaInner (grade - order.val)‖ ≤
      (outerReference order.val * innerDeviation (grade - order.val)) *
        physicalBudget parameters field rho epsilon (offset + grade) :=
    mixed_size_bound offset grade order.val (grade - order.val) (by omega) parameters field rho epsilon
      ‖referenceOuter order.val‖ ‖deltaInner (grade - order.val)‖
      (outerReference order.val) (innerDeviation (grade - order.val)) (norm_nonneg _) (norm_nonneg _)
      (outerReferenceNonnegative _) (innerDeviationNonnegative _) (outerReferenceBound _) (innerDeviationBound _)
  have thirdSize (order : Fin (grade + 1)) :
      ‖deltaOuter order.val‖ * ‖deltaInner (grade - order.val)‖ ≤
      (outerDeviation order.val * innerDeviation (grade - order.val) * pairBudgetConstant offset grade lowBound) *
        physicalBudget parameters field rho epsilon (offset + grade) :=
    paired_size_bound offset grade order.val (grade - order.val) (by omega) parameters field rho epsilon lowBound
      lowNonnegative low ‖deltaOuter order.val‖ ‖deltaInner (grade - order.val)‖
      (outerDeviation order.val) (innerDeviation (grade - order.val)) (norm_nonneg _) (norm_nonneg _)
      (outerDeviationNonnegative _) (innerDeviationNonnegative _) (outerDeviationBound _) (innerDeviationBound _)
  rw [composition_deviation_expansion]
  calc
    _ ≤ ‖coefficientComposition admissible grade (deltaOuter grade) (referenceInner grade)‖ +
        ‖coefficientComposition admissible grade (referenceOuter grade) (deltaInner grade)‖ +
        ‖coefficientComposition admissible grade (deltaOuter grade) (deltaInner grade)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ allocatedProductConstant grade * (∑ order : Fin (grade + 1),
        (‖deltaOuter order.val‖ * ‖referenceInner (grade - order.val)‖ +
        ‖referenceOuter order.val‖ * ‖deltaInner (grade - order.val)‖ +
        ‖deltaOuter order.val‖ * ‖deltaInner (grade - order.val)‖)) := by
      have sumBound := add_le_add (add_le_add first second) third
      simpa only [Finset.sum_add_distrib, mul_add] using sumBound
    _ ≤ allocatedProductConstant grade * (∑ order : Fin (grade + 1),
        (outerDeviation order.val * innerReference (grade - order.val) +
          outerReference order.val * innerDeviation (grade - order.val) +
          outerDeviation order.val * innerDeviation (grade - order.val) * pairBudgetConstant offset grade lowBound) *
            physicalBudget parameters field rho epsilon (offset + grade)) := by
      apply mul_le_mul_of_nonneg_left _ (allocatedProductConstant_nonnegative _)
      apply Finset.sum_le_sum
      intro order _
      simpa only [add_mul] using add_le_add (add_le_add (firstSize order) (secondSize order)) (thirdSize order)
    _ = _ := by rw [← Finset.sum_mul]; simp only [productDeviationConstant, mul_assoc]

end Grad.GaugeCoefficients.Physical.Allocation

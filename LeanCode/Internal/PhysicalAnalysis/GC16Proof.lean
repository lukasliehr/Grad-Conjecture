import GC16SlotForcing

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.InverseAllocation

open Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.Allocation

theorem inverse_slot_step {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (offset grade : ℕ) (field : ACore parameters 3) (rho epsilon lowBound theta : ℝ)
    (lowNonnegative : 0 ≤ lowBound) (thetaLt : theta < 1)
    (low : physicalBudget parameters field rho epsilon offset ≤ lowBound)
    {dimension : ℕ} (positive : 0 < dimension)
    (coefficient : CoefficientFamily L parameters.sigma0 parameters.gamma ell dimension dimension)
    (coherent : FamilyCoherent coefficient) (constants : ℕ → ℝ)
    (nonnegative : ∀ order, 0 ≤ constants order)
    (bounds : ∀ order, ‖coefficient order‖ ≤
      constants order * physicalBudget parameters field rho epsilon (offset + order))
    (normBound : ‖coefficient 0‖ ≤ theta)
    (slot : RegularitySlot grade) (inductionConstant : ℝ) (inductionNonnegative : 0 ≤ inductionConstant)
    (lowerBounds : ∀ other : RegularitySlot grade, slotOrder other < slotOrder slot →
      slotNorm (inverseFamily admissible coefficient grade -
        gradedIdentityCoefficient L parameters.sigma0 parameters.gamma ell grade dimension) other ≤
          inductionConstant * physicalBudget parameters field rho epsilon (offset + slotOrder other)) :
    slotNorm (inverseFamily admissible coefficient grade -
      gradedIdentityCoefficient L parameters.sigma0 parameters.gamma ell grade dimension) slot ≤
        ((forcingConstant constants grade + interactionConstant constants offset grade lowBound *
          inductionConstant) / (1 - theta)) *
            physicalBudget parameters field rho epsilon (offset + slotOrder slot) := by
  let identity := gradedIdentityCoefficient L parameters.sigma0 parameters.gamma ell grade dimension
  let deviation := inverseFamily admissible coefficient grade - identity
  let budget := physicalBudget parameters field rho epsilon (offset + slotOrder slot)
  have fixedPoint := inverse_deviation_fixedPoint admissible positive coefficient coherent theta normBound thetaLt
    (grade := grade)
  have triangle : slotNorm deviation slot ≤
      slotNorm (coefficientComposition admissible grade (coefficient grade) identity) slot +
        slotNorm (coefficientComposition admissible grade (coefficient grade) deviation) slot := by
    calc
      _ = slotNorm (coefficientComposition admissible grade (coefficient grade) identity +
          coefficientComposition admissible grade (coefficient grade) deviation) slot :=
        congrArg (fun value => slotNorm value slot) fixedPoint
      _ ≤ _ := slotNorm_add_le _ _ slot
  have productBound := Grad.GaugeCoefficients.Neumann.Regularity.slotComposition_norm_le admissible grade
    (coefficient grade) deviation slot
  rw [slotCompositionNormMajorant_eq_split, slot_product_zero_split,
    coherent_zero_slot_norm coefficient coherent] at productBound
  have zeroBound : ‖coefficient 0‖ * slotNorm deviation slot ≤ theta * slotNorm deviation slot :=
    mul_le_mul_of_nonneg_right normBound (slotNorm_nonnegative deviation slot)
  have positiveBound := positive_interaction_bound parameters offset grade field rho epsilon lowBound
    lowNonnegative low coefficient coherent constants nonnegative bounds deviation slot
    inductionConstant inductionNonnegative lowerBounds
  have forcingBound := identity_forcing_bound parameters admissible offset grade field rho epsilon
    coefficient coherent constants nonnegative bounds slot
  have combined : slotNorm deviation slot ≤ forcingConstant constants grade * budget +
      (theta * slotNorm deviation slot +
        interactionConstant constants offset grade lowBound * inductionConstant * budget) :=
    triangle.trans (add_le_add forcingBound (productBound.trans (add_le_add zeroBound positiveBound)))
  have absorbed : slotNorm deviation slot ≤
      ((forcingConstant constants grade + interactionConstant constants offset grade lowBound *
        inductionConstant) * budget) / (1 - theta) := by
    apply (le_div_iff₀ (by linarith : 0 < 1 - theta)).2
    nlinarith [combined]
  exact absorbed.trans_eq (by ring)

theorem inverse_slot_one_high {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (offset grade : ℕ) (field : ACore parameters 3) (rho epsilon lowBound theta : ℝ)
    (lowNonnegative : 0 ≤ lowBound) (thetaLt : theta < 1)
    (low : physicalBudget parameters field rho epsilon offset ≤ lowBound)
    {dimension : ℕ} (positive : 0 < dimension)
    (coefficient : CoefficientFamily L parameters.sigma0 parameters.gamma ell dimension dimension)
    (coherent : FamilyCoherent coefficient) (constants : ℕ → ℝ)
    (nonnegative : ∀ order, 0 ≤ constants order)
    (bounds : ∀ order, ‖coefficient order‖ ≤
      constants order * physicalBudget parameters field rho epsilon (offset + order))
    (normBound : ‖coefficient 0‖ ≤ theta) (slot : RegularitySlot grade) :
    slotNorm (inverseFamily admissible coefficient grade -
      gradedIdentityCoefficient L parameters.sigma0 parameters.gamma ell grade dimension) slot ≤
        inverseSlotConstant constants offset grade lowBound theta (slotOrder slot + 1) *
          physicalBudget parameters field rho epsilon (offset + slotOrder slot) := by
  have inductionStatement : ∀ order : ℕ, ∀ slot : RegularitySlot grade, slotOrder slot = order →
      slotNorm (inverseFamily admissible coefficient grade -
        gradedIdentityCoefficient L parameters.sigma0 parameters.gamma ell grade dimension) slot ≤
          inverseSlotConstant constants offset grade lowBound theta (order + 1) *
            physicalBudget parameters field rho epsilon (offset + order) := by
    intro order
    induction order using Nat.strong_induction_on with
    | h order ih =>
      intro slot orderEquality
      have constantNonnegative := inverseSlotConstant_nonnegative constants nonnegative offset grade
        lowNonnegative thetaLt order
      have lowerBounds : ∀ other : RegularitySlot grade, slotOrder other < slotOrder slot →
          slotNorm (inverseFamily admissible coefficient grade -
            gradedIdentityCoefficient L parameters.sigma0 parameters.gamma ell grade dimension) other ≤
              inverseSlotConstant constants offset grade lowBound theta order *
                physicalBudget parameters field rho epsilon (offset + slotOrder other) := by
        intro other strictlyLower
        have otherLess : slotOrder other < order := by omega
        exact (ih (slotOrder other) otherLess other rfl).trans
          (mul_le_mul_of_nonneg_right
            (inverseSlotConstant_monotone constants nonnegative offset grade lowNonnegative thetaLt
              (by omega : slotOrder other + 1 ≤ order))
            (physicalBudget_nonnegative _ _ _ _ _))
      have step := inverse_slot_step parameters admissible offset grade field rho epsilon lowBound theta
        lowNonnegative thetaLt low positive coefficient coherent constants nonnegative bounds normBound slot
        (inverseSlotConstant constants offset grade lowBound theta order) constantNonnegative lowerBounds
      rw [orderEquality] at step
      exact step.trans (mul_le_mul_of_nonneg_right
        (by rw [inverseSlotConstant_succ]; exact le_add_of_nonneg_right constantNonnegative)
        (physicalBudget_nonnegative _ _ _ _ _))
  exact inductionStatement (slotOrder slot) slot rfl

def inverseNormConstant (constants : ℕ → ℝ) (offset grade : ℕ) (lowBound theta : ℝ) : ℝ :=
  (Fintype.card (DerivativeIndex grade) : ℝ) *
    inverseSlotConstant constants offset grade lowBound theta (grade + 1)

theorem inverseNormConstant_nonnegative (constants : ℕ → ℝ)
    (nonnegative : ∀ order, 0 ≤ constants order) (offset grade : ℕ)
    {lowBound theta : ℝ} (lowNonnegative : 0 ≤ lowBound) (thetaLt : theta < 1) :
    0 ≤ inverseNormConstant constants offset grade lowBound theta :=
  mul_nonneg (Nat.cast_nonneg _) (inverseSlotConstant_nonnegative constants nonnegative offset grade
    lowNonnegative thetaLt (grade + 1))

theorem inverse_norm_one_high {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (offset grade : ℕ) (field : ACore parameters 3) (rho epsilon lowBound theta : ℝ)
    (lowNonnegative : 0 ≤ lowBound) (thetaLt : theta < 1)
    (low : physicalBudget parameters field rho epsilon offset ≤ lowBound)
    {dimension : ℕ} (positive : 0 < dimension)
    (coefficient : CoefficientFamily L parameters.sigma0 parameters.gamma ell dimension dimension)
    (coherent : FamilyCoherent coefficient) (constants : ℕ → ℝ)
    (nonnegative : ∀ order, 0 ≤ constants order)
    (bounds : ∀ order, ‖coefficient order‖ ≤
      constants order * physicalBudget parameters field rho epsilon (offset + order))
    (normBound : ‖coefficient 0‖ ≤ theta) :
    ‖inverseFamily admissible coefficient grade -
      gradedIdentityCoefficient L parameters.sigma0 parameters.gamma ell grade dimension‖ ≤
        inverseNormConstant constants offset grade lowBound theta *
          physicalBudget parameters field rho epsilon (offset + grade) := by
  rw [norm_eq_topSlot_sum]
  calc
    _ ≤ ∑ index : DerivativeIndex grade,
        inverseSlotConstant constants offset grade lowBound theta (grade + 1) *
          physicalBudget parameters field rho epsilon (offset + grade) := by
      apply Finset.sum_le_sum
      intro index _
      have bound := inverse_slot_one_high parameters admissible offset grade field rho epsilon lowBound theta
        lowNonnegative thetaLt low positive coefficient coherent constants nonnegative bounds normBound (topSlot index)
      simpa only [topSlot_order] using bound
    _ = _ := by simp [inverseNormConstant, mul_assoc]

theorem oneHighInverseGoal : OneHighInverseGoal := by
  intro offset grade lowBound theta lowNonnegative thetaLt constants nonnegative
  refine ⟨inverseNormConstant constants offset grade lowBound theta,
    inverseNormConstant_nonnegative constants nonnegative offset grade lowNonnegative thetaLt, ?_⟩
  intro parameters L ell admissible dimension positive field rho epsilon coefficient coherent low bounds normBound
  refine ⟨analyticCapCoefficientNeumannInverse_baseBound admissible positive (coefficient 0) theta normBound thetaLt,
    gradedCoefficientNeumannInverse_realizes admissible positive (coefficient 0) (coefficient grade) theta
      (coherent_realizes coefficient coherent grade) normBound thetaLt, ?_⟩
  exact inverse_norm_one_high parameters admissible offset grade field rho epsilon lowBound theta lowNonnegative
    thetaLt low positive coefficient coherent constants nonnegative bounds normBound

end Grad.GaugeCoefficients.Physical.InverseAllocation

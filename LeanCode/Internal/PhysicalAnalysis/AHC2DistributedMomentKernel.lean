import AHC1AdditivePhaseRatio

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Neumann.Regularity

/-- The Cartesian derivative is unchanged when assigned its exact grade. -/
def apDerivativeAtGrade {grade : ℕ} (index : DerivativeIndex grade) (target : ℕ)
    (bound : derivativeOrder index ≤ target) : DerivativeIndex target :=
  ⟨(⟨index.val.1.val, by have := index.val.1.isLt; unfold derivativeOrder at bound; omega⟩,
    ⟨index.val.2.val, by have := index.val.2.isLt; unfold derivativeOrder at bound; omega⟩), bound⟩

theorem apDerivativeAtGrade_order {grade : ℕ} (index : DerivativeIndex grade) (target : ℕ)
    (bound : derivativeOrder index ≤ target) :
    derivativeOrder (apDerivativeAtGrade index target bound) = derivativeOrder index := rfl

def apDistributedOrder {grade : ℕ} (allocation : APAllocation grade) : ℕ :=
  grade - (derivativeOrder (apCoefficientIndex allocation) + derivativeOrder (apInputIndex allocation))

abbrev APDistributedMoment {grade : ℕ} (allocation : APAllocation grade) := Fin (apDistributedOrder allocation + 1)

def apDistributedCoefficientGrade {grade : ℕ} (allocation : APAllocation grade)
    (moment : APDistributedMoment allocation) : ℕ := derivativeOrder (apCoefficientIndex allocation) + moment.val

def apDistributedInputGrade {grade : ℕ} (allocation : APAllocation grade)
    (moment : APDistributedMoment allocation) : ℕ := grade - apDistributedCoefficientGrade allocation moment

theorem apDistributed_grades {grade : ℕ} (allocation : APAllocation grade)
    (moment : APDistributedMoment allocation) :
    derivativeOrder (apCoefficientIndex allocation) ≤ apDistributedCoefficientGrade allocation moment ∧
    derivativeOrder (apInputIndex allocation) ≤ apDistributedInputGrade allocation moment ∧
    apDistributedCoefficientGrade allocation moment + apDistributedInputGrade allocation moment = grade ∧
    apDistributedCoefficientGrade allocation moment ≤ grade ∧ apDistributedInputGrade allocation moment ≤ grade := by
  have allocationBound := apAllocation_order_le allocation
  have momentBound := moment.isLt
  unfold apDistributedOrder at momentBound
  dsimp only [apDistributedInputGrade, apDistributedCoefficientGrade]
  omega

def apDistributedCoefficientIndex {grade : ℕ} (allocation : APAllocation grade)
    (moment : APDistributedMoment allocation) : DerivativeIndex (apDistributedCoefficientGrade allocation moment) :=
  apDerivativeAtGrade (apCoefficientIndex allocation) _ (apDistributed_grades allocation moment).1

def apDistributedInputIndex {grade : ℕ} (allocation : APAllocation grade)
    (moment : APDistributedMoment allocation) : DerivativeIndex (apDistributedInputGrade allocation moment) :=
  apDerivativeAtGrade (apInputIndex allocation) _ (apDistributed_grades allocation moment).2.1

/-- A single bounded scalar kernel balances every exact binomial moment.
Its denominator is the sum of those moments, not a changed analytic phase. -/
def apDistributedRatio {grade : ℕ} (L sigma gamma ell : ℝ) (allocation : APAllocation grade)
    (input shift : ℤ) : C(ClosedDisk, ℝ) where
  toFun point :=
    (scaledCellWeight L ell (input + shift) ^ (grade - derivativeOrder (apOutputIndex allocation)) *
      apRatioDerivative sigma gamma ell (derivativeOrder (apPhaseIndex allocation))
        (apPhaseWord allocation) input shift point) /
    (originalEnvelope sigma gamma ell shift point.val *
      (scaledCellWeight L ell shift + scaledCellWeight L ell input) ^ apDistributedOrder allocation)
  continuous_toFun := by
    apply (continuous_const.mul (apRatioDerivative sigma gamma ell
      (derivativeOrder (apPhaseIndex allocation)) (apPhaseWord allocation) input shift).continuous).div
      (show Continuous (fun point : ClosedDisk => originalEnvelope sigma gamma ell shift point.val *
        (scaledCellWeight L ell shift + scaledCellWeight L ell input) ^ apDistributedOrder allocation) by
          unfold originalEnvelope
          fun_prop)
    intro point
    exact (mul_pos (Real.exp_pos _)
      (pow_pos (add_pos (lt_of_lt_of_le zero_lt_one (scaledCellWeight_one_le L ell shift))
        (lt_of_lt_of_le zero_lt_one (scaledCellWeight_one_le L ell input))) _)).ne'

theorem apDistributedRatio_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade : ℕ} (allocation : APAllocation grade) (input shift : ℤ) (point : ClosedDisk) :
    |apDistributedRatio L sigma gamma ell allocation input shift point| ≤
      apRatioConstant L sigma gamma (derivativeOrder (apPhaseIndex allocation)) := by
  let frequency := scaledCellWeight L ell shift + scaledCellWeight L ell input
  have frequencyPositive : 0 < frequency := add_pos
    (lt_of_lt_of_le zero_lt_one (scaledCellWeight_one_le L ell shift))
    (lt_of_lt_of_le zero_lt_one (scaledCellWeight_one_le L ell input))
  have denominatorPositive : 0 < originalEnvelope sigma gamma ell shift point.val * frequency ^ apDistributedOrder allocation :=
    mul_pos (Real.exp_pos _) (pow_pos frequencyPositive _)
  have frequencyBound : scaledCellWeight L ell (input + shift) ≤ frequency :=
    (scaledCellWeight_additive L ell input shift).trans_eq (add_comm _ _)
  have orderEquality : grade - derivativeOrder (apOutputIndex allocation) +
      derivativeOrder (apPhaseIndex allocation) = apDistributedOrder allocation := by
    have order := apAllocation_order allocation
    have bound : derivativeOrder (apOutputIndex allocation) ≤ grade := allocation.1.property
    unfold apDistributedOrder
    omega
  dsimp only [apDistributedRatio, ContinuousMap.coe_mk]
  rw [abs_div, abs_mul, abs_of_nonneg (pow_nonneg (scaledCellWeight_nonnegative L ell _) _),
    abs_of_pos denominatorPositive]
  apply (div_le_iff₀ denominatorPositive).mpr
  have ratio := apRatioDerivative_additive_bound admissible (derivativeOrder (apPhaseIndex allocation))
    (apPhaseWord allocation) input shift point
  calc
    _ ≤ frequency ^ (grade - derivativeOrder (apOutputIndex allocation)) *
        (apRatioConstant L sigma gamma (derivativeOrder (apPhaseIndex allocation)) *
          frequency ^ derivativeOrder (apPhaseIndex allocation) * originalEnvelope sigma gamma ell shift point.val) :=
      mul_le_mul (pow_le_pow_left₀ (scaledCellWeight_nonnegative L ell _) frequencyBound _) ratio
        (abs_nonneg _) (pow_nonneg frequencyPositive.le _)
    _ = apRatioConstant L sigma gamma (derivativeOrder (apPhaseIndex allocation)) *
        (originalEnvelope sigma gamma ell shift point.val * frequency ^ apDistributedOrder allocation) := by
      rw [← orderEquality, pow_add]
      ring

theorem apDistributedMoment_scale {grade : ℕ} (L sigma gamma ell : ℝ) (allocation : APAllocation grade)
    (moment : APDistributedMoment allocation) (input shift : ℤ) (point : ClosedDisk) :
    coefficientScale L sigma gamma ell (apDistributedCoefficientGrade allocation moment) shift
      (apDistributedCoefficientIndex allocation moment) point *
        scaledCellWeight L ell input ^ (apDistributedInputGrade allocation moment -
          derivativeOrder (apDistributedInputIndex allocation moment)) =
      originalEnvelope sigma gamma ell shift point.val *
        scaledCellWeight L ell shift ^ moment.val *
          scaledCellWeight L ell input ^ (apDistributedOrder allocation - moment.val) := by
  have inputOrder : apDistributedInputGrade allocation moment - derivativeOrder (apDistributedInputIndex allocation moment) =
      apDistributedOrder allocation - moment.val := by
    have bound := apAllocation_order_le allocation
    have momentBound := moment.isLt
    simp only [apDistributedInputIndex, apDerivativeAtGrade_order]
    unfold apDistributedInputGrade apDistributedCoefficientGrade apDistributedOrder at *
    omega
  rw [coefficientScale, inputOrder]
  have coefficientOrder : apDistributedCoefficientGrade allocation moment -
      derivativeOrder (apDistributedCoefficientIndex allocation moment) = moment.val := by
    change derivativeOrder (apCoefficientIndex allocation) + moment.val - derivativeOrder (apCoefficientIndex allocation) = moment.val
    omega
  rw [coefficientOrder]

theorem apDistributedMoment_sum {grade : ℕ} (L sigma gamma ell : ℝ) (allocation : APAllocation grade)
    (input shift : ℤ) (point : ClosedDisk) :
    (∑ moment : APDistributedMoment allocation,
      (Nat.choose (apDistributedOrder allocation) moment.val : ℝ) *
      coefficientScale L sigma gamma ell (apDistributedCoefficientGrade allocation moment) shift
        (apDistributedCoefficientIndex allocation moment) point *
      scaledCellWeight L ell input ^ (apDistributedInputGrade allocation moment -
        derivativeOrder (apDistributedInputIndex allocation moment))) =
    originalEnvelope sigma gamma ell shift point.val *
      (scaledCellWeight L ell shift + scaledCellWeight L ell input) ^ apDistributedOrder allocation := by
  simp_rw [mul_assoc (Nat.choose _ _ : ℝ), apDistributedMoment_scale]
  rw [add_pow, Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun moment : ℕ =>
    (Nat.choose (apDistributedOrder allocation) moment : ℝ) *
      (originalEnvelope sigma gamma ell shift point.val * scaledCellWeight L ell shift ^ moment *
        scaledCellWeight L ell input ^ (apDistributedOrder allocation - moment)))]
  apply Finset.sum_congr rfl
  intro moment _
  ring

end Grad.GaugeCoefficients.Physical.RadialLedger

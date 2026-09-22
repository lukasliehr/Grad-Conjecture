import GC16Interface

noncomputable section

set_option maxHeartbeats 1200000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.InverseAllocation

open Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.Allocation

theorem coherent_realizes {L sigma gamma ell : ℝ} {dimension : ℕ}
    (coefficient : CoefficientFamily L sigma gamma ell dimension dimension)
    (coherent : FamilyCoherent coefficient) (grade : ℕ) :
    RealizesSameCoefficient (coefficient 0) (coefficient grade) := by
  intro cell point
  exact coherent grade 0 (zeroDerivativeIndexAt grade) zeroDerivativeIndex rfl cell point

theorem coherent_zero_slot_norm {L sigma gamma ell : ℝ} {dimension grade : ℕ}
    (coefficient : CoefficientFamily L sigma gamma ell dimension dimension)
    (coherent : FamilyCoherent coefficient) :
    slotNorm (coefficient grade) (zeroRegularitySlot grade) = ‖coefficient 0‖ :=
  zeroSlotNorm_eq_baseNorm (coherent_realizes coefficient coherent grade)

theorem slotNorm_add_le {L sigma gamma ell : ℝ} {dimension grade : ℕ}
    (first second : Coefficient L sigma gamma ell grade dimension dimension)
    (slot : RegularitySlot grade) :
    slotNorm (first + second) slot ≤ slotNorm first slot + slotNorm second slot := by
  have coordinate (cell : ℤ) :
      slotCoordinate (first + second) slot cell =
        slotCoordinate first slot cell + slotCoordinate second slot cell :=
    (slotCoordinateCLM L sigma gamma ell grade dimension dimension cell slot).map_add first second
  have coordinateBound (cell : ℤ) :
      ‖slotCoordinate (first + second) slot cell‖ ≤
        ‖slotCoordinate first slot cell‖ + ‖slotCoordinate second slot cell‖ := by
    rw [coordinate]
    exact norm_add_le (slotCoordinate first slot cell) (slotCoordinate second slot cell)
  unfold slotNorm
  calc
    _ ≤ ∑' cell : ℤ, (‖slotCoordinate first slot cell‖ + ‖slotCoordinate second slot cell‖) :=
      Summable.tsum_le_tsum coordinateBound
        (slotCoordinate_norm_summable (first + second) slot)
        ((slotCoordinate_norm_summable first slot).add (slotCoordinate_norm_summable second slot))
    _ = _ := (slotCoordinate_norm_summable first slot).tsum_add
      (slotCoordinate_norm_summable second slot)

theorem identity_slotCoordinate_norm_le (L sigma gamma ell : ℝ) (dimension grade : ℕ)
    (slot : RegularitySlot grade) (cell : ℤ) :
    ‖slotCoordinate (gradedIdentityCoefficient L sigma gamma ell grade dimension) slot cell‖ ≤
      if cell = 0 then 1 else 0 := by
  apply (ContinuousMap.norm_le _ (by split_ifs <;> positivity)).2
  intro point
  rw [slotCoordinate_apply]
  by_cases zeroOrder : derivativeOrder (slotDerivativeIndex slot) = 0
  · rw [derivativeIndex_eq_zeroDerivativeIndexAt_of_order_zero _ zeroOrder,
      gradedIdentityCoefficient_zeroDerivative]
    by_cases zeroCell : cell = 0
    · subst cell
      simp only [ite_true]
      have scalarOne : ((originalEnvelope sigma gamma ell 0 point.val *
          scaledCellWeight L ell 0 ^ (slot.moment : ℕ) : ℝ) : ℂ) = 1 := by
        simp [originalEnvelope, scaledCellWeight]
      rw [scalarOne, one_smul]
      exact ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := PhysicalValue dimension)
    · simp only [zeroCell, ite_false]
      have zeroScaled : ((originalEnvelope sigma gamma ell cell point.val *
          scaledCellWeight L ell cell ^ (slot.moment : ℕ) : ℝ) : ℂ) •
          (0 : OperatorValue dimension dimension) = 0 := by
        apply ContinuousLinearMap.ext
        intro vector
        simp only [smul_apply, zero_apply, smul_zero]
      rw [zeroScaled, norm_zero]
  · rw [gradedIdentityCoefficient_positiveDerivative L sigma gamma ell grade dimension cell
      (slotDerivativeIndex slot) (Nat.pos_of_ne_zero zeroOrder)]
    have zeroScaled : ((originalEnvelope sigma gamma ell cell point.val *
        scaledCellWeight L ell cell ^ (slot.moment : ℕ) : ℝ) : ℂ) •
        (0 : OperatorValue dimension dimension) = 0 := by
      apply ContinuousLinearMap.ext
      intro vector
      simp only [smul_apply, zero_apply, smul_zero]
    rw [zeroScaled, norm_zero]
    split_ifs <;> norm_num

theorem identity_slotNorm_le (L sigma gamma ell : ℝ) (dimension grade : ℕ)
    (slot : RegularitySlot grade) :
    slotNorm (gradedIdentityCoefficient L sigma gamma ell grade dimension) slot ≤ 1 := by
  unfold slotNorm
  calc
    _ ≤ ∑' cell : ℤ, (if cell = 0 then (1 : ℝ) else 0) :=
      Summable.tsum_le_tsum (identity_slotCoordinate_norm_le L sigma gamma ell dimension grade slot)
        (slotCoordinate_norm_summable _ slot) (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
    _ = 1 := by simp

theorem inverse_deviation_fixedPoint {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (positive : 0 < dimension)
    (coefficient : CoefficientFamily L sigma gamma ell dimension dimension)
    (coherent : FamilyCoherent coefficient) (theta : ℝ)
    (normBound : ‖coefficient 0‖ ≤ theta) (thetaLt : theta < 1) :
    inverseFamily admissible coefficient grade -
        gradedIdentityCoefficient L sigma gamma ell grade dimension =
      coefficientComposition admissible grade (coefficient grade)
          (gradedIdentityCoefficient L sigma gamma ell grade dimension) +
        coefficientComposition admissible grade (coefficient grade)
          (inverseFamily admissible coefficient grade -
            gradedIdentityCoefficient L sigma gamma ell grade dimension) := by
  have fixedPoint := gradedCoefficientNeumannInverse_fixedPoint admissible positive (coefficient 0)
    (coefficient grade) theta (coherent_realizes coefficient coherent grade) normBound thetaLt
  have difference : inverseFamily admissible coefficient grade -
      gradedIdentityCoefficient L sigma gamma ell grade dimension =
      coefficientComposition admissible grade (coefficient grade)
        (inverseFamily admissible coefficient grade) := by
    change gradedCoefficientNeumannInverse admissible (coefficient grade) - _ = _
    rw [fixedPoint]
    abel
  calc
    _ = coefficientComposition admissible grade (coefficient grade)
        (inverseFamily admissible coefficient grade) := difference
    _ = coefficientComposition admissible grade (coefficient grade)
        (gradedIdentityCoefficient L sigma gamma ell grade dimension +
          (inverseFamily admissible coefficient grade -
            gradedIdentityCoefficient L sigma gamma ell grade dimension)) := by
      congr 1
      abel
    _ = _ := (compositionRightLinear admissible grade (coefficient grade)).map_add _ _

end Grad.GaugeCoefficients.Physical.InverseAllocation

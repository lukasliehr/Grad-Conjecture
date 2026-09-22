import GC12Allocation

noncomputable section

set_option maxHeartbeats 3000000

open Grad.ClosedJets Grad.GaugeCoefficients.Envelope
open scoped BigOperators Topology ENNReal

namespace Grad.GaugeCoefficients.Neumann.Regularity

open Grad.GaugeCoefficients.Algebra

/-- A Cartesian derivative together with a remaining polynomial cell moment;
the total regularity spent is at most the fixed grade. -/
structure RegularitySlot (grade : ℕ) where
  first : Fin (grade + 1)
  second : Fin (grade + 1)
  moment : Fin (grade + 1)
  total_le : (first : ℕ) + (second : ℕ) + (moment : ℕ) ≤ grade
deriving Fintype, DecidableEq

def slotDerivativeIndex {grade : ℕ} (slot : RegularitySlot grade) :
    DerivativeIndex grade :=
  ⟨(slot.first, slot.second), (Nat.le_add_right _ _).trans slot.total_le⟩

def slotOrder {grade : ℕ} (slot : RegularitySlot grade) : ℕ :=
  (slot.first : ℕ) + (slot.second : ℕ) + (slot.moment : ℕ)

def slotGap {grade : ℕ} (slot : RegularitySlot grade) : ℕ :=
  grade - slotOrder slot

def zeroRegularitySlot (grade : ℕ) : RegularitySlot grade :=
  ⟨⟨0, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩, by simp⟩

@[simp] theorem slotDerivativeIndex_zero (grade : ℕ) :
    slotDerivativeIndex (zeroRegularitySlot grade) = zeroDerivativeIndexAt grade := by
  rfl

@[simp] theorem slotGap_zero (grade : ℕ) :
    slotGap (zeroRegularitySlot grade) = grade := by
  simp [slotGap, slotOrder, zeroRegularitySlot]

/-- The scalar `l¹` coordinate carrying exactly the moment requested by a
regularity slot.  The frozen grade norm carries the larger top moment, so this
coordinate is obtained by a contraction. -/
def slotCoordinate {L sigma gamma ell : ℝ} {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (slot : RegularitySlot grade) (cell : ℤ) :
    ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) :=
  ((scaledCellWeight L ell cell ^ slotGap slot : ℂ)⁻¹) •
    weightedDerivative coefficient cell (slotDerivativeIndex slot)

theorem slotCoordinate_apply {L sigma gamma ell : ℝ}
    {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (slot : RegularitySlot grade) (cell : ℤ) (point : ClosedDisk) :
    slotCoordinate coefficient slot cell point =
      ((originalEnvelope sigma gamma ell cell point.val *
          scaledCellWeight L ell cell ^ (slot.moment : ℕ) : ℝ) : ℂ) •
        coefficientDerivative coefficient cell (slotDerivativeIndex slot) point := by
  unfold slotCoordinate
  change ((scaledCellWeight L ell cell ^ slotGap slot : ℂ)⁻¹) •
      weightedDerivative coefficient cell (slotDerivativeIndex slot) point = _
  rw [weighted_derivative_literal grade inputDimension outputDimension coefficient cell
    (slotDerivativeIndex slot) point]
  have exponentIdentity :
      grade - derivativeOrder (slotDerivativeIndex slot) =
        slotGap slot + (slot.moment : ℕ) := by
    have totalLe : (slot.first : ℕ) + (slot.second : ℕ) +
        (slot.moment : ℕ) ≤ grade := slot.total_le
    change grade - ((slot.first : ℕ) + (slot.second : ℕ)) =
      grade - ((slot.first : ℕ) + (slot.second : ℕ) +
        (slot.moment : ℕ)) + (slot.moment : ℕ)
    omega
  unfold coefficientScale
  rw [exponentIdentity, pow_add]
  rw [smul_smul]
  have weightNonzero : (scaledCellWeight L ell cell : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (lt_of_lt_of_le zero_lt_one (scaledCellWeight_one_le L ell cell)).ne'
  push_cast
  field_simp

theorem slotCoordinate_norm_le {L sigma gamma ell : ℝ}
    {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (slot : RegularitySlot grade) (cell : ℤ) :
    ‖slotCoordinate coefficient slot cell‖ ≤
      ‖weightedDerivative coefficient cell (slotDerivativeIndex slot)‖ := by
  unfold slotCoordinate
  have scalarLe : ‖((scaledCellWeight L ell cell ^ slotGap slot : ℂ)⁻¹)‖ ≤ 1 := by
    rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (scaledCellWeight_nonnegative L ell cell)]
    exact inv_le_one_of_one_le₀
      (one_le_pow₀ (scaledCellWeight_one_le L ell cell))
  apply (ContinuousMap.norm_le
    (((scaledCellWeight L ell cell ^ slotGap slot : ℂ)⁻¹) •
      weightedDerivative coefficient cell (slotDerivativeIndex slot))
    (norm_nonneg (weightedDerivative coefficient cell
      (slotDerivativeIndex slot)))).2
  intro point
  change ‖((scaledCellWeight L ell cell ^ slotGap slot : ℂ)⁻¹) •
      weightedDerivative coefficient cell (slotDerivativeIndex slot) point‖ ≤ _
  calc
    _ ≤ ‖((scaledCellWeight L ell cell ^ slotGap slot : ℂ)⁻¹)‖ *
        ‖weightedDerivative coefficient cell (slotDerivativeIndex slot) point‖ :=
      norm_smul_le _ _
    _ ≤ 1 * ‖weightedDerivative coefficient cell (slotDerivativeIndex slot)‖ :=
      mul_le_mul scalarLe (ContinuousMap.norm_coe_le_norm _ point)
        (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem slotCoordinate_norm_summable {L sigma gamma ell : ℝ}
    {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (slot : RegularitySlot grade) :
    Summable (fun cell : ℤ => ‖slotCoordinate coefficient slot cell‖) :=
  Summable.of_nonneg_of_le
    (fun cell => norm_nonneg (slotCoordinate coefficient slot cell))
    (slotCoordinate_norm_le coefficient slot)
    (coordinate_norm_summable coefficient.1 (slotDerivativeIndex slot))

def slotNorm {L sigma gamma ell : ℝ} {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (slot : RegularitySlot grade) : ℝ :=
  ∑' cell : ℤ, ‖slotCoordinate coefficient slot cell‖

theorem slotNorm_nonnegative {L sigma gamma ell : ℝ}
    {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (slot : RegularitySlot grade) : 0 ≤ slotNorm coefficient slot :=
  tsum_nonneg fun cell => norm_nonneg (slotCoordinate coefficient slot cell)

theorem slotNorm_le_norm {L sigma gamma ell : ℝ}
    {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (slot : RegularitySlot grade) :
    slotNorm coefficient slot ≤ ‖coefficient‖ := by
  calc
    slotNorm coefficient slot ≤
        ∑' cell : ℤ,
          ‖weightedDerivative coefficient cell (slotDerivativeIndex slot)‖ :=
      Summable.tsum_le_tsum (slotCoordinate_norm_le coefficient slot)
        (slotCoordinate_norm_summable coefficient slot)
        (coordinate_norm_summable coefficient.1 (slotDerivativeIndex slot))
    _ ≤ ‖coefficient‖ :=
      coordinate_norm_sum_le coefficient.1 (slotDerivativeIndex slot)

theorem zeroSlotCoordinate_eq_baseWeightedDerivative
    {L sigma gamma ell : ℝ} {grade dimension : ℕ}
    {base : BaseCoefficient L sigma gamma ell dimension}
    {graded : Coefficient L sigma gamma ell grade dimension dimension}
    (realizes : RealizesSameCoefficient base graded) (cell : ℤ) :
    slotCoordinate graded (zeroRegularitySlot grade) cell =
      weightedDerivative base cell zeroDerivativeIndex := by
  apply ContinuousMap.ext
  intro point
  unfold slotCoordinate
  rw [slotDerivativeIndex_zero, slotGap_zero]
  change ((scaledCellWeight L ell cell ^ grade : ℂ)⁻¹) •
      weightedDerivative graded cell (zeroDerivativeIndexAt grade) point =
    weightedDerivative base cell zeroDerivativeIndex point
  rw [weighted_derivative_literal grade dimension dimension graded cell
    (zeroDerivativeIndexAt grade) point]
  rw [realizes cell point]
  rw [weighted_derivative_literal 0 dimension dimension base cell
    zeroDerivativeIndex point]
  unfold coefficientScale
  rw [derivativeOrder_zeroDerivativeIndexAt]
  simp only [derivativeOrder, zeroDerivativeIndex, Nat.zero_sub, Nat.sub_zero,
    pow_zero, mul_one]
  change ((scaledCellWeight L ell cell ^ grade : ℂ)⁻¹) •
      (((originalEnvelope sigma gamma ell cell point.val *
          scaledCellWeight L ell cell ^ grade : ℝ) : ℂ) •
        coefficientValue base cell point) =
    (originalEnvelope sigma gamma ell cell point.val : ℂ) •
      coefficientValue base cell point
  apply ContinuousLinearMap.ext
  intro value
  simp only [smul_apply, smul_smul]
  have weightNonzero : (scaledCellWeight L ell cell : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (lt_of_lt_of_le zero_lt_one (scaledCellWeight_one_le L ell cell)).ne'
  push_cast
  field_simp

theorem zeroSlotNorm_eq_baseNorm
    {L sigma gamma ell : ℝ} {grade dimension : ℕ}
    {base : BaseCoefficient L sigma gamma ell dimension}
    {graded : Coefficient L sigma gamma ell grade dimension dimension}
    (realizes : RealizesSameCoefficient base graded) :
    slotNorm graded (zeroRegularitySlot grade) = ‖base‖ := by
  unfold slotNorm
  simp_rw [zeroSlotCoordinate_eq_baseWeightedDerivative realizes]
  rw [coefficient_norm_formula]
  rw [derivativeIndex_zero_univ]
  simp only [Finset.sum_singleton]

end Grad.GaugeCoefficients.Neumann.Regularity

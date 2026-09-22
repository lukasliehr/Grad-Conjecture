import GC12SlotSplit

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

open Grad.GenericCarriers Grad.ClosedJets Grad.GaugeCoefficients.Envelope
open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Neumann.Regularity

open Grad.GaugeCoefficients.Algebra

def combineSlotSplit {grade : ℕ} {slot : RegularitySlot grade}
    (physical : DerivativeSplit (slotDerivativeIndex slot))
    (moment : Fin ((slot.moment : ℕ) + 1)) : RegularitySlotSplit slot where
  first := physical.1
  second := physical.2
  moment := moment

@[simp] theorem slotPhysicalSplit_combine {grade : ℕ}
    {slot : RegularitySlot grade}
    (physical : DerivativeSplit (slotDerivativeIndex slot))
    (moment : Fin ((slot.moment : ℕ) + 1)) :
    slotPhysicalSplit (combineSlotSplit physical moment) = physical := rfl

theorem slotSplitMultiplicity_combine {grade : ℕ}
    {slot : RegularitySlot grade}
    (physical : DerivativeSplit (slotDerivativeIndex slot))
    (moment : Fin ((slot.moment : ℕ) + 1)) :
    slotSplitMultiplicity (combineSlotSplit physical moment) =
      splitMultiplicity (slotDerivativeIndex slot) physical *
        Nat.choose (slot.moment : ℕ) (moment : ℕ) := by
  unfold slotSplitMultiplicity splitMultiplicity combineSlotSplit slotDerivativeIndex
  ring

theorem slotCompositionTerm_point_norm_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (outer inner : Coefficient L sigma gamma ell grade dimension dimension)
    (slot : RegularitySlot grade) (first second : ℤ)
    (physical : DerivativeSplit (slotDerivativeIndex slot))
    (point : ClosedDisk) :
    ‖(coefficientMomentWeight L sigma gamma ell (first + second)
          (slot.moment : ℕ) point : ℂ) •
        ((splitMultiplicity (slotDerivativeIndex slot) physical : ℂ) •
          (coefficientDerivative outer first
            (lowerDerivativeIndex (slotDerivativeIndex slot) physical) point).comp
          (coefficientDerivative inner second
            (upperDerivativeIndex (slotDerivativeIndex slot) physical) point))‖ ≤
      ∑ moment : Fin ((slot.moment : ℕ) + 1),
        (slotSplitMultiplicity (combineSlotSplit physical moment) : ℝ) *
          ‖slotCoordinate outer
            (lowerRegularitySlot (combineSlotSplit physical moment)) first‖ *
          ‖slotCoordinate inner
            (upperRegularitySlot (combineSlotSplit physical moment)) second‖ := by
  let outerDerivative := coefficientDerivative outer first
    (lowerDerivativeIndex (slotDerivativeIndex slot) physical) point
  let innerDerivative := coefficientDerivative inner second
    (upperDerivativeIndex (slotDerivativeIndex slot) physical) point
  have outputWeightNonnegative : 0 ≤
      coefficientMomentWeight L sigma gamma ell (first + second)
        (slot.moment : ℕ) point := by
    unfold coefficientMomentWeight
    exact mul_nonneg (Real.exp_pos _).le
      (pow_nonneg (scaledCellWeight_nonnegative L ell _) _)
  have physicalMultiplicityNonnegative : 0 ≤
      (splitMultiplicity (slotDerivativeIndex slot) physical : ℝ) := by positivity
  have compositionNorm : ‖outerDerivative.comp innerDerivative‖ ≤
      ‖outerDerivative‖ * ‖innerDerivative‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have weightBound := coefficientMomentWeight_add_le admissible first second
    (slot.moment : ℕ) point
  calc
    ‖(coefficientMomentWeight L sigma gamma ell (first + second)
          (slot.moment : ℕ) point : ℂ) •
        ((splitMultiplicity (slotDerivativeIndex slot) physical : ℂ) •
          outerDerivative.comp innerDerivative)‖ ≤
      coefficientMomentWeight L sigma gamma ell (first + second)
          (slot.moment : ℕ) point *
        (splitMultiplicity (slotDerivativeIndex slot) physical : ℝ) *
          (‖outerDerivative‖ * ‖innerDerivative‖) := by
      rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_natCast,
        Real.norm_eq_abs, abs_of_nonneg outputWeightNonnegative]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left compositionNorm
        (mul_nonneg outputWeightNonnegative physicalMultiplicityNonnegative)
    _ ≤ (∑ moment : Fin ((slot.moment : ℕ) + 1),
          (Nat.choose (slot.moment : ℕ) (moment : ℕ) : ℝ) *
            coefficientMomentWeight L sigma gamma ell first (moment : ℕ) point *
            coefficientMomentWeight L sigma gamma ell second
              ((slot.moment : ℕ) - (moment : ℕ)) point) *
        (splitMultiplicity (slotDerivativeIndex slot) physical : ℝ) *
          (‖outerDerivative‖ * ‖innerDerivative‖) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right weightBound physicalMultiplicityNonnegative)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ∑ moment : Fin ((slot.moment : ℕ) + 1),
        (slotSplitMultiplicity (combineSlotSplit physical moment) : ℝ) *
          (coefficientMomentWeight L sigma gamma ell first (moment : ℕ) point *
            ‖outerDerivative‖) *
          (coefficientMomentWeight L sigma gamma ell second
              ((slot.moment : ℕ) - (moment : ℕ)) point *
            ‖innerDerivative‖) := by
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro moment _membership
      rw [slotSplitMultiplicity_combine]
      push_cast
      ring
    _ ≤ ∑ moment : Fin ((slot.moment : ℕ) + 1),
        (slotSplitMultiplicity (combineSlotSplit physical moment) : ℝ) *
          ‖slotCoordinate outer
            (lowerRegularitySlot (combineSlotSplit physical moment)) first‖ *
          ‖slotCoordinate inner
            (upperRegularitySlot (combineSlotSplit physical moment)) second‖ := by
      apply Finset.sum_le_sum
      intro moment _membership
      have outerPoint :
          coefficientMomentWeight L sigma gamma ell first (moment : ℕ) point *
              ‖outerDerivative‖ =
            ‖slotCoordinate outer
              (lowerRegularitySlot (combineSlotSplit physical moment)) first point‖ := by
        rw [slotCoordinate_apply]
        rw [slotDerivativeIndex_lower, slotPhysicalSplit_combine]
        simp only [lowerRegularitySlot, combineSlotSplit]
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by
            exact mul_nonneg (Real.exp_pos _).le
              (pow_nonneg (scaledCellWeight_nonnegative L ell _) _))]
        unfold coefficientMomentWeight outerDerivative
        rfl
      have innerPoint :
          coefficientMomentWeight L sigma gamma ell second
                ((slot.moment : ℕ) - (moment : ℕ)) point *
              ‖innerDerivative‖ =
            ‖slotCoordinate inner
              (upperRegularitySlot (combineSlotSplit physical moment)) second point‖ := by
        rw [slotCoordinate_apply]
        rw [slotDerivativeIndex_upper, slotPhysicalSplit_combine]
        simp only [upperRegularitySlot, combineSlotSplit]
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by
            exact mul_nonneg (Real.exp_pos _).le
              (pow_nonneg (scaledCellWeight_nonnegative L ell _) _))]
        unfold coefficientMomentWeight innerDerivative
        rfl
      rw [outerPoint, innerPoint]
      gcongr
      · exact ContinuousMap.norm_coe_le_norm _ point
      · exact ContinuousMap.norm_coe_le_norm _ point

def slotWeightedCompositionTerm (L sigma gamma ell : ℝ) (grade : ℕ)
    {dimension : ℕ}
    (outer inner : Coefficient L sigma gamma ell grade dimension dimension)
    (cell first : ℤ) (slot : RegularitySlot grade)
    (physical : DerivativeSplit (slotDerivativeIndex slot)) :
    ContinuousMap ClosedDisk (OperatorValue dimension dimension) :=
  ((scaledCellWeight L ell cell ^ slotGap slot : ℂ)⁻¹) •
    ((splitMultiplicity (slotDerivativeIndex slot) physical : ℂ) •
      weightedCompositionTerm L sigma gamma ell grade outer.1 first inner.1
        (cell - first) (slotDerivativeIndex slot) physical)

theorem slotWeightedCompositionTerm_apply {L sigma gamma ell : ℝ}
    (grade : ℕ) {dimension : ℕ}
    (outer inner : Coefficient L sigma gamma ell grade dimension dimension)
    (cell first : ℤ) (slot : RegularitySlot grade)
    (physical : DerivativeSplit (slotDerivativeIndex slot)) (point : ClosedDisk) :
    slotWeightedCompositionTerm L sigma gamma ell grade outer inner cell first
        slot physical point =
      (coefficientMomentWeight L sigma gamma ell cell (slot.moment : ℕ) point : ℂ) •
        ((splitMultiplicity (slotDerivativeIndex slot) physical : ℂ) •
          (coefficientDerivative outer first
            (lowerDerivativeIndex (slotDerivativeIndex slot) physical) point).comp
          (coefficientDerivative inner (cell - first)
            (upperDerivativeIndex (slotDerivativeIndex slot) physical) point)) := by
  unfold slotWeightedCompositionTerm
  change ((scaledCellWeight L ell cell ^ slotGap slot : ℂ)⁻¹) •
      ((splitMultiplicity (slotDerivativeIndex slot) physical : ℂ) •
        weightedCompositionTerm L sigma gamma ell grade outer.1 first inner.1
          (cell - first) (slotDerivativeIndex slot) physical point) = _
  have unweighted := weightedCompositionTerm_unweighted grade outer inner cell first
    (slotDerivativeIndex slot) physical point
  have exponentIdentity :
      grade - derivativeOrder (slotDerivativeIndex slot) =
        slotGap slot + (slot.moment : ℕ) := by
    have totalLe : (slot.first : ℕ) + (slot.second : ℕ) +
        (slot.moment : ℕ) ≤ grade := slot.total_le
    change grade - ((slot.first : ℕ) + (slot.second : ℕ)) =
      grade - ((slot.first : ℕ) + (slot.second : ℕ) +
        (slot.moment : ℕ)) + (slot.moment : ℕ)
    omega
  have scaleIdentity :
      ((scaledCellWeight L ell cell ^ slotGap slot : ℂ)⁻¹) =
        (coefficientMomentWeight L sigma gamma ell cell (slot.moment : ℕ) point : ℂ) *
          (coefficientScale L sigma gamma ell grade cell
            (slotDerivativeIndex slot) point : ℂ)⁻¹ := by
    unfold coefficientMomentWeight coefficientScale
    rw [exponentIdentity, pow_add]
    have envelopeNonzero :
        (originalEnvelope sigma gamma ell cell point.val : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
    have weightNonzero : (scaledCellWeight L ell cell : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr
        (lt_of_lt_of_le zero_lt_one (scaledCellWeight_one_le L ell cell)).ne'
    push_cast
    field_simp
  rw [scaleIdentity]
  simpa only [smul_smul, mul_assoc, mul_left_comm, mul_comm] using congrArg
    (fun value : OperatorValue dimension dimension =>
      (coefficientMomentWeight L sigma gamma ell cell
        (slot.moment : ℕ) point : ℂ) •
        ((splitMultiplicity (slotDerivativeIndex slot) physical : ℂ) • value))
    unweighted

theorem slotWeightedCompositionTerm_norm_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) {dimension : ℕ}
    (outer inner : Coefficient L sigma gamma ell grade dimension dimension)
    (cell first : ℤ) (slot : RegularitySlot grade)
    (physical : DerivativeSplit (slotDerivativeIndex slot)) :
    ‖slotWeightedCompositionTerm L sigma gamma ell grade outer inner cell first
        slot physical‖ ≤
      ∑ moment : Fin ((slot.moment : ℕ) + 1),
        (slotSplitMultiplicity (combineSlotSplit physical moment) : ℝ) *
          ‖slotCoordinate outer
            (lowerRegularitySlot (combineSlotSplit physical moment)) first‖ *
          ‖slotCoordinate inner
            (upperRegularitySlot (combineSlotSplit physical moment)) (cell - first)‖ := by
  apply (ContinuousMap.norm_le
    (slotWeightedCompositionTerm L sigma gamma ell grade outer inner cell first
      slot physical) (by positivity)).2
  intro point
  rw [slotWeightedCompositionTerm_apply]
  simpa only [show first + (cell - first) = cell by omega] using
    slotCompositionTerm_point_norm_le admissible outer inner slot first
      (cell - first) physical point

def slotCompositionCoordinateMajorant {L sigma gamma ell : ℝ}
    {grade dimension : ℕ}
    (outer inner : Coefficient L sigma gamma ell grade dimension dimension)
    (cell : ℤ) (slot : RegularitySlot grade) : ℝ :=
  ∑ physical : DerivativeSplit (slotDerivativeIndex slot),
    ∑ moment : Fin ((slot.moment : ℕ) + 1),
      let split := combineSlotSplit physical moment
      (slotSplitMultiplicity split : ℝ) *
        ∑' first : ℤ,
          ‖slotCoordinate outer (lowerRegularitySlot split) first‖ *
            ‖slotCoordinate inner (upperRegularitySlot split) (cell - first)‖

theorem slotConvolutionNorm_reindexed_summable {L sigma gamma ell : ℝ}
    {grade dimension : ℕ}
    (outer inner : Coefficient L sigma gamma ell grade dimension dimension)
    (outerSlot innerSlot : RegularitySlot grade) :
    Summable (fun pair : ℤ × ℤ =>
      ‖slotCoordinate outer outerSlot pair.2‖ *
        ‖slotCoordinate inner innerSlot (pair.1 - pair.2)‖) := by
  have pairSummable := (slotCoordinate_norm_summable outer outerSlot).mul_of_nonneg
    (slotCoordinate_norm_summable inner innerSlot)
    (fun cell => norm_nonneg (slotCoordinate outer outerSlot cell))
    (fun cell => norm_nonneg (slotCoordinate inner innerSlot cell))
  change Summable ((fun pair : ℤ × ℤ =>
    ‖slotCoordinate outer outerSlot pair.1‖ *
      ‖slotCoordinate inner innerSlot pair.2‖) ∘ cellConvolutionEquiv)
  exact cellConvolutionEquiv.summable_iff.mpr pairSummable

theorem slotConvolutionNorm_fixed_summable {L sigma gamma ell : ℝ}
    {grade dimension : ℕ}
    (outer inner : Coefficient L sigma gamma ell grade dimension dimension)
    (outerSlot innerSlot : RegularitySlot grade) (cell : ℤ) :
    Summable (fun first : ℤ =>
      ‖slotCoordinate outer outerSlot first‖ *
        ‖slotCoordinate inner innerSlot (cell - first)‖) :=
  (slotConvolutionNorm_reindexed_summable outer inner outerSlot innerSlot).prod_factor cell

theorem slotWeightedCompositionTerm_norm_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) {dimension : ℕ}
    (outer inner : Coefficient L sigma gamma ell grade dimension dimension)
    (cell : ℤ) (slot : RegularitySlot grade)
    (physical : DerivativeSplit (slotDerivativeIndex slot)) :
    Summable (fun first : ℤ =>
      ‖slotWeightedCompositionTerm L sigma gamma ell grade outer inner cell first
        slot physical‖) := by
  apply Summable.of_nonneg_of_le
    (fun first => norm_nonneg
      (slotWeightedCompositionTerm L sigma gamma ell grade outer inner cell first
        slot physical))
    (fun first => slotWeightedCompositionTerm_norm_le admissible grade outer inner
      cell first slot physical)
  apply summable_sum
  intro moment _membership
  let split := combineSlotSplit physical moment
  simpa only [mul_assoc] using ((slotConvolutionNorm_fixed_summable outer inner
    (lowerRegularitySlot split) (upperRegularitySlot split) cell).mul_left
      (slotSplitMultiplicity split : ℝ))

theorem slotWeightedCompositionTerm_tsum_norm_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) {dimension : ℕ}
    (outer inner : Coefficient L sigma gamma ell grade dimension dimension)
    (cell : ℤ) (slot : RegularitySlot grade)
    (physical : DerivativeSplit (slotDerivativeIndex slot)) :
    ‖∑' first : ℤ,
        slotWeightedCompositionTerm L sigma gamma ell grade outer inner cell first
          slot physical‖ ≤
      ∑' first : ℤ,
        ‖slotWeightedCompositionTerm L sigma gamma ell grade outer inner cell first
          slot physical‖ := by
  let term : ℤ → ContinuousMap ClosedDisk (OperatorValue dimension dimension) :=
    fun first =>
      slotWeightedCompositionTerm L sigma gamma ell grade outer inner cell first
        slot physical
  have termNormSummable : Summable (fun first : ℤ => ‖term first‖) :=
    slotWeightedCompositionTerm_norm_summable admissible grade outer inner
      cell slot physical
  change ‖∑' first : ℤ, term first‖ ≤ ∑' first : ℤ, ‖term first‖
  exact @norm_tsum_le_tsum_norm ℤ
    (ContinuousMap ClosedDisk (OperatorValue dimension dimension)) _
      term termNormSummable

theorem slotCompositionCoordinate_eq {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) {dimension : ℕ}
    (outer inner : Coefficient L sigma gamma ell grade dimension dimension)
    (cell : ℤ) (slot : RegularitySlot grade) :
    slotCoordinate (coefficientComposition admissible grade outer inner) slot cell =
      ∑ physical : DerivativeSplit (slotDerivativeIndex slot),
        ∑' first : ℤ,
          slotWeightedCompositionTerm L sigma gamma ell grade outer inner cell first
            slot physical := by
  change ((scaledCellWeight L ell cell ^ slotGap slot : ℂ)⁻¹) •
      weightedCompositionCoordinate L sigma gamma ell grade outer.1 inner.1 cell
        (slotDerivativeIndex slot) = _
  unfold weightedCompositionCoordinate
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro physical _membership
  have termSummable := weightedCompositionTerm_summable admissible grade outer.1 inner.1
    cell (slotDerivativeIndex slot) physical
  rw [← Summable.tsum_const_smul
    (splitMultiplicity (slotDerivativeIndex slot) physical : ℂ) termSummable]
  rw [← Summable.tsum_const_smul
    ((scaledCellWeight L ell cell ^ slotGap slot : ℂ)⁻¹)
    (Summable.const_smul
      (splitMultiplicity (slotDerivativeIndex slot) physical : ℂ) termSummable)]
  apply tsum_congr
  intro first
  rfl

theorem slotCompositionCoordinate_norm_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) {dimension : ℕ}
    (outer inner : Coefficient L sigma gamma ell grade dimension dimension)
    (cell : ℤ) (slot : RegularitySlot grade) :
    ‖slotCoordinate (coefficientComposition admissible grade outer inner) slot cell‖ ≤
      slotCompositionCoordinateMajorant outer inner cell slot := by
  rw [slotCompositionCoordinate_eq admissible]
  calc
    ‖∑ physical : DerivativeSplit (slotDerivativeIndex slot),
        ∑' first : ℤ,
          slotWeightedCompositionTerm L sigma gamma ell grade outer inner cell first
            slot physical‖ ≤
      ∑ physical : DerivativeSplit (slotDerivativeIndex slot),
        ‖∑' first : ℤ,
          slotWeightedCompositionTerm L sigma gamma ell grade outer inner cell first
            slot physical‖ :=
      by
        simpa using
          norm_sum_le (Finset.univ :
            Finset (DerivativeSplit (slotDerivativeIndex slot)))
            (fun physical =>
              ∑' first : ℤ,
                slotWeightedCompositionTerm L sigma gamma ell grade outer inner
                  cell first slot physical)
    _ ≤ ∑ physical : DerivativeSplit (slotDerivativeIndex slot),
        ∑' first : ℤ,
          ‖slotWeightedCompositionTerm L sigma gamma ell grade outer inner cell first
            slot physical‖ := by
      apply Finset.sum_le_sum
      intro physical _membership
      exact slotWeightedCompositionTerm_tsum_norm_le admissible grade outer inner
        cell slot physical
    _ ≤ ∑ physical : DerivativeSplit (slotDerivativeIndex slot),
        ∑' first : ℤ,
          ∑ moment : Fin ((slot.moment : ℕ) + 1),
            let split := combineSlotSplit physical moment
            (slotSplitMultiplicity split : ℝ) *
              ‖slotCoordinate outer (lowerRegularitySlot split) first‖ *
              ‖slotCoordinate inner (upperRegularitySlot split) (cell - first)‖ := by
      apply Finset.sum_le_sum
      intro physical _membership
      exact Summable.tsum_le_tsum
        (fun first => slotWeightedCompositionTerm_norm_le admissible grade outer inner
          cell first slot physical)
        (slotWeightedCompositionTerm_norm_summable admissible grade outer inner
          cell slot physical)
        (by
          apply summable_sum
          intro moment _membership
          let split := combineSlotSplit physical moment
          simpa only [mul_assoc] using
            (slotConvolutionNorm_fixed_summable outer inner
              (lowerRegularitySlot split) (upperRegularitySlot split) cell).mul_left
                (slotSplitMultiplicity split : ℝ)
        )
    _ = slotCompositionCoordinateMajorant outer inner cell slot := by
      unfold slotCompositionCoordinateMajorant
      apply Finset.sum_congr rfl
      intro physical _membership
      rw [Summable.tsum_finsetSum]
      · apply Finset.sum_congr rfl
        intro moment _momentMembership
        let split := combineSlotSplit physical moment
        dsimp only
        simp only [mul_assoc]
        rw [tsum_mul_left]
      · intro moment _momentMembership
        let split := combineSlotSplit physical moment
        simpa only [mul_assoc] using
          (slotConvolutionNorm_fixed_summable outer inner
          (lowerRegularitySlot split) (upperRegularitySlot split) cell).mul_left
            (slotSplitMultiplicity split : ℝ)

theorem slotConvolutionNorm_total_eq {L sigma gamma ell : ℝ}
    {grade dimension : ℕ}
    (outer inner : Coefficient L sigma gamma ell grade dimension dimension)
    (outerSlot innerSlot : RegularitySlot grade) :
    (∑' cell : ℤ, ∑' first : ℤ,
      ‖slotCoordinate outer outerSlot first‖ *
        ‖slotCoordinate inner innerSlot (cell - first)‖) =
      slotNorm outer outerSlot * slotNorm inner innerSlot := by
  have outerSummable := slotCoordinate_norm_summable outer outerSlot
  have innerSummable := slotCoordinate_norm_summable inner innerSlot
  have pairSummable := outerSummable.mul_of_nonneg innerSummable
    (fun cell => norm_nonneg (slotCoordinate outer outerSlot cell))
    (fun cell => norm_nonneg (slotCoordinate inner innerSlot cell))
  have reindexed := slotConvolutionNorm_reindexed_summable outer inner
    outerSlot innerSlot
  calc
    (∑' cell : ℤ, ∑' first : ℤ,
        ‖slotCoordinate outer outerSlot first‖ *
          ‖slotCoordinate inner innerSlot (cell - first)‖) =
      ∑' pair : ℤ × ℤ,
        ‖slotCoordinate outer outerSlot pair.2‖ *
          ‖slotCoordinate inner innerSlot (pair.1 - pair.2)‖ :=
      reindexed.tsum_prod.symm
    _ = ∑' pair : ℤ × ℤ,
        ‖slotCoordinate outer outerSlot pair.1‖ *
          ‖slotCoordinate inner innerSlot pair.2‖ :=
      cellConvolutionEquiv.tsum_eq (fun pair : ℤ × ℤ =>
        ‖slotCoordinate outer outerSlot pair.1‖ *
          ‖slotCoordinate inner innerSlot pair.2‖)
    _ = slotNorm outer outerSlot * slotNorm inner innerSlot := by
      unfold slotNorm
      exact (outerSummable.tsum_mul_tsum innerSummable pairSummable).symm

def slotCompositionNormMajorant {L sigma gamma ell : ℝ}
    {grade dimension : ℕ}
    (outer inner : Coefficient L sigma gamma ell grade dimension dimension)
    (slot : RegularitySlot grade) : ℝ :=
  ∑ physical : DerivativeSplit (slotDerivativeIndex slot),
    ∑ moment : Fin ((slot.moment : ℕ) + 1),
      let split := combineSlotSplit physical moment
      (slotSplitMultiplicity split : ℝ) *
        slotNorm outer (lowerRegularitySlot split) *
          slotNorm inner (upperRegularitySlot split)

theorem slotCompositionCoordinateMajorant_summable {L sigma gamma ell : ℝ}
    {grade dimension : ℕ}
    (outer inner : Coefficient L sigma gamma ell grade dimension dimension)
    (slot : RegularitySlot grade) :
    Summable (fun cell : ℤ =>
      slotCompositionCoordinateMajorant outer inner cell slot) := by
  unfold slotCompositionCoordinateMajorant
  apply summable_sum
  intro physical _physicalMembership
  apply summable_sum
  intro moment _momentMembership
  let split := combineSlotSplit physical moment
  exact ((slotConvolutionNorm_reindexed_summable outer inner
    (lowerRegularitySlot split) (upperRegularitySlot split)).prod.mul_left
      (slotSplitMultiplicity split : ℝ))

theorem slotComposition_norm_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) {dimension : ℕ}
    (outer inner : Coefficient L sigma gamma ell grade dimension dimension)
    (slot : RegularitySlot grade) :
    slotNorm (coefficientComposition admissible grade outer inner) slot ≤
      slotCompositionNormMajorant outer inner slot := by
  unfold slotNorm
  calc
    (∑' cell : ℤ,
      ‖slotCoordinate (coefficientComposition admissible grade outer inner) slot cell‖) ≤
        ∑' cell : ℤ, slotCompositionCoordinateMajorant outer inner cell slot :=
      Summable.tsum_le_tsum
        (fun cell =>
          slotCompositionCoordinate_norm_le admissible grade outer inner cell slot)
        (slotCoordinate_norm_summable
          (coefficientComposition admissible grade outer inner) slot)
        (slotCompositionCoordinateMajorant_summable outer inner slot)
    _ = slotCompositionNormMajorant outer inner slot := by
      unfold slotCompositionCoordinateMajorant slotCompositionNormMajorant
      rw [Summable.tsum_finsetSum]
      · apply Finset.sum_congr rfl
        intro physical _physicalMembership
        rw [Summable.tsum_finsetSum]
        · apply Finset.sum_congr rfl
          intro moment _momentMembership
          let split := combineSlotSplit physical moment
          rw [tsum_mul_left, slotConvolutionNorm_total_eq]
          simp only [mul_assoc]
        · intro moment _momentMembership
          let split := combineSlotSplit physical moment
          exact ((slotConvolutionNorm_reindexed_summable outer inner
            (lowerRegularitySlot split) (upperRegularitySlot split)).prod.mul_left
              (slotSplitMultiplicity split : ℝ))
      · intro physical _physicalMembership
        apply summable_sum
        intro moment _momentMembership
        let split := combineSlotSplit physical moment
        exact ((slotConvolutionNorm_reindexed_summable outer inner
          (lowerRegularitySlot split) (upperRegularitySlot split)).prod.mul_left
            (slotSplitMultiplicity split : ℝ))

end Grad.GaugeCoefficients.Neumann.Regularity

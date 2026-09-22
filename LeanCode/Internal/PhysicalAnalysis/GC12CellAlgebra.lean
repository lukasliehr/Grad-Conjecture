import GC12SeriesEquation

noncomputable section

set_option maxHeartbeats 3000000

open Grad.GenericCarriers Grad.ClosedJets Grad.GaugeCoefficients.Envelope
open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Neumann.Regularity

open Grad.GaugeCoefficients.Algebra

def CellFieldSummable {dimension : ℕ} (field : CellField dimension) : Prop :=
  ∀ point : ClosedDisk, Summable (fun cell : ℤ => ‖field cell point‖)

theorem coefficientScale_one_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (cell : ℤ) (index : DerivativeIndex grade)
    (point : ClosedDisk) :
    1 ≤ coefficientScale L sigma gamma ell grade cell index point := by
  have pointMembership : point.val ∈
      Grad.GaugeCoefficients.Envelope.closedDisk := by
    simpa only [Grad.GaugeCoefficients.Envelope.closedDisk,
      Metric.mem_closedBall, dist_zero_right, closedUnitDisk, Set.mem_ofPred_eq]
      using point.property
  have envelopeOne : 1 ≤ originalEnvelope sigma gamma ell cell point.val :=
    (envelopeGoal L sigma gamma ell admissible cell point.val pointMembership).1
  have weightOne : 1 ≤ scaledCellWeight L ell cell ^
      (grade - derivativeOrder index) :=
    one_le_pow₀ (scaledCellWeight_one_le L ell cell)
  unfold coefficientScale
  nlinarith [mul_le_mul envelopeOne weightOne zero_le_one
    (by exact (Real.exp_pos _).le)]

theorem coefficientDerivative_point_norm_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    ‖coefficientDerivative coefficient cell index point‖ ≤
      ‖weightedDerivative coefficient cell index‖ := by
  have scaleOne := coefficientScale_one_le admissible grade cell index point
  have literal := weighted_derivative_literal grade inputDimension outputDimension
    coefficient cell index point
  calc
    ‖coefficientDerivative coefficient cell index point‖ =
        1 * ‖coefficientDerivative coefficient cell index point‖ := by rw [one_mul]
    _ ≤ coefficientScale L sigma gamma ell grade cell index point *
        ‖coefficientDerivative coefficient cell index point‖ :=
      mul_le_mul_of_nonneg_right scaleOne (norm_nonneg _)
    _ = ‖(coefficientScale L sigma gamma ell grade cell index point : ℂ) •
        coefficientDerivative coefficient cell index point‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (coefficientScale_pos L sigma gamma ell grade cell index point).le]
    _ = ‖weightedDerivative coefficient cell index point‖ := by
      rw [literal]
    _ ≤ ‖weightedDerivative coefficient cell index‖ :=
      ContinuousMap.norm_coe_le_norm _ point

theorem coefficientDerivative_point_norm_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (index : DerivativeIndex grade) (point : ClosedDisk) :
    Summable (fun cell : ℤ =>
      ‖coefficientDerivative coefficient cell index point‖) :=
  Summable.of_nonneg_of_le
    (fun _cell => norm_nonneg _)
    (fun cell => coefficientDerivative_point_norm_le admissible coefficient cell index point)
    (coordinate_norm_summable coefficient.1 index)

theorem gradedDerivativeCellField_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    {grade dimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade dimension dimension)
    (index : DerivativeIndex grade) :
    CellFieldSummable (gradedDerivativeCellField coefficient index) :=
  coefficientDerivative_point_norm_summable admissible coefficient index

theorem baseCellField_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (coefficient : BaseCoefficient L sigma gamma ell dimension) :
    CellFieldSummable (baseCellField coefficient) := by
  intro point
  exact coefficientValue_point_norm_summable admissible coefficient point

def identityCellField (dimension : ℕ) : CellField dimension :=
  fun cell _point =>
    if cell = 0 then ContinuousLinearMap.id ℂ (PhysicalValue dimension) else 0

theorem identityCellField_summable (dimension : ℕ) :
    CellFieldSummable (identityCellField dimension) := by
  intro point
  apply ((hasSum_ite_eq (0 : ℤ)
    ‖ContinuousLinearMap.id ℂ (PhysicalValue dimension)‖).summable).congr
  intro cell
  by_cases cellZero : cell = 0 <;> simp [identityCellField, cellZero]

theorem CellFieldSummable.add {dimension : ℕ} {first second : CellField dimension}
    (firstSummable : CellFieldSummable first)
    (secondSummable : CellFieldSummable second) :
    CellFieldSummable (first + second) := by
  intro point
  exact Summable.of_nonneg_of_le
    (fun cell => norm_nonneg ((first + second) cell point))
    (fun cell => norm_add_le (first cell point) (second cell point))
    ((firstSummable point).add (secondSummable point))

theorem CellFieldSummable.neg {dimension : ℕ} {field : CellField dimension}
    (summable : CellFieldSummable field) : CellFieldSummable (-field) := by
  intro point
  simpa only [Pi.neg_apply, norm_neg] using summable point

theorem CellFieldSummable.sub {dimension : ℕ} {first second : CellField dimension}
    (firstSummable : CellFieldSummable first)
    (secondSummable : CellFieldSummable second) :
    CellFieldSummable (first - second) := by
  rw [sub_eq_add_neg]
  exact firstSummable.add secondSummable.neg

theorem cellFieldComposition_fixed_norm_summable {dimension : ℕ}
    {outer inner : CellField dimension}
    (outerSummable : CellFieldSummable outer)
    (innerSummable : CellFieldSummable inner)
    (cell : ℤ) (point : ClosedDisk) :
    Summable (fun first : ℤ =>
      ‖(outer first point).comp (inner (cell - first) point)‖) := by
  have pairMajorant : Summable (fun pair : ℤ × ℤ =>
      ‖outer pair.1 point‖ * ‖inner pair.2 point‖) :=
    (outerSummable point).mul_of_nonneg (innerSummable point)
      (fun first => norm_nonneg _) (fun second => norm_nonneg _)
  have fixedMajorant : Summable (fun first : ℤ =>
      ‖outer first point‖ * ‖inner (cell - first) point‖) :=
    (cellConvolutionEquiv.summable_iff.mpr pairMajorant).prod_factor cell
  exact Summable.of_nonneg_of_le
    (fun first => norm_nonneg _)
    (fun first => ContinuousLinearMap.opNorm_comp_le _ _)
    fixedMajorant

theorem cellFieldComposition_fixed_summable {dimension : ℕ}
    {outer inner : CellField dimension}
    (outerSummable : CellFieldSummable outer)
    (innerSummable : CellFieldSummable inner)
    (cell : ℤ) (point : ClosedDisk) :
    Summable (fun first : ℤ =>
      (outer first point).comp (inner (cell - first) point)) :=
  (cellFieldComposition_fixed_norm_summable outerSummable innerSummable
    cell point).of_norm

theorem CellFieldSummable.composition {dimension : ℕ}
    {outer inner : CellField dimension}
    (outerSummable : CellFieldSummable outer)
    (innerSummable : CellFieldSummable inner) :
    CellFieldSummable (cellFieldComposition outer inner) := by
  intro point
  have pairMajorant : Summable (fun pair : ℤ × ℤ =>
      ‖outer pair.1 point‖ * ‖inner pair.2 point‖) :=
    (outerSummable point).mul_of_nonneg (innerSummable point)
      (fun first => norm_nonneg _) (fun second => norm_nonneg _)
  have reindexed := cellConvolutionEquiv.summable_iff.mpr pairMajorant
  apply Summable.of_nonneg_of_le
    (fun cell => norm_nonneg (cellFieldComposition outer inner cell point))
    (fun cell => ?_)
    reindexed.prod
  unfold cellFieldComposition
  have fixedNorm := cellFieldComposition_fixed_norm_summable
    outerSummable innerSummable cell point
  have fixedProduct := reindexed.prod_factor cell
  calc
    ‖∑' first : ℤ, (outer first point).comp (inner (cell - first) point)‖ ≤
        ∑' first : ℤ,
          ‖(outer first point).comp (inner (cell - first) point)‖ :=
      norm_tsum_le_tsum_norm fixedNorm
    _ ≤ ∑' first : ℤ,
        ‖outer first point‖ * ‖inner (cell - first) point‖ :=
      Summable.tsum_le_tsum (fun first =>
        ContinuousLinearMap.opNorm_comp_le _ _) fixedNorm fixedProduct

theorem cellFieldComposition_add_outer {dimension : ℕ}
    {first second inner : CellField dimension}
    (firstSummable : CellFieldSummable first)
    (secondSummable : CellFieldSummable second)
    (innerSummable : CellFieldSummable inner) :
    cellFieldComposition (first + second) inner =
      cellFieldComposition first inner + cellFieldComposition second inner := by
  funext cell point
  unfold cellFieldComposition
  simp only [Pi.add_apply, ContinuousLinearMap.add_comp]
  exact (cellFieldComposition_fixed_summable firstSummable innerSummable cell point).tsum_add
    (cellFieldComposition_fixed_summable secondSummable innerSummable cell point)

theorem cellFieldComposition_neg_outer {dimension : ℕ}
    {outer inner : CellField dimension}
    (_outerSummable : CellFieldSummable outer)
    (_innerSummable : CellFieldSummable inner) :
    cellFieldComposition (-outer) inner =
      -cellFieldComposition outer inner := by
  funext cell point
  unfold cellFieldComposition
  simp only [Pi.neg_apply, ContinuousLinearMap.neg_comp]
  rw [tsum_neg]

theorem cellFieldComposition_sub_outer {dimension : ℕ}
    {first second inner : CellField dimension}
    (firstSummable : CellFieldSummable first)
    (secondSummable : CellFieldSummable second)
    (innerSummable : CellFieldSummable inner) :
    cellFieldComposition (first - second) inner =
      cellFieldComposition first inner - cellFieldComposition second inner := by
  rw [sub_eq_add_neg, sub_eq_add_neg,
    cellFieldComposition_add_outer firstSummable secondSummable.neg innerSummable,
    cellFieldComposition_neg_outer secondSummable innerSummable]

theorem cellFieldComposition_identity_left {dimension : ℕ}
    {field : CellField dimension} (_summable : CellFieldSummable field) :
    cellFieldComposition (identityCellField dimension) field = field := by
  funext cell point
  unfold cellFieldComposition
  rw [tsum_eq_single 0]
  · simp [identityCellField]
  · intro first different
    simp [identityCellField, different]

theorem cellFieldComposition_identity_right {dimension : ℕ}
    {field : CellField dimension} (_summable : CellFieldSummable field) :
    cellFieldComposition field (identityCellField dimension) = field := by
  funext cell point
  unfold cellFieldComposition
  rw [tsum_eq_single cell]
  · simp [identityCellField]
  · intro first different
    have nonzero : cell - first ≠ 0 := by omega
    simp [identityCellField, nonzero]

def tripleCellConvolutionEquiv : (ℤ × (ℤ × ℤ)) ≃ ((ℤ × ℤ) × ℤ) where
  toFun pair := ((pair.2.1, pair.2.2), pair.1 - pair.2.1 - pair.2.2)
  invFun triple := (triple.1.1 + triple.1.2 + triple.2, triple.1)
  left_inv pair := by rcases pair with ⟨total, first, second⟩; ext <;> simp
  right_inv triple := by
    rcases triple with ⟨⟨first, second⟩, third⟩
    apply Prod.ext
    · rfl
    · dsimp
      omega

theorem cellFieldTriple_fixed_summable {dimension : ℕ}
    {first second third : CellField dimension}
    (firstSummable : CellFieldSummable first)
    (secondSummable : CellFieldSummable second)
    (thirdSummable : CellFieldSummable third)
    (cell : ℤ) (point : ClosedDisk) :
    Summable (fun pair : ℤ × ℤ =>
      ((first pair.1 point).comp (second pair.2 point)).comp
        (third (cell - pair.1 - pair.2) point)) := by
  have pairNorm : Summable (fun pair : ℤ × ℤ =>
      ‖first pair.1 point‖ * ‖second pair.2 point‖) :=
    (firstSummable point).mul_of_nonneg (secondSummable point)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have tripleNorm : Summable (fun triple : (ℤ × ℤ) × ℤ =>
      (‖first triple.1.1 point‖ * ‖second triple.1.2 point‖) *
        ‖third triple.2 point‖) :=
    pairNorm.mul_of_nonneg (thirdSummable point)
      (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun _ => norm_nonneg _)
  have fixedNorm :=
    (tripleCellConvolutionEquiv.summable_iff.mpr tripleNorm).prod_factor cell
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun pair => (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _)
        (norm_nonneg _))) fixedNorm

theorem cellFieldComposition_associative {dimension : ℕ}
    {first second third : CellField dimension}
    (firstSummable : CellFieldSummable first)
    (secondSummable : CellFieldSummable second)
    (thirdSummable : CellFieldSummable third) :
    cellFieldComposition (cellFieldComposition first second) third =
      cellFieldComposition first (cellFieldComposition second third) := by
  funext cell point
  unfold cellFieldComposition
  let composition := ContinuousLinearMap.compL ℂ
    (PhysicalValue dimension) (PhysicalValue dimension) (PhysicalValue dimension)
  have normalizedSummable := cellFieldTriple_fixed_summable firstSummable
    secondSummable thirdSummable cell point
  have leftPairSummable : Summable (fun pair : ℤ × ℤ =>
      ((first pair.2 point).comp (second (pair.1 - pair.2) point)).comp
        (third (cell - pair.1) point)) := by
    apply (cellConvolutionEquiv.summable_iff.mpr normalizedSummable).congr
    intro pair
    apply ContinuousLinearMap.ext
    intro value
    dsimp [cellConvolutionEquiv]
    rw [show cell - pair.2 - (pair.1 - pair.2) = cell - pair.1 by omega]
  have rightPairSummable : Summable (fun pair : ℤ × ℤ =>
      (first pair.1 point).comp
        ((second pair.2 point).comp (third (cell - pair.1 - pair.2) point))) := by
    exact normalizedSummable.congr fun pair => by
      apply ContinuousLinearMap.ext
      intro value
      rfl
  calc
    (∑' outerCell : ℤ,
        (∑' middleCell : ℤ,
          (first middleCell point).comp
            (second (outerCell - middleCell) point)).comp
          (third (cell - outerCell) point)) =
      ∑' outerCell : ℤ, ∑' middleCell : ℤ,
        ((first middleCell point).comp
          (second (outerCell - middleCell) point)).comp
            (third (cell - outerCell) point) := by
      apply tsum_congr
      intro outerCell
      let composeRight :=
        (ContinuousLinearMap.apply ℂ (OperatorValue dimension dimension)
          (third (cell - outerCell) point)).comp composition
      change composeRight (∑' middleCell : ℤ,
          (first middleCell point).comp
            (second (outerCell - middleCell) point)) =
        ∑' middleCell : ℤ, composeRight
          ((first middleCell point).comp
            (second (outerCell - middleCell) point))
      rw [composeRight.map_tsum
        (cellFieldComposition_fixed_summable firstSummable secondSummable
          outerCell point)]
    _ = ∑' pair : ℤ × ℤ,
        ((first pair.2 point).comp (second (pair.1 - pair.2) point)).comp
          (third (cell - pair.1) point) := leftPairSummable.tsum_prod.symm
    _ = ∑' pair : ℤ × ℤ,
        ((first pair.1 point).comp (second pair.2 point)).comp
          (third (cell - pair.1 - pair.2) point) := by
      let term := fun pair : ℤ × ℤ =>
        ((first pair.1 point).comp (second pair.2 point)).comp
          (third (cell - pair.1 - pair.2) point)
      calc
        _ = ∑' pair : ℤ × ℤ, term (cellConvolutionEquiv pair) := by
          apply tsum_congr
          intro pair
          apply ContinuousLinearMap.ext
          intro value
          dsimp [term, cellConvolutionEquiv]
          rw [show cell - pair.2 - (pair.1 - pair.2) = cell - pair.1 by omega]
        _ = ∑' pair : ℤ × ℤ, term pair :=
          cellConvolutionEquiv.tsum_eq term
    _ = ∑' pair : ℤ × ℤ,
        (first pair.1 point).comp
          ((second pair.2 point).comp
            (third (cell - pair.1 - pair.2) point)) := by
      apply tsum_congr
      intro pair
      apply ContinuousLinearMap.ext
      intro value
      rfl
    _ = ∑' outerCell : ℤ, ∑' middleCell : ℤ,
        (first outerCell point).comp
          ((second middleCell point).comp
            (third (cell - outerCell - middleCell) point)) :=
      rightPairSummable.tsum_prod
    _ = ∑' outerCell : ℤ,
        (first outerCell point).comp
          (∑' middleCell : ℤ,
            (second middleCell point).comp
              (third ((cell - outerCell) - middleCell) point)) := by
      apply tsum_congr
      intro outerCell
      let composeLeft := composition (first outerCell point)
      change (∑' middleCell : ℤ, composeLeft
          ((second middleCell point).comp
            (third (cell - outerCell - middleCell) point))) =
        composeLeft (∑' middleCell : ℤ,
          (second middleCell point).comp
            (third (cell - outerCell - middleCell) point))
      exact (composeLeft.map_tsum
        (cellFieldComposition_fixed_summable secondSummable thirdSummable
          (cell - outerCell) point)).symm

end Grad.GaugeCoefficients.Neumann.Regularity

import GC10Norm

noncomputable section

set_option maxHeartbeats 3000000

open Set
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets
open Grad.GaugeCoefficients.Envelope
open scoped BigOperators ContDiff ENNReal Topology

namespace Grad.GaugeCoefficients.Algebra

def zeroDerivativeSplit : DerivativeSplit zeroDerivativeIndex :=
  (⟨0, by norm_num [zeroDerivativeIndex]⟩,
    ⟨0, by norm_num [zeroDerivativeIndex]⟩)

theorem derivativeSplit_zero_eq (split : DerivativeSplit zeroDerivativeIndex) :
    split = zeroDerivativeSplit := by
  apply Prod.ext
  · apply Fin.ext
    omega
  · apply Fin.ext
    omega

theorem derivativeSplit_zero_univ :
    (Finset.univ : Finset (DerivativeSplit zeroDerivativeIndex)) =
      {zeroDerivativeSplit} := by
  ext split
  simp only [Finset.mem_univ, Finset.mem_singleton]
  exact ⟨fun _ => derivativeSplit_zero_eq split, fun _ => trivial⟩

@[simp]
theorem lowerDerivativeIndex_zero :
    lowerDerivativeIndex zeroDerivativeIndex zeroDerivativeSplit = zeroDerivativeIndex := by
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> rfl

@[simp]
theorem upperDerivativeIndex_zero :
    upperDerivativeIndex zeroDerivativeIndex zeroDerivativeSplit = zeroDerivativeIndex := by
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> rfl

@[simp]
theorem splitMultiplicity_zero :
    splitMultiplicity zeroDerivativeIndex zeroDerivativeSplit = 1 := by
  norm_num [splitMultiplicity, zeroDerivativeSplit, zeroDerivativeIndex]

theorem coefficientComposition_value {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : Coefficient L sigma gamma ell 0 middleDimension outputDimension)
    (inner : Coefficient L sigma gamma ell 0 inputDimension middleDimension)
    (cell : ℤ) (point : ClosedDisk) :
    coefficientValue (coefficientComposition admissible 0 outer inner) cell point =
      ∑' first : ℤ,
        (coefficientValue outer first point).comp
          (coefficientValue inner (cell - first) point) := by
  change coefficientDerivative (coefficientComposition admissible 0 outer inner)
      cell zeroDerivativeIndex point = _
  rw [coefficientComposition_derivative]
  unfold formalCompositionDerivative
  apply tsum_congr
  intro first
  rw [derivativeSplit_zero_univ]
  simp only [Finset.sum_singleton, splitMultiplicity_zero, Nat.cast_one, one_smul,
    lowerDerivativeIndex_zero, upperDerivativeIndex_zero]
  rfl

theorem coefficientScale_zero_one_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (cell : ℤ) (point : ClosedDisk) :
    1 ≤ coefficientScale L sigma gamma ell 0 cell zeroDerivativeIndex point := by
  have pointMembership : point.val ∈ Grad.GaugeCoefficients.Envelope.closedDisk := by
    simpa only [closedDisk, Metric.mem_closedBall, dist_zero_right, closedUnitDisk,
      Set.mem_ofPred_eq] using
      point.property
  simpa only [coefficientScale, derivativeOrder, zeroDerivativeIndex, Nat.zero_sub,
    pow_zero, mul_one] using
      (envelopeGoal L sigma gamma ell admissible cell point.val pointMembership).1

theorem coefficientValue_point_norm_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell 0 inputDimension outputDimension)
    (cell : ℤ) (point : ClosedDisk) :
    ‖coefficientValue coefficient cell point‖ ≤
      ‖weightedDerivative coefficient cell zeroDerivativeIndex‖ := by
  have scaleOne : 1 ≤ coefficientScale L sigma gamma ell 0 cell zeroDerivativeIndex point :=
    coefficientScale_zero_one_le admissible cell point
  have literal := weighted_derivative_literal 0 inputDimension outputDimension
    coefficient cell zeroDerivativeIndex point
  calc
    ‖coefficientValue coefficient cell point‖ =
        1 * ‖coefficientValue coefficient cell point‖ := by rw [one_mul]
    _ ≤ coefficientScale L sigma gamma ell 0 cell zeroDerivativeIndex point *
        ‖coefficientValue coefficient cell point‖ :=
      mul_le_mul_of_nonneg_right scaleOne (norm_nonneg _)
    _ = ‖(coefficientScale L sigma gamma ell 0 cell zeroDerivativeIndex point : ℂ) •
        coefficientValue coefficient cell point‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg
          (coefficientScale_pos L sigma gamma ell 0 cell zeroDerivativeIndex point).le]
    _ = ‖weightedDerivative coefficient cell zeroDerivativeIndex point‖ := by
      simpa only [coefficientValue] using (congrArg norm literal).symm
    _ ≤ ‖weightedDerivative coefficient cell zeroDerivativeIndex‖ :=
      ContinuousMap.norm_coe_le_norm _ point

theorem coefficientValue_point_norm_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell 0 inputDimension outputDimension)
    (point : ClosedDisk) :
    Summable (fun cell : ℤ => ‖coefficientValue coefficient cell point‖) :=
  Summable.of_nonneg_of_le
    (fun cell => norm_nonneg (coefficientValue coefficient cell point))
    (fun cell => coefficientValue_point_norm_le admissible coefficient cell point)
    (coordinate_norm_summable coefficient.1 zeroDerivativeIndex)

def fourierPhase (cell : ℤ) (angle : ℝ) : ℂ :=
  Complex.exp (Complex.I * (cell : ℂ) * angle)

theorem fourierPhase_norm (cell : ℤ) (angle : ℝ) :
    ‖fourierPhase cell angle‖ = 1 := by
  unfold fourierPhase
  rw [Complex.norm_exp]
  norm_num

theorem fourierPhase_add (first second : ℤ) (angle : ℝ) :
    fourierPhase (first + second) angle =
      fourierPhase first angle * fourierPhase second angle := by
  unfold fourierPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem fourierTerm_norm_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell 0 inputDimension outputDimension)
    (angle : ℝ) (point : ClosedDisk) :
    Summable (fun cell : ℤ =>
      ‖fourierPhase cell angle • coefficientValue coefficient cell point‖) := by
  simpa only [norm_smul, fourierPhase_norm, one_mul] using
    coefficientValue_point_norm_summable admissible coefficient point

theorem fourierTerm_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell 0 inputDimension outputDimension)
    (angle : ℝ) (point : ClosedDisk) :
    Summable (fun cell : ℤ =>
      fourierPhase cell angle • coefficientValue coefficient cell point) :=
  (fourierTerm_norm_summable admissible coefficient angle point).of_norm

theorem fourierPhase_comp
    {inputDimension middleDimension outputDimension : ℕ}
    (first second : ℤ) (angle : ℝ)
    (outer : OperatorValue middleDimension outputDimension)
    (inner : OperatorValue inputDimension middleDimension) :
    fourierPhase (first + second) angle • outer.comp inner =
      (fourierPhase first angle • outer).comp
        (fourierPhase second angle • inner) := by
  rw [fourierPhase_add]
  apply ContinuousLinearMap.ext
  intro value
  simp only [smul_apply, ContinuousLinearMap.comp_apply, map_smul, smul_smul]
  rw [mul_comm]

theorem coefficientValueComposition_fixed_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : Coefficient L sigma gamma ell 0 middleDimension outputDimension)
    (inner : Coefficient L sigma gamma ell 0 inputDimension middleDimension)
    (cell : ℤ) (point : ClosedDisk) :
    Summable (fun first : ℤ =>
      (coefficientValue outer first point).comp
        (coefficientValue inner (cell - first) point)) := by
  have outerNorm := coefficientValue_point_norm_summable admissible outer point
  have innerNorm := coefficientValue_point_norm_summable admissible inner point
  have pairMajorant : Summable (fun pair : ℤ × ℤ =>
      ‖coefficientValue outer pair.1 point‖ *
        ‖coefficientValue inner pair.2 point‖) :=
    outerNorm.mul_of_nonneg innerNorm
      (fun first => norm_nonneg (coefficientValue outer first point))
      (fun second => norm_nonneg (coefficientValue inner second point))
  have fixedMajorant : Summable (fun first : ℤ =>
      ‖coefficientValue outer first point‖ *
        ‖coefficientValue inner (cell - first) point‖) :=
    (cellConvolutionEquiv.summable_iff.mpr pairMajorant).prod_factor cell
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le
    (fun first => norm_nonneg
      ((coefficientValue outer first point).comp
        (coefficientValue inner (cell - first) point)))
    (fun first => ContinuousLinearMap.opNorm_comp_le _ _)
    fixedMajorant

theorem fourierPairTerm_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : Coefficient L sigma gamma ell 0 middleDimension outputDimension)
    (inner : Coefficient L sigma gamma ell 0 inputDimension middleDimension)
    (angle : ℝ) (point : ClosedDisk) :
    Summable (fun pair : ℤ × ℤ =>
      (fourierPhase pair.1 angle • coefficientValue outer pair.1 point).comp
        (fourierPhase pair.2 angle • coefficientValue inner pair.2 point)) := by
  have outerNorm := fourierTerm_norm_summable admissible outer angle point
  have innerNorm := fourierTerm_norm_summable admissible inner angle point
  have pairMajorant : Summable (fun pair : ℤ × ℤ =>
      ‖fourierPhase pair.1 angle • coefficientValue outer pair.1 point‖ *
        ‖fourierPhase pair.2 angle • coefficientValue inner pair.2 point‖) :=
    outerNorm.mul_of_nonneg innerNorm
      (fun first => norm_nonneg
        (fourierPhase first angle • coefficientValue outer first point))
      (fun second => norm_nonneg
        (fourierPhase second angle • coefficientValue inner second point))
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le
    (fun pair => norm_nonneg
      ((fourierPhase pair.1 angle • coefficientValue outer pair.1 point).comp
        (fourierPhase pair.2 angle • coefficientValue inner pair.2 point)))
    (fun pair => ContinuousLinearMap.opNorm_comp_le _ _)
    pairMajorant

theorem fourierConvolutionPair_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : Coefficient L sigma gamma ell 0 middleDimension outputDimension)
    (inner : Coefficient L sigma gamma ell 0 inputDimension middleDimension)
    (angle : ℝ) (point : ClosedDisk) :
    Summable (fun pair : ℤ × ℤ =>
      fourierPhase pair.1 angle •
        (coefficientValue outer pair.2 point).comp
          (coefficientValue inner (pair.1 - pair.2) point)) := by
  have reindexed := cellConvolutionEquiv.summable_iff.mpr
    (fourierPairTerm_summable admissible outer inner angle point)
  apply reindexed.congr
  intro pair
  change (fourierPhase pair.2 angle • coefficientValue outer pair.2 point).comp
      (fourierPhase (pair.1 - pair.2) angle •
        coefficientValue inner (pair.1 - pair.2) point) = _
  rw [← fourierPhase_comp]
  rw [show pair.2 + (pair.1 - pair.2) = pair.1 by omega]

theorem fourierComposition {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : Coefficient L sigma gamma ell 0 middleDimension outputDimension)
    (inner : Coefficient L sigma gamma ell 0 inputDimension middleDimension)
    (angle : ℝ) (point : ClosedDisk) :
    fourierEvaluation (coefficientComposition admissible 0 outer inner) angle point =
      (fourierEvaluation outer angle point).comp
        (fourierEvaluation inner angle point) := by
  change (∑' cell : ℤ, fourierPhase cell angle •
      coefficientValue (coefficientComposition admissible 0 outer inner) cell point) =
    (∑' first : ℤ, fourierPhase first angle • coefficientValue outer first point).comp
      (∑' second : ℤ, fourierPhase second angle • coefficientValue inner second point)
  simp_rw [coefficientComposition_value admissible outer inner]
  have pairSummable := fourierPairTerm_summable admissible outer inner angle point
  have reindexedSummable :=
    fourierConvolutionPair_summable admissible outer inner angle point
  calc
    (∑' cell : ℤ, fourierPhase cell angle •
        ∑' first : ℤ, (coefficientValue outer first point).comp
          (coefficientValue inner (cell - first) point)) =
      ∑' cell : ℤ, ∑' first : ℤ, fourierPhase cell angle •
        (coefficientValue outer first point).comp
          (coefficientValue inner (cell - first) point) := by
        apply tsum_congr
        intro cell
        rw [Summable.tsum_const_smul
          (fourierPhase cell angle)
          (coefficientValueComposition_fixed_summable
            admissible outer inner cell point)]
    _ = ∑' pair : ℤ × ℤ, fourierPhase pair.1 angle •
          (coefficientValue outer pair.2 point).comp
            (coefficientValue inner (pair.1 - pair.2) point) :=
      reindexedSummable.tsum_prod.symm
    _ = ∑' pair : ℤ × ℤ,
          (fourierPhase pair.2 angle • coefficientValue outer pair.2 point).comp
            (fourierPhase (pair.1 - pair.2) angle •
              coefficientValue inner (pair.1 - pair.2) point) := by
      apply tsum_congr
      intro pair
      rw [← fourierPhase_comp]
      rw [show pair.2 + (pair.1 - pair.2) = pair.1 by omega]
    _ = ∑' pair : ℤ × ℤ,
          (fourierPhase pair.1 angle • coefficientValue outer pair.1 point).comp
            (fourierPhase pair.2 angle • coefficientValue inner pair.2 point) :=
      by
        change (∑' pair : ℤ × ℤ,
          (fourierPhase (cellConvolutionEquiv pair).1 angle •
            coefficientValue outer (cellConvolutionEquiv pair).1 point).comp
              (fourierPhase (cellConvolutionEquiv pair).2 angle •
                coefficientValue inner (cellConvolutionEquiv pair).2 point)) = _
        exact cellConvolutionEquiv.tsum_eq
          (fun pair : ℤ × ℤ =>
            (fourierPhase pair.1 angle • coefficientValue outer pair.1 point).comp
              (fourierPhase pair.2 angle • coefficientValue inner pair.2 point))
    _ = ∑' first : ℤ, ∑' second : ℤ,
          (fourierPhase first angle • coefficientValue outer first point).comp
            (fourierPhase second angle • coefficientValue inner second point) :=
      pairSummable.tsum_prod
    _ = (∑' first : ℤ,
          fourierPhase first angle • coefficientValue outer first point).comp
        (∑' second : ℤ,
          fourierPhase second angle • coefficientValue inner second point) := by
      let composition := ContinuousLinearMap.compL ℂ
        (PhysicalValue inputDimension) (PhysicalValue middleDimension)
          (PhysicalValue outputDimension)
      have outerSummable := fourierTerm_summable admissible outer angle point
      have innerSummable := fourierTerm_summable admissible inner angle point
      have mappedOuterSummable : Summable (fun first : ℤ =>
          composition (fourierPhase first angle • coefficientValue outer first point)) :=
        (composition.hasSum outerSummable.hasSum).summable
      have innerTsum (first : ℤ) :
          (∑' second : ℤ,
            (fourierPhase first angle • coefficientValue outer first point).comp
              (fourierPhase second angle • coefficientValue inner second point)) =
          composition (fourierPhase first angle • coefficientValue outer first point)
            (∑' second : ℤ,
              fourierPhase second angle • coefficientValue inner second point) := by
        rw [(composition
          (fourierPhase first angle • coefficientValue outer first point)).map_tsum
            innerSummable]
        apply tsum_congr
        intro second
        rw [ContinuousLinearMap.compL_apply]
      simp_rw [innerTsum]
      change (∑' first : ℤ,
          (ContinuousLinearMap.apply ℂ
            (OperatorValue inputDimension outputDimension)
            (∑' second : ℤ,
              fourierPhase second angle • coefficientValue inner second point))
            (composition
              (fourierPhase first angle • coefficientValue outer first point))) = _
      rw [← (ContinuousLinearMap.apply ℂ
        (OperatorValue inputDimension outputDimension)
        (∑' second : ℤ,
          fourierPhase second angle • coefficientValue inner second point)).map_tsum
            mappedOuterSummable]
      rw [← composition.map_tsum outerSummable]
      change composition
          (∑' first : ℤ,
            fourierPhase first angle • coefficientValue outer first point)
          (∑' second : ℤ,
            fourierPhase second angle • coefficientValue inner second point) = _
      exact ContinuousLinearMap.compL_apply ℂ
        (PhysicalValue inputDimension) (PhysicalValue middleDimension)
          (PhysicalValue outputDimension) _ _

end Grad.GaugeCoefficients.Algebra

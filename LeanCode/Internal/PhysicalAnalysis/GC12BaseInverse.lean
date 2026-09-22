import GC12PowerNorm

noncomputable section

set_option maxHeartbeats 3000000

open Grad.ClosedJets Grad.GaugeCoefficients.Envelope
open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Neumann.Regularity

open Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Neumann

def weightedDerivativeCLM (L sigma gamma ell : ℝ)
    (grade inputDimension outputDimension : ℕ) (cell : ℤ)
    (index : DerivativeIndex grade) :
    Coefficient L sigma gamma ell grade inputDimension outputDimension →L[ℂ]
      ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) :=
  LinearMap.mkContinuous
    { toFun := fun coefficient => weightedDerivative coefficient cell index
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun coefficient => by
      change ‖coefficient.1 (cell, index)‖ ≤ 1 * ‖coefficient.1‖
      rw [one_mul]
      exact lp.norm_apply_le_norm (p := 1) (by norm_num) coefficient.1
        (cell, index))

@[simp] theorem weightedDerivativeCLM_apply {L sigma gamma ell : ℝ}
    {grade inputDimension outputDimension : ℕ} (cell : ℤ)
    (index : DerivativeIndex grade)
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension) :
    weightedDerivativeCLM L sigma gamma ell grade inputDimension outputDimension
      cell index coefficient = weightedDerivative coefficient cell index := rfl

def slotCoordinateCLM (L sigma gamma ell : ℝ)
    (grade inputDimension outputDimension : ℕ) (cell : ℤ)
    (slot : RegularitySlot grade) :
    Coefficient L sigma gamma ell grade inputDimension outputDimension →L[ℂ]
      ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) :=
  LinearMap.mkContinuous
    { toFun := fun coefficient => slotCoordinate coefficient slot cell
      map_add' := fun first second => by
        simp [slotCoordinate, weightedDerivative, smul_add]
      map_smul' := fun scalar coefficient => by
        simp [slotCoordinate, weightedDerivative, smul_smul, mul_comm] }
    1 (fun coefficient => by
      rw [one_mul]
      exact (slotCoordinate_norm_le coefficient slot cell).trans
        (lp.norm_apply_le_norm (p := 1) (by norm_num) coefficient.1
          (cell, slotDerivativeIndex slot)))

@[simp] theorem slotCoordinateCLM_apply {L sigma gamma ell : ℝ}
    {grade inputDimension outputDimension : ℕ} (cell : ℤ)
    (slot : RegularitySlot grade)
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension) :
    slotCoordinateCLM L sigma gamma ell grade inputDimension outputDimension
      cell slot coefficient = slotCoordinate coefficient slot cell := rfl

theorem realizesSameCoefficient_of_zeroSlotCoordinate
    {L sigma gamma ell : ℝ} {grade dimension : ℕ}
    {base : BaseCoefficient L sigma gamma ell dimension}
    {graded : Coefficient L sigma gamma ell grade dimension dimension}
    (coordinateEquality : ∀ cell : ℤ,
      slotCoordinate graded (zeroRegularitySlot grade) cell =
        weightedDerivative base cell zeroDerivativeIndex) :
    RealizesSameCoefficient base graded := by
  intro cell point
  have equalityAtPoint := congrArg (fun function :
      ContinuousMap ClosedDisk (OperatorValue dimension dimension) => function point)
    (coordinateEquality cell)
  rw [slotCoordinate_apply] at equalityAtPoint
  rw [weighted_derivative_literal 0 dimension dimension base cell
    zeroDerivativeIndex point] at equalityAtPoint
  simp only [zeroRegularitySlot, pow_zero, mul_one] at equalityAtPoint
  unfold coefficientScale at equalityAtPoint
  simp only [derivativeOrder, zeroDerivativeIndex, Nat.zero_sub,
    pow_zero, mul_one] at equalityAtPoint
  let scalar : ℂ := originalEnvelope sigma gamma ell cell point.val
  have scalarNonzero : scalar ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  calc
    coefficientDerivative graded cell (zeroDerivativeIndexAt grade) point =
        scalar⁻¹ • (scalar •
          coefficientDerivative graded cell (zeroDerivativeIndexAt grade) point) := by
      simp [scalar, scalarNonzero]
    _ = scalar⁻¹ • (scalar • coefficientValue base cell point) := by
      exact congrArg (fun value : OperatorValue dimension dimension => scalar⁻¹ • value)
        equalityAtPoint
    _ = coefficientValue base cell point := by
      simp [scalarNonzero]

theorem gradedCoefficientNeumannInverse_zeroSlotCoordinate
    {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (positive : 0 < dimension)
    (baseCoefficient : BaseCoefficient L sigma gamma ell dimension)
    (gradedCoefficient : Coefficient L sigma gamma ell grade dimension dimension)
    (theta : ℝ)
    (realizes : RealizesSameCoefficient baseCoefficient gradedCoefficient)
    (normBound : ‖baseCoefficient‖ ≤ theta) (thetaLt : theta < 1)
    (cell : ℤ) :
    slotCoordinate
        (gradedCoefficientNeumannInverse admissible gradedCoefficient)
        (zeroRegularitySlot grade) cell =
      weightedDerivative
        (analyticCapCoefficientNeumannInverse admissible baseCoefficient)
        cell zeroDerivativeIndex := by
  have gradedSummable := gradedCoefficientPower_summable admissible positive
    baseCoefficient gradedCoefficient theta realizes normBound thetaLt
  have baseSummable := coefficientPower_summable admissible positive
    baseCoefficient theta normBound thetaLt
  calc
    slotCoordinate
        (gradedCoefficientNeumannInverse admissible gradedCoefficient)
        (zeroRegularitySlot grade) cell =
      ∑' power : ℕ,
        slotCoordinate (gradedCoefficientPower admissible gradedCoefficient power)
          (zeroRegularitySlot grade) cell := by
      unfold gradedCoefficientNeumannInverse
      simpa only [slotCoordinateCLM_apply] using
        (slotCoordinateCLM L sigma gamma ell grade dimension dimension cell
          (zeroRegularitySlot grade)).map_tsum gradedSummable
    _ = ∑' power : ℕ,
        weightedDerivative (coefficientPower admissible baseCoefficient power)
          cell zeroDerivativeIndex := by
      apply tsum_congr
      intro power
      exact zeroSlotCoordinate_eq_baseWeightedDerivative
        (gradedCoefficientPower_realizes admissible baseCoefficient gradedCoefficient
          realizes power) cell
    _ = weightedDerivative
        (analyticCapCoefficientNeumannInverse admissible baseCoefficient)
        cell zeroDerivativeIndex := by
      unfold analyticCapCoefficientNeumannInverse coefficientNeumannInverse
      symm
      exact (weightedDerivativeCLM L sigma gamma ell 0 dimension dimension cell
        zeroDerivativeIndex).map_tsum baseSummable

theorem gradedCoefficientNeumannInverse_realizes
    {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (positive : 0 < dimension)
    (baseCoefficient : BaseCoefficient L sigma gamma ell dimension)
    (gradedCoefficient : Coefficient L sigma gamma ell grade dimension dimension)
    (theta : ℝ)
    (realizes : RealizesSameCoefficient baseCoefficient gradedCoefficient)
    (normBound : ‖baseCoefficient‖ ≤ theta) (thetaLt : theta < 1) :
    RealizesSameCoefficient
      (analyticCapCoefficientNeumannInverse admissible baseCoefficient)
      (gradedCoefficientNeumannInverse admissible gradedCoefficient) :=
  realizesSameCoefficient_of_zeroSlotCoordinate
    (gradedCoefficientNeumannInverse_zeroSlotCoordinate admissible positive
      baseCoefficient gradedCoefficient theta realizes normBound thetaLt)

end Grad.GaugeCoefficients.Neumann.Regularity

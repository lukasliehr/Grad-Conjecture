import SeedInverseCoefficient

noncomputable section

namespace Grad.Constraints.Seed

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.Frame

theorem inverseDeterminant_difference_bound {eccentricity rho : ℝ}
    (nonnegative : 0 ≤ eccentricity) (small : eccentricity < 1) (rhoBound : |rho| ≤ eccentricity) :
    |inverseDeterminant rho - 1| ≤ inverseDeterminant eccentricity * |rho| := by
  have determinantBound := determinant_inverse_bound nonnegative small rhoBound
  have rhoSmall : |rho| ≤ 1 := rhoBound.trans small.le
  have squareBound : rho ^ 2 ≤ |rho| := by
    have bound := mul_le_mul_of_nonneg_left rhoSmall (abs_nonneg rho)
    simpa only [← sq, sq_abs, mul_one] using bound
  have positive : 0 < 1 - rho ^ 2 := by
    have range := abs_lt.mp (rhoBound.trans_lt small)
    nlinarith
  have rootBound := seed_sqrt_difference_bound (argument := -(rho ^ 2)) (by linarith)
  simp only [← sub_eq_add_neg, abs_neg, abs_of_nonneg (sq_nonneg rho)] at rootBound
  have difference : inverseDeterminant rho - 1 =
      -(Real.sqrt (1 - rho ^ 2) - 1) * inverseDeterminant rho := by
    unfold inverseDeterminant
    field_simp [determinantBound.1.ne']
    ring
  rw [difference, abs_mul, abs_neg, abs_of_pos
    (show 0 < inverseDeterminant rho from inv_pos.mpr determinantBound.1)]
  exact (mul_le_mul (rootBound.trans squareBound) determinantBound.2
    (inv_nonneg.mpr determinantBound.1.le) (abs_nonneg rho)).trans_eq (mul_comm _ _)

def inverseDeviationConstant (phase : PhaseParameters) (grade : ℕ) (eccentricity radius : ℝ) : ℝ :=
  inverseDeterminant eccentricity *
    (seedDeviationConstant phase.sigma0 radius grade + (Fintype.card (DerivativeIndex grade) : ℝ))

theorem inverseDeviation_norm_bound (phase : PhaseParameters) (grade : ℕ)
    {eccentricity radius : ℝ} (nonnegative : 0 ≤ eccentricity) (small : eccentricity < 1)
    (radiusNonnegative : 0 ≤ radius) (parameter : Parameters)
    (rhoBound : |parameter 0| ≤ eccentricity) (otherSmall : ∀ index : Fin 3, |parameter index.succ| ≤ radius) :
    ‖inverseDeviationCoefficient phase grade parameter‖ ≤
      inverseDeviationConstant phase grade eccentricity radius * |parameter 0| := by
  have determinantBound := determinant_inverse_bound nonnegative small rhoBound
  have scalarBound : ‖(inverseDeterminant (parameter 0) : ℂ)‖ ≤ inverseDeterminant eccentricity := by
    rw [Complex.norm_real, Real.norm_of_nonneg
      (show 0 ≤ inverseDeterminant (parameter 0) from inv_nonneg.mpr determinantBound.1.le)]
    exact determinantBound.2
  have reflectedBound := seedMatrixDeviation_norm_le (seedAdmissible phase) grade radiusNonnegative
    (show |-(parameter 0)| ≤ 1 by rw [abs_neg]; exact rhoBound.trans small.le)
    (otherSmall 0) (otherSmall 1) (otherSmall 2)
  have firstBound := (coefficientScalarNorm_le (inverseDeterminant (parameter 0) : ℂ)
    (seedMatrixDeviationCoefficient (seedAdmissible phase) grade (-(parameter 0))
      (parameter 1) (parameter 2) (parameter 3))).trans
    (mul_le_mul scalarBound reflectedBound (norm_nonneg _)
      (inv_nonneg.mpr (Real.sqrt_nonneg _)))
  simp only [abs_neg] at firstBound
  have constantBound :
      ‖(((inverseDeterminant (parameter 0) - 1 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (ComplexEuclidean 2))‖ ≤
        inverseDeterminant eccentricity * |parameter 0| := by
    apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
    apply (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)).trans
    rw [mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact inverseDeterminant_difference_bound nonnegative small rhoBound
  have secondBound := (seedZeroCell_norm_le (seedAdmissible phase) (grade := grade)
    (((inverseDeterminant (parameter 0) - 1 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (ComplexEuclidean 2))).trans
    (mul_le_mul_of_nonneg_left constantBound (Nat.cast_nonneg _))
  unfold inverseDeviationCoefficient
  exact ((norm_add_le _ _).trans (add_le_add firstBound secondBound)).trans_eq (by
    unfold inverseDeviationConstant
    ring)

theorem actual_inverse_bound (phase : PhaseParameters) (grade : ℕ)
    {eccentricity radius : ℝ} (nonnegative : 0 ≤ eccentricity) (small : eccentricity < 1)
    (radiusNonnegative : 0 ≤ radius) (parameter : Parameters)
    (rhoBound : |parameter 0| ≤ eccentricity) (otherSmall : ∀ index : Fin 3, |parameter index.succ| ≤ radius) :
    Summable (Multipliers.envelopeTerm phase grade (actualCells 1 parameter)) ∧
      Multipliers.envelope phase grade (actualCells 1 parameter) ≤
        (envelopeComparison phase grade * inverseDeviationConstant phase grade eccentricity radius) * |parameter 0| := by
  have admissible : parameter ∈ parameterDomain := rhoBound.trans_lt small
  have conversion := coefficient_envelope_bound phase grade (inverseDeviationCoefficient phase grade parameter)
    (actualCells 1 parameter) (fun cell => inverseDeviation_cell phase grade parameter admissible cell seedOrigin)
  refine ⟨conversion.1, conversion.2.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left
    (inverseDeviation_norm_bound phase grade nonnegative small radiusNonnegative parameter rhoBound otherSmall)
    (envelopeComparison_nonnegative phase grade)).trans_eq (mul_assoc _ _ _).symm

end Grad.Constraints.Seed

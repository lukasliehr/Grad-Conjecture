import AEC8ConstructedReferenceEnergyConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators
namespace Grad.AnnularLowVolterra
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularVariational Grad.CartesianState

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
theorem norm_add_sq_two (first second : E) :
    ‖first + second‖ ^ 2 ≤ 2 * ‖first‖ ^ 2 + 2 * ‖second‖ ^ 2 := by
  have bound := norm_add_le first second
  have squared := (sq_le_sq₀ (norm_nonneg (first + second)) (add_nonneg (norm_nonneg first) (norm_nonneg second))).mpr bound
  nlinarith [sq_nonneg (‖first‖ - ‖second‖)]

theorem real_two_row_norm_sq (constant a b : ℝ) (nonnegative : 0 ≤ constant)
    (aBound : |a| ≤ constant) (bBound : |b| ≤ constant) (first second : E) :
    ‖a • first + b • second‖ ^ 2 ≤ 2 * constant ^ 2 * (‖first‖ ^ 2 + ‖second‖ ^ 2) := by
  have bound : ‖a • first + b • second‖ ≤ constant * (‖first‖ + ‖second‖) := by
    calc
      _ ≤ ‖a • first‖ + ‖b • second‖ := norm_add_le _ _
      _ = |a| * ‖first‖ + |b| * ‖second‖ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ constant * ‖first‖ + constant * ‖second‖ :=
        add_le_add (mul_le_mul_of_nonneg_right aBound (norm_nonneg _))
          (mul_le_mul_of_nonneg_right bBound (norm_nonneg _))
      _ = _ := by ring
  have squared := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg nonnegative (add_nonneg (norm_nonneg first) (norm_nonneg second)))).mpr bound
  nlinarith [mul_nonneg (sq_nonneg constant) (sq_nonneg (‖first‖ - ‖second‖))]

theorem lowReferenceRow_normalized_sq (parameters : PhaseParameters) (length radius : ℝ)
    (lengthPositive : 0 < length) (mode : LowAnnularMode) (positive : 0 < radius) (bounded : radius ≤ 1)
    (row : Fin 2) (first second : E) :
    ‖(lowMu length radius mode.val.2)⁻¹ •
      (lowReferenceMatrix parameters length radius mode row 0 • first +
        lowReferenceMatrix parameters length radius mode row 1 • second)‖ ^ 2 ≤
      2 * lowReferenceCoefficientConstant parameters length ^ 2 * (‖first‖ ^ 2 + ‖second‖ ^ 2) := by
  rw [smul_add, smul_smul, smul_smul]
  have firstCoefficient : (lowMu length radius mode.val.2)⁻¹ * lowReferenceMatrix parameters length radius mode row 0 =
      lowNormalizedReferenceCoefficient parameters length radius mode row 0 := by
    unfold lowNormalizedReferenceCoefficient
    rw [div_eq_mul_inv, mul_comm]
  have secondCoefficient : (lowMu length radius mode.val.2)⁻¹ * lowReferenceMatrix parameters length radius mode row 1 =
      lowNormalizedReferenceCoefficient parameters length radius mode row 1 := by
    unfold lowNormalizedReferenceCoefficient
    rw [div_eq_mul_inv, mul_comm]
  rw [firstCoefficient, secondCoefficient]
  exact real_two_row_norm_sq _ _ _ (lowReferenceCoefficientConstant_pos parameters length lengthPositive).le
    (lowNormalizedReferenceCoefficient_bound parameters length radius lengthPositive positive bounded mode row 0)
    (lowNormalizedReferenceCoefficient_bound parameters length radius lengthPositive positive bounded mode row 1) first second

/-- The exact normalized derivative is controlled in the original Hilbert
sum of both low components. This supplies the derivative half of BE18 Y. -/
theorem lowReferenceDerivative_pair_bound (parameters : PhaseParameters) (length radius : ℝ)
    (lengthPositive : 0 < length) (mode : LowAnnularMode) (positive : 0 < radius) (bounded : radius ≤ 1)
    (first second forcingFirst forcingSecond : E) :
    ‖(lowMu length radius mode.val.2)⁻¹ •
      (lowReferenceFirst parameters length radius mode first second + lowMu length radius mode.val.2 • forcingFirst)‖ ^ 2 +
    ‖(lowMu length radius mode.val.2)⁻¹ •
      (lowReferenceSecond parameters length radius mode first second + lowMu length radius mode.val.2 • forcingSecond)‖ ^ 2 ≤
      8 * lowReferenceCoefficientConstant parameters length ^ 2 * (‖first‖ ^ 2 + ‖second‖ ^ 2) +
        2 * (‖forcingFirst‖ ^ 2 + ‖forcingSecond‖ ^ 2) := by
  have nonzero := (lowMu_pos length radius mode.val.2 positive).ne'
  rw [smul_add, smul_smul, inv_mul_cancel₀ nonzero, one_smul,
    smul_add, smul_smul, inv_mul_cancel₀ nonzero, one_smul]
  have firstRow := lowReferenceRow_normalized_sq parameters length radius lengthPositive mode positive bounded 0 first second
  have secondRow := lowReferenceRow_normalized_sq parameters length radius lengthPositive mode positive bounded 1 first second
  rw [← lowReferenceFirst_matrix] at firstRow
  rw [← lowReferenceSecond_matrix] at secondRow
  have firstSum := norm_add_sq_two ((lowMu length radius mode.val.2)⁻¹ • lowReferenceFirst parameters length radius mode first second) forcingFirst
  have secondSum := norm_add_sq_two ((lowMu length radius mode.val.2)⁻¹ • lowReferenceSecond parameters length radius mode first second) forcingSecond
  linarith

end Hilbert
end Grad.AnnularLowVolterra

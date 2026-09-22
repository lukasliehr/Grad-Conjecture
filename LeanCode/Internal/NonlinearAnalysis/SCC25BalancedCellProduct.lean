import SCC24ProductWeights
import BL42CoefficientOperator

noncomputable section
open scoped BigOperators ENNReal

namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarAngular Grad.BoundaryLift

def balancedProductEntry (dimension : ℕ) (parameters : PhaseParameters) (power : ℕ)
    (radius : ℝ) (shift : ℤ × ℤ) (coefficient : ℂ) (mode : ℤ × ℤ) :
    ComplexEuclidean dimension →L[ℂ] ComplexEuclidean dimension :=
  ((balancedProductRatio parameters power radius shift mode : ℂ) * coefficient) •
    ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)

theorem balancedProductEntry_bound (dimension : ℕ) (parameters : PhaseParameters) (power : ℕ)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
    (shift : ℤ × ℤ) (coefficient : ℂ) (mode : ℤ × ℤ) :
    ‖balancedProductEntry dimension parameters power radius shift coefficient mode‖ ≤
      productPhaseConstant parameters power * coefficientRadialEnvelope parameters shift.2 radius * ‖coefficient‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (productPhaseConstant_pos _ _).le (coefficientRadialEnvelope_pos _ _ _).le)
      (norm_nonneg coefficient))
  intro value
  change ‖((balancedProductRatio parameters power radius shift mode : ℂ) * coefficient) • value‖ ≤ _
  rw [norm_smul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (balancedProductRatio_nonnegative _ _ _ _ _)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (balancedProductRatio_bound parameters power radius nonnegative bounded shift mode) (norm_nonneg coefficient))
    (norm_nonneg value)

def balancedSingleProduct {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
    (shift : ℤ × ℤ) (coefficient : ℂ) (high low : CellL2 dimension) : CellL2 dimension :=
  coefficientOperator parameters 0 (productTranslation shift)
    (balancedProductEntry dimension parameters power radius shift coefficient)
    (mul_nonneg (mul_nonneg (productPhaseConstant_pos _ _).le (coefficientRadialEnvelope_pos _ _ _).le)
      (norm_nonneg coefficient))
    (balancedProductEntry_bound dimension parameters power radius nonnegative bounded shift coefficient)
    (high + ((annularFrequency shift.1 shift.2 : ℂ) ^ power) • low)

theorem balancedSingleProduct_value {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
    (shift : ℤ × ℤ) (coefficient : ℂ) (high low : CellL2 dimension) (mode : ℤ × ℤ) :
    balancedSingleProduct parameters power radius nonnegative bounded shift coefficient high low mode =
      ((balancedProductRatio parameters power radius shift mode : ℂ) * coefficient) •
        (high (mode - shift) + ((annularFrequency shift.1 shift.2 : ℂ) ^ power) • low (mode - shift)) := by
  rfl

def productMoment (parameters : PhaseParameters) (power : ℕ) (radius : ℝ)
    (coefficient : ℤ × ℤ → ℂ) (shift : ℤ × ℤ) : ℝ :=
  coefficientRadialEnvelope parameters shift.2 radius * annularFrequency shift.1 shift.2 ^ power * ‖coefficient shift‖

theorem productMoment_nonnegative (parameters : PhaseParameters) (power : ℕ) (radius : ℝ)
    (coefficient : ℤ × ℤ → ℂ) (shift : ℤ × ℤ) : 0 ≤ productMoment parameters power radius coefficient shift :=
  mul_nonneg (mul_nonneg (coefficientRadialEnvelope_pos _ _ _).le
    (pow_nonneg (annularFrequency_nonnegative _ _) _)) (norm_nonneg _)

theorem balancedSingleProduct_norm {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
    (coefficient : ℤ × ℤ → ℂ) (high low : CellL2 dimension) (shift : ℤ × ℤ) :
    ‖balancedSingleProduct parameters power radius nonnegative bounded shift (coefficient shift) high low‖ ≤
      productPhaseConstant parameters power *
        (productMoment parameters 0 radius coefficient shift * ‖high‖ +
          productMoment parameters power radius coefficient shift * ‖low‖) := by
  have bound := entryReindexLinear_norm_le parameters 0 (productTranslation shift)
    (balancedProductEntry dimension parameters power radius shift (coefficient shift))
    (mul_nonneg (mul_nonneg (productPhaseConstant_pos _ _).le (coefficientRadialEnvelope_pos _ _ _).le)
      (norm_nonneg (coefficient shift)))
    (balancedProductEntry_bound dimension parameters power radius nonnegative bounded shift (coefficient shift))
    (high + ((annularFrequency shift.1 shift.2 : ℂ) ^ power) • low)
  have sumBound : ‖high + ((annularFrequency shift.1 shift.2 : ℂ) ^ power) • low‖ ≤
      ‖high‖ + annularFrequency shift.1 shift.2 ^ power * ‖low‖ := by
    exact (norm_add_le _ _).trans_eq (by
      rw [norm_smul, Complex.norm_pow, Complex.norm_real,
        Real.norm_of_nonneg (annularFrequency_nonnegative _ _)])
  exact bound.trans ((mul_le_mul_of_nonneg_left sumBound
    (mul_nonneg (mul_nonneg (productPhaseConstant_pos _ _).le (coefficientRadialEnvelope_pos _ _ _).le)
      (norm_nonneg _))).trans_eq (by dsimp [productMoment]; ring))

def pointwiseProduct {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
    (coefficient : ℤ × ℤ → ℂ) (high low : CellL2 dimension) : CellL2 dimension :=
  ∑' shift, balancedSingleProduct parameters power radius nonnegative bounded shift (coefficient shift) high low

theorem pointwiseProduct_summable_norm {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
    (coefficient : ℤ × ℤ → ℂ)
    (lowMoment : Summable (productMoment parameters 0 radius coefficient))
    (highMoment : Summable (productMoment parameters power radius coefficient)) (high low : CellL2 dimension) :
    Summable (fun shift => ‖balancedSingleProduct parameters power radius nonnegative bounded shift (coefficient shift) high low‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (balancedSingleProduct_norm parameters power radius nonnegative bounded coefficient high low)
    (((lowMoment.mul_right ‖high‖).add (highMoment.mul_right ‖low‖)).mul_left _)

/-- The one-high Young estimate is pointwise in radius. Neither coefficient
moment has been replaced by a sum of radiuswise suprema. -/
theorem pointwiseProduct_norm {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
    (coefficient : ℤ × ℤ → ℂ)
    (lowMoment : Summable (productMoment parameters 0 radius coefficient))
    (highMoment : Summable (productMoment parameters power radius coefficient)) (high low : CellL2 dimension) :
    ‖pointwiseProduct parameters power radius nonnegative bounded coefficient high low‖ ≤
      productPhaseConstant parameters power *
        ((∑' shift, productMoment parameters 0 radius coefficient shift) * ‖high‖ +
          (∑' shift, productMoment parameters power radius coefficient shift) * ‖low‖) := by
  have summable := pointwiseProduct_summable_norm parameters power radius nonnegative bounded coefficient lowMoment highMoment high low
  refine (norm_tsum_le_tsum_norm summable).trans ?_
  have bound := summable.tsum_le_tsum
    (balancedSingleProduct_norm parameters power radius nonnegative bounded coefficient high low)
    (((lowMoment.mul_right ‖high‖).add (highMoment.mul_right ‖low‖)).mul_left _)
  simpa only [tsum_mul_left, Summable.tsum_add (lowMoment.mul_right ‖high‖) (highMoment.mul_right ‖low‖),
    tsum_mul_right] using bound

end Grad.SourceCollarCoefficients

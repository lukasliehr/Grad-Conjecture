import BL43BoundaryOperators

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

def angularShiftEntry (parameters : PhaseParameters) (grade dimension : ℕ) (shift : ℤ)
    (mode : ℤ × ℤ) : ComplexEuclidean dimension →L[ℂ] ComplexEuclidean dimension :=
  ((boundaryWeight parameters grade mode /
      boundaryWeight parameters grade (mode.1 - shift, mode.2) : ℝ) : ℂ) •
    ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)

theorem angularShiftEntry_norm_le (parameters : PhaseParameters) (grade dimension : ℕ)
    (shift : ℤ) (mode : ℤ × ℤ) :
    ‖angularShiftEntry parameters grade dimension shift mode‖ ≤ (1 + |(shift : ℝ)|) ^ grade := by
  have ratioPos : 0 < boundaryWeight parameters grade mode /
      boundaryWeight parameters grade (mode.1 - shift, mode.2) :=
    div_pos (boundaryWeight_pos parameters grade mode) (boundaryWeight_pos parameters grade _)
  have ratioBound : boundaryWeight parameters grade mode /
      boundaryWeight parameters grade (mode.1 - shift, mode.2) ≤
        cellPolynomialWeight shift ^ grade := by
    rw [div_le_iff₀ (boundaryWeight_pos parameters grade _)]
    have shiftLaw := boundaryWeight_angular_shift_le parameters grade mode.1 mode.2 shift
    simpa only [Prod.mk.eta] using shiftLaw
  unfold angularShiftEntry
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ratioPos]
  calc boundaryWeight parameters grade mode /
        boundaryWeight parameters grade (mode.1 - shift, mode.2) *
          ‖ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)‖
      ≤ boundaryWeight parameters grade mode /
          boundaryWeight parameters grade (mode.1 - shift, mode.2) * 1 :=
        mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le ratioPos.le
    _ = boundaryWeight parameters grade mode /
          boundaryWeight parameters grade (mode.1 - shift, mode.2) := mul_one _
    _ ≤ cellPolynomialWeight shift ^ grade := ratioBound
    _ = (1 + |(shift : ℝ)|) ^ grade := by rw [cellPolynomialWeight_formula]

/-- The exact angular index shift on every boundary grade. -/
def angularShiftOperator (parameters : PhaseParameters) (grade dimension : ℕ) (shift : ℤ) :
    BoundaryGrade parameters (ComplexEuclidean dimension) grade →L[ℂ]
      BoundaryGrade parameters (ComplexEuclidean dimension) grade :=
  coefficientOperator parameters grade (angularPairTranslation shift)
    (angularShiftEntry parameters grade dimension shift) (by positivity)
    (angularShiftEntry_norm_le parameters grade dimension shift)

theorem angularShiftOperator_norm_le (parameters : PhaseParameters) (grade dimension : ℕ)
    (shift : ℤ) :
    ‖angularShiftOperator parameters grade dimension shift‖ ≤ (1 + |(shift : ℝ)|) ^ grade :=
  coefficientOperator_norm_le parameters grade _ _ _ _

theorem angularShiftOperator_coefficient (parameters : PhaseParameters) (grade dimension : ℕ)
    (shift : ℤ) (field : BoundaryGrade parameters (ComplexEuclidean dimension) grade)
    (mode : ℤ × ℤ) :
    boundaryCoefficient parameters grade
        (angularShiftOperator parameters grade dimension shift field) mode =
      boundaryCoefficient parameters grade field (mode.1 - shift, mode.2) := by
  have applyLaw : angularShiftOperator parameters grade dimension shift field mode =
      ((boundaryWeight parameters grade mode /
          boundaryWeight parameters grade (mode.1 - shift, mode.2) : ℝ) : ℂ) •
        field (mode.1 - shift, mode.2) := rfl
  unfold boundaryCoefficient
  rw [applyLaw, smul_smul]
  have modeNe : ((boundaryWeight parameters grade mode : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (boundaryWeight_pos parameters grade mode).ne'
  have scalarLaw : ((boundaryWeight parameters grade mode : ℝ) : ℂ)⁻¹ *
      ((boundaryWeight parameters grade mode /
          boundaryWeight parameters grade (mode.1 - shift, mode.2) : ℝ) : ℂ) =
        ((boundaryWeight parameters grade (mode.1 - shift, mode.2) : ℝ) : ℂ)⁻¹ := by
    rw [Complex.ofReal_div, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ modeNe, one_mul]
  rw [scalarLaw]

def highComplementEntry (dimension : ℕ) (mode : ℤ × ℤ) :
    ComplexEuclidean dimension →L[ℂ] ComplexEuclidean dimension :=
  if |mode.1| ≤ 2 then 0 else ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)

theorem highComplementEntry_norm_le (dimension : ℕ) (mode : ℤ × ℤ) :
    ‖highComplementEntry dimension mode‖ ≤ 1 := by
  unfold highComplementEntry
  by_cases small : |mode.1| ≤ 2
  · rw [if_pos small, norm_zero]
    norm_num
  · rw [if_neg small]
    exact ContinuousLinearMap.norm_id_le

/-- The exact five-mode angular complement projection on every boundary
grade, with norm at most one. -/
def highComplementProjection (parameters : PhaseParameters) (grade dimension : ℕ) :
    BoundaryGrade parameters (ComplexEuclidean dimension) grade →L[ℂ]
      BoundaryGrade parameters (ComplexEuclidean dimension) grade :=
  coefficientOperator parameters grade (Equiv.refl (ℤ × ℤ)) (highComplementEntry dimension)
    zero_le_one (highComplementEntry_norm_le dimension)

theorem highComplementProjection_norm_le (parameters : PhaseParameters) (grade dimension : ℕ) :
    ‖highComplementProjection parameters grade dimension‖ ≤ 1 :=
  coefficientOperator_norm_le parameters grade _ _ _ _

theorem highComplementProjection_coefficient (parameters : PhaseParameters) (grade dimension : ℕ)
    (field : BoundaryGrade parameters (ComplexEuclidean dimension) grade) (mode : ℤ × ℤ) :
    boundaryCoefficient parameters grade
        (highComplementProjection parameters grade dimension field) mode =
      if |mode.1| ≤ 2 then 0 else boundaryCoefficient parameters grade field mode := by
  have applyLaw : highComplementProjection parameters grade dimension field mode =
      highComplementEntry dimension mode (field mode) := rfl
  unfold boundaryCoefficient
  rw [applyLaw]
  unfold highComplementEntry
  by_cases small : |mode.1| ≤ 2
  · rw [if_pos small, if_pos small, zero_apply, smul_zero]
  · rw [if_neg small, if_neg small, ContinuousLinearMap.id_apply]

theorem highComplementProjection_idempotent (parameters : PhaseParameters) (grade dimension : ℕ) :
    (highComplementProjection parameters grade dimension).comp
        (highComplementProjection parameters grade dimension) =
      highComplementProjection parameters grade dimension := by
  apply ContinuousLinearMap.ext
  intro field
  apply Subtype.ext
  funext mode
  change highComplementEntry dimension mode
      (highComplementProjection parameters grade dimension field mode) =
    highComplementEntry dimension mode (field mode)
  have directLaw : highComplementProjection parameters grade dimension field mode =
      highComplementEntry dimension mode (field mode) := rfl
  rw [directLaw]
  unfold highComplementEntry
  by_cases small : |mode.1| ≤ 2
  · simp only [if_pos small, zero_apply]
  · simp only [if_neg small, ContinuousLinearMap.id_apply]

end Grad.BoundaryLift

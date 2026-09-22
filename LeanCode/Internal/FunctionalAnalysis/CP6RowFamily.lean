import CP5RowMembership

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Cor18

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Gauges Grad.BoundaryTrace Grad.BoundaryLift

/-- The literal N29 physical-row coefficient family `P_{≥3}[e_r · M⁻¹ u_⊥]`
of a state field, as high-angular boundary coefficients of the radial
contraction of the accepted seed-inverted planar field. -/
def physicalRowFamily (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (state : ACore parameters 3) :
    ℤ × ℤ → ComplexEuclidean 1 :=
  fun mode => if |mode.1| ≤ 2 then 0 else
    EuclideanSpace.single (0 : Fin 1)
      (fourierCoeff (rowFunction parameters
        (rowField parameters parameter inside state) mode.2) mode.1)

theorem norm_weight_smul (parameters : PhaseParameters) (grade : ℕ)
    (mode : ℤ × ℤ) {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (vector : Value) :
    ‖(boundaryWeight parameters grade mode : ℂ) • vector‖ =
      boundaryWeight parameters grade mode * ‖vector‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (boundaryWeight_pos parameters grade mode)]

/-- The two-shift domination of the cut coefficient by the weighted trace
families. -/
theorem physicalRowFamily_pointwise (parameters : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (state : ACore parameters 3) (grade : ℕ) (mode : ℤ × ℤ) :
    ‖(boundaryWeight parameters grade mode : ℂ) •
        physicalRowFamily parameters parameter inside state mode‖ ≤
      cellPolynomialWeight 1 ^ grade *
        (boundaryWeight parameters grade (mode.1 - 1, mode.2) *
          ‖originalBoundaryCoefficient parameters
            (rowField parameters parameter inside state) (mode.1 - 1, mode.2)‖) +
        cellPolynomialWeight (-1) ^ grade *
          (boundaryWeight parameters grade (mode.1 + 1, mode.2) *
            ‖originalBoundaryCoefficient parameters
              (rowField parameters parameter inside state) (mode.1 + 1, mode.2)‖) := by
  set field := rowField parameters parameter inside state with fieldDef
  have termNonneg : ∀ shift : ℤ, 0 ≤ cellPolynomialWeight shift ^ grade *
      (boundaryWeight parameters grade (mode.1 - shift, mode.2) *
        ‖originalBoundaryCoefficient parameters field (mode.1 - shift, mode.2)‖) :=
    fun shift => mul_nonneg (pow_nonneg
      (le_trans zero_le_one (cellPolynomialWeight_one_le shift)) grade)
      (mul_nonneg (boundaryWeight_pos parameters grade _).le (norm_nonneg _))
  unfold physicalRowFamily
  by_cases lowMode : |mode.1| ≤ 2
  · rw [if_pos lowMode, smul_zero, norm_zero]
    have first := termNonneg 1
    have second := termNonneg (-1)
    rw [show mode.1 - -1 = mode.1 + 1 by ring] at second
    exact add_nonneg first second
  · rw [if_neg lowMode, norm_weight_smul, single_norm_eq]
    have coefficientSplit := rowFunction_coefficient parameters field mode.2 mode.1
    have plusBound : ‖fourierCoeff (rowPlusFunction parameters field mode.2)
        (mode.1 - 1)‖ ≤ ‖originalBoundaryCoefficient parameters field
          (mode.1 - 1, mode.2)‖ := by
      rw [rowPlusFunction_coefficient]
      have splitNorm := norm_add_le
        (originalBoundaryCoefficient parameters field (mode.1 - 1, mode.2) 0 / 2)
        (originalBoundaryCoefficient parameters field (mode.1 - 1, mode.2) 1 /
          (2 * Complex.I))
      apply splitNorm.trans
      have firstComponent := component_norm_le
        (originalBoundaryCoefficient parameters field (mode.1 - 1, mode.2)) 0
      have secondComponent := component_norm_le
        (originalBoundaryCoefficient parameters field (mode.1 - 1, mode.2)) 1
      have twoINorm : ‖(2 * Complex.I : ℂ)‖ = 2 := by
        rw [norm_mul, Complex.norm_I, mul_one]
        simp
      rw [norm_div, norm_div, twoINorm]
      rw [show ‖(2 : ℂ)‖ = 2 by simp]
      nlinarith [norm_nonneg (originalBoundaryCoefficient parameters field
        (mode.1 - 1, mode.2))]
    have minusBound : ‖fourierCoeff (rowMinusFunction parameters field mode.2)
        (mode.1 + 1)‖ ≤ ‖originalBoundaryCoefficient parameters field
          (mode.1 + 1, mode.2)‖ := by
      rw [rowMinusFunction_coefficient]
      have splitNorm := norm_sub_le
        (originalBoundaryCoefficient parameters field (mode.1 + 1, mode.2) 0 / 2)
        (originalBoundaryCoefficient parameters field (mode.1 + 1, mode.2) 1 /
          (2 * Complex.I))
      apply splitNorm.trans
      have firstComponent := component_norm_le
        (originalBoundaryCoefficient parameters field (mode.1 + 1, mode.2)) 0
      have secondComponent := component_norm_le
        (originalBoundaryCoefficient parameters field (mode.1 + 1, mode.2)) 1
      have twoINorm : ‖(2 * Complex.I : ℂ)‖ = 2 := by
        rw [norm_mul, Complex.norm_I, mul_one]
        simp
      rw [norm_div, norm_div, twoINorm]
      rw [show ‖(2 : ℂ)‖ = 2 by simp]
      nlinarith [norm_nonneg (originalBoundaryCoefficient parameters field
        (mode.1 + 1, mode.2))]
    have coefficientBound : ‖fourierCoeff (rowFunction parameters field mode.2)
        mode.1‖ ≤ ‖originalBoundaryCoefficient parameters field
          (mode.1 - 1, mode.2)‖ + ‖originalBoundaryCoefficient parameters field
          (mode.1 + 1, mode.2)‖ := by
      rw [coefficientSplit]
      exact (norm_add_le _ _).trans (add_le_add plusBound minusBound)
    have weightFirst := boundaryWeight_angular_shift_le parameters grade
      mode.1 mode.2 1
    have weightSecond := boundaryWeight_angular_shift_le parameters grade
      mode.1 mode.2 (-1)
    rw [show mode.1 - -1 = mode.1 + 1 by ring] at weightSecond
    have weightNonneg := (boundaryWeight_pos parameters grade mode).le
    have firstNormNonneg := norm_nonneg (originalBoundaryCoefficient parameters
      field (mode.1 - 1, mode.2))
    have secondNormNonneg := norm_nonneg (originalBoundaryCoefficient parameters
      field (mode.1 + 1, mode.2))
    have firstWeightNonneg := (boundaryWeight_pos parameters grade
      (mode.1 - 1, mode.2)).le
    have secondWeightNonneg := (boundaryWeight_pos parameters grade
      (mode.1 + 1, mode.2)).le
    calc boundaryWeight parameters grade mode *
        ‖fourierCoeff (rowFunction parameters field mode.2) mode.1‖
        ≤ boundaryWeight parameters grade mode *
          (‖originalBoundaryCoefficient parameters field (mode.1 - 1, mode.2)‖ +
            ‖originalBoundaryCoefficient parameters field (mode.1 + 1, mode.2)‖) :=
          mul_le_mul_of_nonneg_left coefficientBound weightNonneg
      _ ≤ cellPolynomialWeight 1 ^ grade *
            (boundaryWeight parameters grade (mode.1 - 1, mode.2) *
              ‖originalBoundaryCoefficient parameters field (mode.1 - 1, mode.2)‖) +
          cellPolynomialWeight (-1) ^ grade *
            (boundaryWeight parameters grade (mode.1 + 1, mode.2) *
              ‖originalBoundaryCoefficient parameters field (mode.1 + 1, mode.2)‖) := by
          rw [mul_add]
          apply add_le_add
          · calc boundaryWeight parameters grade mode *
                ‖originalBoundaryCoefficient parameters field (mode.1 - 1, mode.2)‖
                ≤ (cellPolynomialWeight 1 ^ grade *
                    boundaryWeight parameters grade (mode.1 - 1, mode.2)) *
                  ‖originalBoundaryCoefficient parameters field
                    (mode.1 - 1, mode.2)‖ :=
                  mul_le_mul_of_nonneg_right weightFirst firstNormNonneg
              _ = _ := by ring
          · calc boundaryWeight parameters grade mode *
                ‖originalBoundaryCoefficient parameters field (mode.1 + 1, mode.2)‖
                ≤ (cellPolynomialWeight (-1) ^ grade *
                    boundaryWeight parameters grade (mode.1 + 1, mode.2)) *
                  ‖originalBoundaryCoefficient parameters field
                    (mode.1 + 1, mode.2)‖ :=
                  mul_le_mul_of_nonneg_right weightSecond secondNormNonneg
              _ = _ := by ring

end Grad.Cor18

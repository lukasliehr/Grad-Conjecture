import AW2Hessian

noncomputable section

open Grad.PDEBootstrap
open scoped ContDiff RealInnerProductSpace

namespace Grad.AnalyticWeights.Calculus

theorem physicalWeight_hasFDerivAt (sigma gamma scale : ℝ) (cell : ℤ) (point : Spatial) :
    HasFDerivAt (physicalWeight sigma gamma scale cell)
      (physicalWeight sigma gamma scale cell point • phaseGradient gamma scale cell point) point :=
  (physicalPhase_hasFDerivAt sigma gamma scale cell point).exp

theorem inverseWeight_hasFDerivAt (sigma gamma scale : ℝ) (cell : ℤ) (point : Spatial) :
    HasFDerivAt (inverseWeight sigma gamma scale cell)
      (-inverseWeight sigma gamma scale cell point • phaseGradient gamma scale cell point) point := by
  have equality : inverseWeight sigma gamma scale cell =
      fun source => Real.exp (-physicalPhase sigma gamma scale cell source) :=
    funext (inverseWeight_exp sigma gamma scale cell)
  rw [equality]
  apply (physicalPhase_hasFDerivAt sigma gamma scale cell point).neg.exp.congr_fderiv
  apply ContinuousLinearMap.ext
  intro direction
  change Real.exp (-physicalPhase sigma gamma scale cell point) *
      (-phaseGradient gamma scale cell point direction) =
    (-Real.exp (-physicalPhase sigma gamma scale cell point)) * phaseGradient gamma scale cell point direction
  ring

theorem weightDerivativeGoal : WeightDerivativeGoal := by
  intro sigma gamma scale cell point
  refine ⟨physicalWeight_hasFDerivAt sigma gamma scale cell point,
    inverseWeight_hasFDerivAt sigma gamma scale cell point, ?_, ?_⟩
  · intro direction
    rw [(physicalWeight_hasFDerivAt sigma gamma scale cell point).fderiv]
    rfl
  · intro direction
    rw [(inverseWeight_hasFDerivAt sigma gamma scale cell point).fderiv]
    simp only [phaseGradient, smul_apply, smul_eq_mul, innerSL_apply_apply]
    ring

theorem weightAxisGoal : WeightAxisGoal := by
  intro sigma gamma scale cell
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [physicalWeight_exp, (axisGoal sigma gamma scale cell).1]
  · rw [inverseWeight_exp, (axisGoal sigma gamma scale cell).1, neg_mul]
  · rw [(physicalWeight_hasFDerivAt sigma gamma scale cell 0).fderiv]
    simp [phaseGradient]
  · rw [(inverseWeight_hasFDerivAt sigma gamma scale cell 0).fderiv]
    simp [phaseGradient]

theorem physicalPhase_fderiv_norm (sigma gamma scale : ℝ) (cell : ℤ) (point : Spatial) :
    ‖fderiv ℝ (physicalPhase sigma gamma scale cell) point‖ =
      |(-gamma * scale ^ 2 * Grad.CellWeights.cellWeight cell ^ 2 / Real.sqrt (radicand scale cell point))| * ‖point‖ := by
  rw [physicalPhase_fderiv, phaseGradient, norm_smul, Real.norm_eq_abs, innerSL_apply_norm]

theorem firstNormGoal : FirstNormGoal := by
  intro sigma gamma scale cell gammaNonnegative scaleNonnegative point
  have rootPositive := sqrt_radicand_pos scale cell point
  have coefficientNonnegative :
      0 ≤ gamma * scale ^ 2 * Grad.CellWeights.cellWeight cell ^ 2 / Real.sqrt (radicand scale cell point) :=
    div_nonneg (mul_nonneg (mul_nonneg gammaNonnegative (sq_nonneg scale))
      (sq_nonneg (Grad.CellWeights.cellWeight cell))) rootPositive.le
  have rootBound : scale * Grad.CellWeights.cellWeight cell * ‖point‖ ≤ Real.sqrt (radicand scale cell point) := by
    apply Real.le_sqrt_of_sq_le
    unfold radicand
    nlinarith
  have ratioBound : scale * Grad.CellWeights.cellWeight cell * ‖point‖ /
      Real.sqrt (radicand scale cell point) ≤ 1 :=
    (div_le_iff₀ rootPositive).mpr (by simpa only [one_mul] using rootBound)
  rw [physicalPhase_fderiv_norm, neg_mul, neg_mul, neg_div, abs_neg, abs_of_nonneg coefficientNonnegative]
  calc
    _ = (gamma * scale * Grad.CellWeights.cellWeight cell) *
        (scale * Grad.CellWeights.cellWeight cell * ‖point‖ / Real.sqrt (radicand scale cell point)) := by ring
    _ ≤ (gamma * scale * Grad.CellWeights.cellWeight cell) * 1 :=
      mul_le_mul_of_nonneg_left ratioBound (mul_nonneg (mul_nonneg gammaNonnegative scaleNonnegative)
        (Grad.CellWeights.cellWeight_pos cell).le)
    _ = _ := mul_one _

theorem zeroGoal : ZeroGoal := by
  constructor
  · intro sigma gamma cell point
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [physicalPhase, phase]
    · rw [physicalPhase_fderiv]
      simp [phaseGradient]
    · apply ContinuousLinearMap.ext
      intro first
      apply ContinuousLinearMap.ext
      intro second
      rw [physicalPhase_hessian_apply]
      simp
    · simp [physicalWeight, weight, phase]
    · simp [inverseWeight_exp, physicalPhase, phase, neg_mul]
  · intro sigma gamma scale point
    simp [physicalPhase, phase, Grad.CellWeights.cellWeight, mul_pow]

end Grad.AnalyticWeights.Calculus

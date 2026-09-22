import AW2Basic

noncomputable section

open Grad.PDEBootstrap
open scoped ContDiff RealInnerProductSpace

namespace Grad.AnalyticWeights.Calculus

theorem radicand_hasFDerivAt (scale : ℝ) (cell : ℤ) (point : Spatial) :
    HasFDerivAt (radicand scale cell)
      ((2 * scale ^ 2 * Grad.CellWeights.cellWeight cell ^ 2) • innerSL ℝ point) point := by
  have derivative := ((((hasStrictFDerivAt_norm_sq point).hasFDerivAt.const_mul (scale ^ 2)).mul_const
    (Grad.CellWeights.cellWeight cell ^ 2)).const_add 1)
  apply derivative.congr_fderiv
  apply ContinuousLinearMap.ext
  intro direction
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  ring

theorem sqrt_radicand_hasFDerivAt (scale : ℝ) (cell : ℤ) (point : Spatial) :
    HasFDerivAt (fun source => Real.sqrt (radicand scale cell source))
      ((scale ^ 2 * Grad.CellWeights.cellWeight cell ^ 2 / Real.sqrt (radicand scale cell point)) •
        innerSL ℝ point) point := by
  have derivative := (radicand_hasFDerivAt scale cell point).sqrt (radicand_pos scale cell point).ne'
  apply derivative.congr_fderiv
  apply ContinuousLinearMap.ext
  intro direction
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  field_simp [(sqrt_radicand_pos scale cell point).ne']

theorem physicalPhase_hasFDerivAt (sigma gamma scale : ℝ) (cell : ℤ) (point : Spatial) :
    HasFDerivAt (physicalPhase sigma gamma scale cell) (phaseGradient gamma scale cell point) point := by
  have derivative := (((sqrt_radicand_hasFDerivAt scale cell point).sub_const 1).const_mul gamma).const_sub
    (sigma * Grad.CellWeights.cellWeight cell)
  have equality : physicalPhase sigma gamma scale cell = fun source =>
      sigma * Grad.CellWeights.cellWeight cell - gamma * (Real.sqrt (radicand scale cell source) - 1) :=
    funext (physicalPhase_formula sigma gamma scale cell)
  rw [equality]
  apply derivative.congr_fderiv
  apply ContinuousLinearMap.ext
  intro direction
  simp only [phaseGradient, smul_apply, neg_apply,
    smul_eq_mul, innerSL_apply_apply]
  ring

theorem physicalPhase_fderiv (sigma gamma scale : ℝ) (cell : ℤ) (point : Spatial) :
    fderiv ℝ (physicalPhase sigma gamma scale cell) point = phaseGradient gamma scale cell point :=
  (physicalPhase_hasFDerivAt sigma gamma scale cell point).fderiv

theorem physicalPhase_fderiv_apply (sigma gamma scale : ℝ) (cell : ℤ) (point direction : Spatial) :
    fderiv ℝ (physicalPhase sigma gamma scale cell) point direction =
      (-gamma * scale ^ 2 * Grad.CellWeights.cellWeight cell ^ 2 / Real.sqrt (radicand scale cell point)) *
        inner ℝ point direction := by
  rw [physicalPhase_fderiv]
  rfl

theorem firstGoal : FirstGoal := by
  intro sigma gamma scale cell point
  exact ⟨physicalPhase_hasFDerivAt sigma gamma scale cell point,
    physicalPhase_fderiv sigma gamma scale cell point, physicalPhase_fderiv_apply sigma gamma scale cell point⟩

end Grad.AnalyticWeights.Calculus

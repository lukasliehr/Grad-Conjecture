import AW2First
import Mathlib.Analysis.Calculus.Deriv.Inv

noncomputable section

open Grad.PDEBootstrap
open scoped ContDiff RealInnerProductSpace

namespace Grad.AnalyticWeights.Calculus

theorem gradientCoefficient_hasFDerivAt (gamma scale : ℝ) (cell : ℤ) (point : Spatial) :
    HasFDerivAt (fun source : Spatial =>
      -gamma * scale ^ 2 * Grad.CellWeights.cellWeight cell ^ 2 / Real.sqrt (radicand scale cell source))
      ((gamma * scale ^ 4 * Grad.CellWeights.cellWeight cell ^ 4 / Real.sqrt (radicand scale cell point) ^ 3) •
        innerSL ℝ point) point := by
  have inverseDerivative := (hasDerivAt_inv (sqrt_radicand_pos scale cell point).ne').comp_hasFDerivAt point
    (sqrt_radicand_hasFDerivAt scale cell point)
  have derivative := inverseDerivative.const_mul (-gamma * scale ^ 2 * Grad.CellWeights.cellWeight cell ^ 2)
  simp only [div_eq_mul_inv]
  apply derivative.congr_fderiv
  apply ContinuousLinearMap.ext
  intro direction
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  field_simp [(sqrt_radicand_pos scale cell point).ne']

theorem phaseGradient_hasFDerivAt (gamma scale : ℝ) (cell : ℤ) (point : Spatial) :
    HasFDerivAt (phaseGradient gamma scale cell) (phaseHessian gamma scale cell point) point := by
  let bilinear : Spatial →L[ℝ] (Spatial →L[ℝ] ℝ) := innerSL ℝ
  have derivative := (gradientCoefficient_hasFDerivAt gamma scale cell point).smul
    (bilinear.hasFDerivAt (x := point))
  apply derivative.congr_fderiv
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  change _ * inner ℝ first second + (_ * inner ℝ point first) * inner ℝ point second =
    _ * inner ℝ first second + _ * (inner ℝ point first * inner ℝ point second)
  ring

theorem physicalPhase_fderiv_hasFDerivAt (sigma gamma scale : ℝ) (cell : ℤ) (point : Spatial) :
    HasFDerivAt (fderiv ℝ (physicalPhase sigma gamma scale cell)) (phaseHessian gamma scale cell point) point := by
  have equality : fderiv ℝ (physicalPhase sigma gamma scale cell) = phaseGradient gamma scale cell :=
    funext (physicalPhase_fderiv sigma gamma scale cell)
  rw [equality]
  exact phaseGradient_hasFDerivAt gamma scale cell point

theorem physicalPhase_hessian (sigma gamma scale : ℝ) (cell : ℤ) (point : Spatial) :
    fderiv ℝ (fderiv ℝ (physicalPhase sigma gamma scale cell)) point = phaseHessian gamma scale cell point :=
  (physicalPhase_fderiv_hasFDerivAt sigma gamma scale cell point).fderiv

theorem physicalPhase_hessian_apply (sigma gamma scale : ℝ) (cell : ℤ) (point first second : Spatial) :
    fderiv ℝ (fderiv ℝ (physicalPhase sigma gamma scale cell)) point first second =
      (-gamma * scale ^ 2 * Grad.CellWeights.cellWeight cell ^ 2 / Real.sqrt (radicand scale cell point)) *
          inner ℝ first second +
        (gamma * scale ^ 4 * Grad.CellWeights.cellWeight cell ^ 4 / Real.sqrt (radicand scale cell point) ^ 3) *
          (inner ℝ point first * inner ℝ point second) := by
  rw [physicalPhase_hessian]
  rfl

theorem physicalPhase_iteratedFDeriv_two (sigma gamma scale : ℝ) (cell : ℤ) (point first second : Spatial) :
    iteratedFDeriv ℝ 2 (physicalPhase sigma gamma scale cell) point ![first, second] =
      (-gamma * scale ^ 2 * Grad.CellWeights.cellWeight cell ^ 2 / Real.sqrt (radicand scale cell point)) *
          inner ℝ first second +
        (gamma * scale ^ 4 * Grad.CellWeights.cellWeight cell ^ 4 / Real.sqrt (radicand scale cell point) ^ 3) *
          (inner ℝ point first * inner ℝ point second) := by
  rw [iteratedFDeriv_two_apply]
  exact physicalPhase_hessian_apply sigma gamma scale cell point first second

theorem hessianGoal : HessianGoal := by
  intro sigma gamma scale cell point
  exact ⟨physicalPhase_fderiv_hasFDerivAt sigma gamma scale cell point,
    physicalPhase_hessian sigma gamma scale cell point, physicalPhase_hessian_apply sigma gamma scale cell point,
    physicalPhase_iteratedFDeriv_two sigma gamma scale cell point⟩

theorem physicalPhase_fderiv_axis (sigma gamma scale : ℝ) (cell : ℤ) :
    fderiv ℝ (physicalPhase sigma gamma scale cell) 0 = 0 := by
  rw [physicalPhase_fderiv]
  simp [phaseGradient]

theorem physicalPhase_hessian_axis (sigma gamma scale : ℝ) (cell : ℤ) (first second : Spatial) :
    fderiv ℝ (fderiv ℝ (physicalPhase sigma gamma scale cell)) 0 first second =
      -gamma * scale ^ 2 * Grad.CellWeights.cellWeight cell ^ 2 * inner ℝ first second := by
  simpa [radicand] using physicalPhase_hessian_apply sigma gamma scale cell 0 first second

theorem axisGoal : AxisGoal := by
  intro sigma gamma scale cell
  refine ⟨?_, physicalPhase_fderiv_axis sigma gamma scale cell,
    physicalPhase_hessian_axis sigma gamma scale cell, ?_⟩
  · simp [physicalPhase, phase]
  · intro first second
    rw [iteratedFDeriv_two_apply]
    exact physicalPhase_hessian_axis sigma gamma scale cell first second

end Grad.AnalyticWeights.Calculus

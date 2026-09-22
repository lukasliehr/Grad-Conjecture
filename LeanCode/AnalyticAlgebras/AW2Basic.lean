import AW2Interface

noncomputable section

open Grad.PDEBootstrap
open scoped ContDiff RealInnerProductSpace

namespace Grad.AnalyticWeights.Calculus

theorem radicand_pos (scale : ℝ) (cell : ℤ) (point : Spatial) :
    0 < radicand scale cell point := by
  unfold radicand
  positivity

theorem sqrt_radicand_pos (scale : ℝ) (cell : ℤ) (point : Spatial) :
    0 < Real.sqrt (radicand scale cell point) :=
  Real.sqrt_pos.mpr (radicand_pos scale cell point)

theorem physicalPhase_formula (sigma gamma scale : ℝ) (cell : ℤ) (point : Spatial) :
    physicalPhase sigma gamma scale cell point = sigma * Grad.CellWeights.cellWeight cell -
      gamma * (Real.sqrt (radicand scale cell point) - 1) := by
  simp only [physicalPhase, phase, radicand, mul_pow]

theorem physicalWeight_exp (sigma gamma scale : ℝ) (cell : ℤ) (point : Spatial) :
    physicalWeight sigma gamma scale cell point = Real.exp (physicalPhase sigma gamma scale cell point) := rfl

theorem inverseWeight_exp (sigma gamma scale : ℝ) (cell : ℤ) (point : Spatial) :
    inverseWeight sigma gamma scale cell point = Real.exp (-physicalPhase sigma gamma scale cell point) := by
  rw [inverseWeight, physicalWeight_exp, Real.exp_neg]

theorem formulaGoal : FormulaGoal := by
  intro sigma gamma scale cell point
  refine ⟨radicand_pos scale cell point, physicalPhase_formula sigma gamma scale cell point,
    physicalWeight_exp sigma gamma scale cell point, inverseWeight_exp sigma gamma scale cell point, ?_⟩
  exact mul_inv_cancel₀ (Real.exp_ne_zero _)

theorem radicand_contDiff (scale : ℝ) (cell : ℤ) : ContDiff ℝ ∞ (radicand scale cell) := by
  unfold radicand
  exact contDiff_const.add ((contDiff_const.mul (contDiff_norm_sq ℝ)).mul contDiff_const)

theorem physicalPhase_contDiff (sigma gamma scale : ℝ) (cell : ℤ) :
    ContDiff ℝ ∞ (physicalPhase sigma gamma scale cell) := by
  have equality : physicalPhase sigma gamma scale cell = fun point =>
      sigma * Grad.CellWeights.cellWeight cell - gamma * (Real.sqrt (radicand scale cell point) - 1) :=
    funext (physicalPhase_formula sigma gamma scale cell)
  rw [equality]
  exact contDiff_const.sub (contDiff_const.mul
    (((radicand_contDiff scale cell).sqrt (fun point => (radicand_pos scale cell point).ne')).sub contDiff_const))

theorem smoothGoal : SmoothGoal := by
  intro sigma gamma scale cell
  have phaseSmooth := physicalPhase_contDiff sigma gamma scale cell
  refine ⟨phaseSmooth, phaseSmooth.exp, ?_⟩
  have equality : inverseWeight sigma gamma scale cell =
      fun point => Real.exp (-physicalPhase sigma gamma scale cell point) :=
    funext (inverseWeight_exp sigma gamma scale cell)
  rw [equality]
  exact phaseSmooth.neg.exp

theorem orthogonalGoal : OrthogonalGoal := by
  intro sigma gamma scale cell orthogonal point
  simp [physicalPhase, physicalWeight, inverseWeight]

end Grad.AnalyticWeights.Calculus

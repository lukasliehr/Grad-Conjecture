import AW2Proof

noncomputable section

open Grad.PDEBootstrap
open scoped ContDiff RealInnerProductSpace

namespace Grad.AnalyticWeights.Calculus.Consumer

theorem fullBlock : BlockGoal := blockGoal

theorem actualFormulas : FormulaGoal := formulaGoal

theorem globalSmoothness (sigma gamma scale : ℝ) (cell : ℤ) :
    ContDiff ℝ ∞ (fun point : Spatial => phase sigma gamma (scale * ‖point‖) cell) ∧
    ContDiff ℝ ∞ (fun point : Spatial => weight sigma gamma (scale * ‖point‖) cell) ∧
    ContDiff ℝ ∞ (fun point : Spatial => (weight sigma gamma (scale * ‖point‖) cell)⁻¹) :=
  smoothGoal sigma gamma scale cell

theorem allOrthogonalMaps : OrthogonalGoal := orthogonalGoal

theorem actualPhaseHasDerivative (sigma gamma scale : ℝ) (cell : ℤ) (point : Spatial) :
    HasFDerivAt (fun source : Spatial => phase sigma gamma (scale * ‖source‖) cell)
      (phaseGradient gamma scale cell point) point :=
  physicalPhase_hasFDerivAt sigma gamma scale cell point

theorem actualPhaseDerivative (sigma gamma scale : ℝ) (cell : ℤ) (point direction : Spatial) :
    fderiv ℝ (fun source : Spatial => phase sigma gamma (scale * ‖source‖) cell) point direction =
      (-gamma * scale ^ 2 * Grad.CellWeights.cellWeight cell ^ 2 / Real.sqrt (radicand scale cell point)) *
        inner ℝ point direction :=
  physicalPhase_fderiv_apply sigma gamma scale cell point direction

theorem actualPhaseHasSecondDerivative (sigma gamma scale : ℝ) (cell : ℤ) (point : Spatial) :
    HasFDerivAt (fderiv ℝ (fun source : Spatial => phase sigma gamma (scale * ‖source‖) cell))
      (phaseHessian gamma scale cell point) point :=
  physicalPhase_fderiv_hasFDerivAt sigma gamma scale cell point

theorem actualPhaseHessian (sigma gamma scale : ℝ) (cell : ℤ) (point first second : Spatial) :
    fderiv ℝ (fderiv ℝ (fun source : Spatial => phase sigma gamma (scale * ‖source‖) cell))
        point first second =
      (-gamma * scale ^ 2 * Grad.CellWeights.cellWeight cell ^ 2 / Real.sqrt (radicand scale cell point)) *
          inner ℝ first second +
        (gamma * scale ^ 4 * Grad.CellWeights.cellWeight cell ^ 4 / Real.sqrt (radicand scale cell point) ^ 3) *
          (inner ℝ point first * inner ℝ point second) :=
  physicalPhase_hessian_apply sigma gamma scale cell point first second

theorem actualIteratedHessian (sigma gamma scale : ℝ) (cell : ℤ) (point first second : Spatial) :
    iteratedFDeriv ℝ 2 (fun source : Spatial => phase sigma gamma (scale * ‖source‖) cell)
        point ![first, second] =
      (-gamma * scale ^ 2 * Grad.CellWeights.cellWeight cell ^ 2 / Real.sqrt (radicand scale cell point)) *
          inner ℝ first second +
        (gamma * scale ^ 4 * Grad.CellWeights.cellWeight cell ^ 4 / Real.sqrt (radicand scale cell point) ^ 3) *
          (inner ℝ point first * inner ℝ point second) :=
  physicalPhase_iteratedFDeriv_two sigma gamma scale cell point first second

theorem axisGradient (sigma gamma scale : ℝ) (cell : ℤ) :
    fderiv ℝ (fun source : Spatial => phase sigma gamma (scale * ‖source‖) cell) 0 = 0 :=
  physicalPhase_fderiv_axis sigma gamma scale cell

theorem axisHessian (sigma gamma scale : ℝ) (cell : ℤ) (first second : Spatial) :
    iteratedFDeriv ℝ 2 (fun source : Spatial => phase sigma gamma (scale * ‖source‖) cell) 0 ![first, second] =
      -gamma * scale ^ 2 * Grad.CellWeights.cellWeight cell ^ 2 * inner ℝ first second :=
  (axisGoal sigma gamma scale cell).2.2.2 first second

theorem actualWeightDerivative (sigma gamma scale : ℝ) (cell : ℤ) (point : Spatial) :
    HasFDerivAt (fun source : Spatial => weight sigma gamma (scale * ‖source‖) cell)
      (weight sigma gamma (scale * ‖point‖) cell • phaseGradient gamma scale cell point) point :=
  physicalWeight_hasFDerivAt sigma gamma scale cell point

theorem actualInverseDerivative (sigma gamma scale : ℝ) (cell : ℤ) (point : Spatial) :
    HasFDerivAt (fun source : Spatial => (weight sigma gamma (scale * ‖source‖) cell)⁻¹)
      (-(weight sigma gamma (scale * ‖point‖) cell)⁻¹ • phaseGradient gamma scale cell point) point :=
  inverseWeight_hasFDerivAt sigma gamma scale cell point

theorem actualWeightDirectionalFormulas : WeightDerivativeGoal := weightDerivativeGoal

theorem axisWeightValuesAndDerivatives : WeightAxisGoal := weightAxisGoal

theorem sharpFirstNorm (sigma gamma scale : ℝ) (cell : ℤ)
    (gammaNonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale) (point : Spatial) :
    ‖fderiv ℝ (fun source : Spatial => phase sigma gamma (scale * ‖source‖) cell) point‖ ≤
      gamma * scale * Grad.CellWeights.cellWeight cell :=
  firstNormGoal sigma gamma scale cell gammaNonnegative scaleNonnegative point

theorem zeroScaleAndCell : ZeroGoal := zeroGoal

end Grad.AnalyticWeights.Calculus.Consumer

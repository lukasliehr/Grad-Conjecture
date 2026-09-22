import AW1Phase
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

open Grad.PDEBootstrap
open scoped ContDiff RealInnerProductSpace

namespace Grad.AnalyticWeights.Calculus

def physicalPhase (sigma gamma scale : ℝ) (cell : ℤ) (point : Spatial) : ℝ :=
  phase sigma gamma (scale * ‖point‖) cell

def physicalWeight (sigma gamma scale : ℝ) (cell : ℤ) (point : Spatial) : ℝ :=
  weight sigma gamma (scale * ‖point‖) cell

def inverseWeight (sigma gamma scale : ℝ) (cell : ℤ) (point : Spatial) : ℝ :=
  (physicalWeight sigma gamma scale cell point)⁻¹

def radicand (scale : ℝ) (cell : ℤ) (point : Spatial) : ℝ :=
  1 + scale ^ 2 * ‖point‖ ^ 2 * Grad.CellWeights.cellWeight cell ^ 2

def phaseGradient (gamma scale : ℝ) (cell : ℤ) (point : Spatial) : Spatial →L[ℝ] ℝ :=
  (-gamma * scale ^ 2 * Grad.CellWeights.cellWeight cell ^ 2 / Real.sqrt (radicand scale cell point)) •
    innerSL ℝ point

def phaseHessian (gamma scale : ℝ) (cell : ℤ) (point : Spatial) :
    Spatial →L[ℝ] (Spatial →L[ℝ] ℝ) :=
  let bilinear : Spatial →L[ℝ] (Spatial →L[ℝ] ℝ) := innerSL ℝ
  (-gamma * scale ^ 2 * Grad.CellWeights.cellWeight cell ^ 2 / Real.sqrt (radicand scale cell point)) •
      bilinear +
    (gamma * scale ^ 4 * Grad.CellWeights.cellWeight cell ^ 4 / Real.sqrt (radicand scale cell point) ^ 3) •
      (innerSL ℝ point).smulRight (innerSL ℝ point)

def FormulaGoal : Prop :=
  ∀ (sigma gamma scale : ℝ) (cell : ℤ) (point : Spatial),
    0 < radicand scale cell point ∧
    physicalPhase sigma gamma scale cell point = sigma * Grad.CellWeights.cellWeight cell -
      gamma * (Real.sqrt (radicand scale cell point) - 1) ∧
    physicalWeight sigma gamma scale cell point = Real.exp (physicalPhase sigma gamma scale cell point) ∧
    inverseWeight sigma gamma scale cell point = Real.exp (-physicalPhase sigma gamma scale cell point) ∧
    physicalWeight sigma gamma scale cell point * inverseWeight sigma gamma scale cell point = 1

def SmoothGoal : Prop :=
  ∀ (sigma gamma scale : ℝ) (cell : ℤ),
    ContDiff ℝ ∞ (physicalPhase sigma gamma scale cell) ∧
    ContDiff ℝ ∞ (physicalWeight sigma gamma scale cell) ∧
    ContDiff ℝ ∞ (inverseWeight sigma gamma scale cell)

def OrthogonalGoal : Prop :=
  ∀ (sigma gamma scale : ℝ) (cell : ℤ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (point : Spatial),
    physicalPhase sigma gamma scale cell (orthogonal point) = physicalPhase sigma gamma scale cell point ∧
    physicalWeight sigma gamma scale cell (orthogonal point) = physicalWeight sigma gamma scale cell point ∧
    inverseWeight sigma gamma scale cell (orthogonal point) = inverseWeight sigma gamma scale cell point

def FirstGoal : Prop :=
  ∀ (sigma gamma scale : ℝ) (cell : ℤ) (point : Spatial),
    HasFDerivAt (physicalPhase sigma gamma scale cell) (phaseGradient gamma scale cell point) point ∧
    fderiv ℝ (physicalPhase sigma gamma scale cell) point = phaseGradient gamma scale cell point ∧
    (∀ direction : Spatial,
      fderiv ℝ (physicalPhase sigma gamma scale cell) point direction =
        (-gamma * scale ^ 2 * Grad.CellWeights.cellWeight cell ^ 2 / Real.sqrt (radicand scale cell point)) *
          inner ℝ point direction)

def HessianGoal : Prop :=
  ∀ (sigma gamma scale : ℝ) (cell : ℤ) (point : Spatial),
    HasFDerivAt (fderiv ℝ (physicalPhase sigma gamma scale cell)) (phaseHessian gamma scale cell point) point ∧
    fderiv ℝ (fderiv ℝ (physicalPhase sigma gamma scale cell)) point = phaseHessian gamma scale cell point ∧
    (∀ first second : Spatial,
      fderiv ℝ (fderiv ℝ (physicalPhase sigma gamma scale cell)) point first second =
        (-gamma * scale ^ 2 * Grad.CellWeights.cellWeight cell ^ 2 / Real.sqrt (radicand scale cell point)) *
            inner ℝ first second +
          (gamma * scale ^ 4 * Grad.CellWeights.cellWeight cell ^ 4 / Real.sqrt (radicand scale cell point) ^ 3) *
            (inner ℝ point first * inner ℝ point second)) ∧
    (∀ first second : Spatial,
      iteratedFDeriv ℝ 2 (physicalPhase sigma gamma scale cell) point ![first, second] =
        (-gamma * scale ^ 2 * Grad.CellWeights.cellWeight cell ^ 2 / Real.sqrt (radicand scale cell point)) *
            inner ℝ first second +
          (gamma * scale ^ 4 * Grad.CellWeights.cellWeight cell ^ 4 / Real.sqrt (radicand scale cell point) ^ 3) *
            (inner ℝ point first * inner ℝ point second))

def AxisGoal : Prop :=
  ∀ (sigma gamma scale : ℝ) (cell : ℤ),
    physicalPhase sigma gamma scale cell 0 = sigma * Grad.CellWeights.cellWeight cell ∧
    fderiv ℝ (physicalPhase sigma gamma scale cell) 0 = 0 ∧
    (∀ first second : Spatial,
      fderiv ℝ (fderiv ℝ (physicalPhase sigma gamma scale cell)) 0 first second =
        -gamma * scale ^ 2 * Grad.CellWeights.cellWeight cell ^ 2 * inner ℝ first second) ∧
    (∀ first second : Spatial,
      iteratedFDeriv ℝ 2 (physicalPhase sigma gamma scale cell) 0 ![first, second] =
        -gamma * scale ^ 2 * Grad.CellWeights.cellWeight cell ^ 2 * inner ℝ first second)

def WeightDerivativeGoal : Prop :=
  ∀ (sigma gamma scale : ℝ) (cell : ℤ) (point : Spatial),
    HasFDerivAt (physicalWeight sigma gamma scale cell)
      (physicalWeight sigma gamma scale cell point • phaseGradient gamma scale cell point) point ∧
    HasFDerivAt (inverseWeight sigma gamma scale cell)
      (-inverseWeight sigma gamma scale cell point • phaseGradient gamma scale cell point) point ∧
    (∀ direction : Spatial,
      fderiv ℝ (physicalWeight sigma gamma scale cell) point direction =
        physicalWeight sigma gamma scale cell point *
          ((-gamma * scale ^ 2 * Grad.CellWeights.cellWeight cell ^ 2 / Real.sqrt (radicand scale cell point)) *
            inner ℝ point direction)) ∧
    (∀ direction : Spatial,
      fderiv ℝ (inverseWeight sigma gamma scale cell) point direction =
        inverseWeight sigma gamma scale cell point *
          ((gamma * scale ^ 2 * Grad.CellWeights.cellWeight cell ^ 2 / Real.sqrt (radicand scale cell point)) *
            inner ℝ point direction))

def WeightAxisGoal : Prop :=
  ∀ (sigma gamma scale : ℝ) (cell : ℤ),
    physicalWeight sigma gamma scale cell 0 = Real.exp (sigma * Grad.CellWeights.cellWeight cell) ∧
    inverseWeight sigma gamma scale cell 0 = Real.exp (-sigma * Grad.CellWeights.cellWeight cell) ∧
    fderiv ℝ (physicalWeight sigma gamma scale cell) 0 = 0 ∧
    fderiv ℝ (inverseWeight sigma gamma scale cell) 0 = 0

def FirstNormGoal : Prop :=
  ∀ (sigma gamma scale : ℝ) (cell : ℤ), 0 ≤ gamma → 0 ≤ scale → ∀ point : Spatial,
    ‖fderiv ℝ (physicalPhase sigma gamma scale cell) point‖ ≤ gamma * scale * Grad.CellWeights.cellWeight cell

def ZeroGoal : Prop :=
  (∀ (sigma gamma : ℝ) (cell : ℤ) (point : Spatial),
    physicalPhase sigma gamma 0 cell point = sigma * Grad.CellWeights.cellWeight cell ∧
    fderiv ℝ (physicalPhase sigma gamma 0 cell) point = 0 ∧
    fderiv ℝ (fderiv ℝ (physicalPhase sigma gamma 0 cell)) point = 0 ∧
    physicalWeight sigma gamma 0 cell point = Real.exp (sigma * Grad.CellWeights.cellWeight cell) ∧
    inverseWeight sigma gamma 0 cell point = Real.exp (-sigma * Grad.CellWeights.cellWeight cell)) ∧
  (∀ (sigma gamma scale : ℝ) (point : Spatial),
    physicalPhase sigma gamma scale 0 point = sigma - gamma * (Real.sqrt (1 + scale ^ 2 * ‖point‖ ^ 2) - 1))

def BlockGoal : Prop :=
  FormulaGoal ∧ SmoothGoal ∧ OrthogonalGoal ∧ FirstGoal ∧ HessianGoal ∧ AxisGoal ∧
    WeightDerivativeGoal ∧ WeightAxisGoal ∧ FirstNormGoal ∧ ZeroGoal

end Grad.AnalyticWeights.Calculus

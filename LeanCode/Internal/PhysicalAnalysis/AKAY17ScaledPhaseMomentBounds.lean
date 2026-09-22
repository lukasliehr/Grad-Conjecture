import AKAY16ScaledActualPhaseDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

open Set MeasureTheory

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.RepresentedKernel.SpatialProduct Grad.AnalyticWeights.Calculus Grad.AnalyticWeights.Higher

/-- Exact original analytic profile under the physical dilation; no width is changed. -/
theorem startupPhysicalWeight_dilation (sigma gamma scale : ℝ) (nonnegative : 0 ≤ scale)
    (cell : ℤ) (point : Spatial) :
    physicalWeight sigma gamma scale cell point = physicalWeight sigma gamma 1 cell (scale • point) := by
  simp only [physicalWeight, norm_smul, Real.norm_eq_abs, abs_of_nonneg nonnegative, one_mul]

theorem startupScaledPhaseSlope_bound (sigma gamma scale : ℝ) (nonnegative : 0 ≤ gamma)
    (scaleNonnegative : 0 ≤ scale) (scaleOne : scale ≤ 1)
    (cell : ℤ) (direction : Fin 2) (point : Spatial) :
    |startupScaledPhaseSlope sigma gamma scale cell direction point| ≤ gamma * Grad.CellWeights.cellWeight cell := by
  change ‖fderiv ℝ (physicalPhase sigma gamma scale cell) point (spatialDirection direction)‖ ≤ _
  apply ((fderiv ℝ (physicalPhase sigma gamma scale cell) point).le_opNorm _).trans
  rw [direction_norm, mul_one]
  apply (firstNormGoal sigma gamma scale cell nonnegative scaleNonnegative point).trans
  exact mul_le_mul_of_nonneg_right (by nlinarith : gamma * scale ≤ gamma)
    (Grad.CellWeights.cellWeight_pos cell).le

theorem startupScaledPhaseSlope_derivative_bound (sigma gamma scale : ℝ) (nonnegative : 0 ≤ gamma)
    (scaleNonnegative : 0 ≤ scale) (scaleOne : scale ≤ 1)
    (cell : ℤ) (outer inner : Fin 2) (point : Spatial) :
    |directionDerivative outer (startupScaledPhaseSlope sigma gamma scale cell inner) point| ≤
      profileConstant 2 * gamma * Grad.CellWeights.cellWeight cell ^ 2 := by
  have identity := listDerivative_ofFn isOpen_univ 2 ![outer, inner]
    (physicalPhase_contDiff sigma gamma scale cell).contDiffOn (mem_univ point)
  change directionDerivative outer (directionDerivative inner (physicalPhase sigma gamma scale cell)) point =
    wordDerivative 2 ![outer, inner] (physicalPhase sigma gamma scale cell) point at identity
  rw [startupScaledPhaseSlope, identity]
  apply (orderedDerivative_norm_le 2 ![outer, inner] (physicalPhase sigma gamma scale cell) point).trans
  apply (physicalPhase_iterated_norm_bound sigma gamma scale cell nonnegative scaleNonnegative 2 (by norm_num) point).trans
  have squared : scale ^ 2 ≤ 1 := by nlinarith
  have coefficient : 0 ≤ profileConstant 2 * gamma := mul_nonneg (profileConstant_nonnegative 2) nonnegative
  exact mul_le_mul_of_nonneg_right (by nlinarith : profileConstant 2 * gamma * scale ^ 2 ≤ profileConstant 2 * gamma)
    (sq_nonneg (Grad.CellWeights.cellWeight cell))

theorem startupScaledPhaseSecond_bound (sigma gamma scale : ℝ) (nonnegative : 0 ≤ gamma)
    (scaleNonnegative : 0 ≤ scale) (scaleOne : scale ≤ 1)
    (cell : ℤ) (outer inner : Fin 2) (point : Spatial) :
    |startupScaledPhaseSecond sigma gamma scale cell outer inner point| ≤
      (profileConstant 2 * gamma + gamma ^ 2) * Grad.CellWeights.cellWeight cell ^ 2 := by
  unfold startupScaledPhaseSecond
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  apply (add_le_add (startupScaledPhaseSlope_derivative_bound sigma gamma scale nonnegative scaleNonnegative scaleOne cell outer inner point)
    (mul_le_mul (startupScaledPhaseSlope_bound sigma gamma scale nonnegative scaleNonnegative scaleOne cell outer point)
      (startupScaledPhaseSlope_bound sigma gamma scale nonnegative scaleNonnegative scaleOne cell inner point)
      (abs_nonneg _) (mul_nonneg nonnegative (Grad.CellWeights.cellWeight_pos cell).le))).trans_eq
  ring

theorem startupScaledPhaseSlope_normalized_bound (sigma gamma scale : ℝ) (nonnegative : 0 ≤ gamma)
    (scaleNonnegative : 0 ≤ scale) (scaleOne : scale ≤ 1)
    (cell : ℤ) (direction : Fin 2) (point : Spatial) :
    |startupScaledPhaseSlope sigma gamma scale cell direction point / Grad.CellWeights.cellWeight cell| ≤ gamma := by
  rw [abs_div, abs_of_pos (Grad.CellWeights.cellWeight_pos cell), div_le_iff₀ (Grad.CellWeights.cellWeight_pos cell)]
  exact startupScaledPhaseSlope_bound sigma gamma scale nonnegative scaleNonnegative scaleOne cell direction point

theorem startupScaledPhaseSecond_normalized_bound (sigma gamma scale : ℝ) (nonnegative : 0 ≤ gamma)
    (scaleNonnegative : 0 ≤ scale) (scaleOne : scale ≤ 1)
    (cell : ℤ) (outer inner : Fin 2) (point : Spatial) :
    |startupScaledPhaseSecond sigma gamma scale cell outer inner point / Grad.CellWeights.cellWeight cell ^ 2| ≤
      profileConstant 2 * gamma + gamma ^ 2 := by
  rw [abs_div, abs_of_pos (pow_pos (Grad.CellWeights.cellWeight_pos cell) _),
    div_le_iff₀ (pow_pos (Grad.CellWeights.cellWeight_pos cell) _)]
  exact startupScaledPhaseSecond_bound sigma gamma scale nonnegative scaleNonnegative scaleOne cell outer inner point

end Grad.CartesianStartup

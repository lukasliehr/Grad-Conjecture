import AKAY2ActualPhaseTestDerivatives
import AW3Phase

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

open Set MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.RepresentedKernel.SpatialProduct Grad.AnalyticWeights.Calculus Grad.AnalyticWeights.Higher

theorem startupPhaseSlope_bound (sigma gamma : ℝ) (nonnegative : 0 ≤ gamma)
    (cell : ℤ) (direction : Fin 2) (point : Spatial) :
    |startupPhaseSlope sigma gamma cell direction point| ≤ gamma * Grad.CellWeights.cellWeight cell := by
  change ‖fderiv ℝ (physicalPhase sigma gamma 1 cell) point (spatialDirection direction)‖ ≤ _
  exact ((fderiv ℝ (physicalPhase sigma gamma 1 cell) point).le_opNorm _).trans
    (by simpa only [direction_norm, mul_one] using firstNormGoal sigma gamma 1 cell nonnegative zero_le_one point)

theorem startupPhaseSlope_derivative_bound (sigma gamma : ℝ) (nonnegative : 0 ≤ gamma)
    (cell : ℤ) (outer inner : Fin 2) (point : Spatial) :
    |directionDerivative outer (startupPhaseSlope sigma gamma cell inner) point| ≤
      profileConstant 2 * gamma * Grad.CellWeights.cellWeight cell ^ 2 := by
  have identity := listDerivative_ofFn isOpen_univ 2 ![outer, inner]
    (physicalPhase_contDiff sigma gamma 1 cell).contDiffOn (mem_univ point)
  change directionDerivative outer (directionDerivative inner (physicalPhase sigma gamma 1 cell)) point =
    wordDerivative 2 ![outer, inner] (physicalPhase sigma gamma 1 cell) point at identity
  rw [startupPhaseSlope, identity]
  exact (orderedDerivative_norm_le 2 ![outer, inner] (physicalPhase sigma gamma 1 cell) point).trans
    (by simpa only [one_pow, mul_one] using
      physicalPhase_iterated_norm_bound sigma gamma 1 cell nonnegative zero_le_one 2 (by norm_num) point)

theorem startupPhaseSecond_bound (sigma gamma : ℝ) (nonnegative : 0 ≤ gamma)
    (cell : ℤ) (outer inner : Fin 2) (point : Spatial) :
    |startupPhaseSecond sigma gamma cell outer inner point| ≤
      (profileConstant 2 * gamma + gamma ^ 2) * Grad.CellWeights.cellWeight cell ^ 2 := by
  unfold startupPhaseSecond
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  apply (add_le_add (startupPhaseSlope_derivative_bound sigma gamma nonnegative cell outer inner point)
    (mul_le_mul (startupPhaseSlope_bound sigma gamma nonnegative cell outer point)
      (startupPhaseSlope_bound sigma gamma nonnegative cell inner point)
      (abs_nonneg _) (mul_nonneg nonnegative (Grad.CellWeights.cellWeight_pos cell).le))).trans_eq
  ring

/-- Dividing by the native first cell moment makes the actual phase slope uniformly bounded. -/
theorem startupPhaseSlope_normalized_bound (sigma gamma : ℝ) (nonnegative : 0 ≤ gamma)
    (cell : ℤ) (direction : Fin 2) (point : Spatial) :
    |startupPhaseSlope sigma gamma cell direction point / Grad.CellWeights.cellWeight cell| ≤ gamma := by
  rw [abs_div, abs_of_pos (Grad.CellWeights.cellWeight_pos cell), div_le_iff₀ (Grad.CellWeights.cellWeight_pos cell)]
  exact startupPhaseSlope_bound sigma gamma nonnegative cell direction point

/-- The native second cell moment pays for every second-order phase remainder. -/
theorem startupPhaseSecond_normalized_bound (sigma gamma : ℝ) (nonnegative : 0 ≤ gamma)
    (cell : ℤ) (outer inner : Fin 2) (point : Spatial) :
    |startupPhaseSecond sigma gamma cell outer inner point / Grad.CellWeights.cellWeight cell ^ 2| ≤
      profileConstant 2 * gamma + gamma ^ 2 := by
  rw [abs_div, abs_of_pos (pow_pos (Grad.CellWeights.cellWeight_pos cell) _),
    div_le_iff₀ (pow_pos (Grad.CellWeights.cellWeight_pos cell) _)]
  exact startupPhaseSecond_bound sigma gamma nonnegative cell outer inner point

end Grad.CartesianStartup

import AKAY17ScaledPhaseMomentBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000

open Set MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.AnalyticWeights.Higher

def startupScaledPhaseFirstField (sigma gamma scale : ℝ) (nonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale) (scaleOne : scale ≤ 1) (direction : Fin 2)
    (moment : StartupL2 3) : StartupL2 3 :=
  startupCellDiagonalField (fun cell point => startupScaledPhaseSlope sigma gamma scale cell direction point / Grad.CellWeights.cellWeight cell)
    gamma nonnegative (fun cell point => startupScaledPhaseSlope_normalized_bound sigma gamma scale nonnegative scaleNonnegative scaleOne cell direction point)
    (fun cell => ((startupScaledPhaseSlope_smooth sigma gamma scale cell direction).div_const _).continuous.aestronglyMeasurable) moment

def startupScaledPhaseSecondField (sigma gamma scale : ℝ) (nonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale) (scaleOne : scale ≤ 1) (outer inner : Fin 2)
    (moment : StartupL2 3) : StartupL2 3 :=
  startupCellDiagonalField (fun cell point => startupScaledPhaseSecond sigma gamma scale cell outer inner point / Grad.CellWeights.cellWeight cell ^ 2)
    (profileConstant 2 * gamma + gamma ^ 2)
    (add_nonneg (mul_nonneg (profileConstant_nonnegative 2) nonnegative) (sq_nonneg gamma))
    (fun cell point => startupScaledPhaseSecond_normalized_bound sigma gamma scale nonnegative scaleNonnegative scaleOne cell outer inner point)
    (fun cell => ((startupScaledPhaseSecond_smooth sigma gamma scale cell outer inner).div_const _).continuous.aestronglyMeasurable) moment

theorem startupScaledPhaseFirstField_norm (sigma gamma scale : ℝ) (nonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale) (scaleOne : scale ≤ 1) (direction : Fin 2)
    (moment : StartupL2 3) : ‖startupScaledPhaseFirstField sigma gamma scale nonnegative scaleNonnegative scaleOne direction moment‖ ≤ gamma * ‖moment‖ :=
  startupCellDiagonalField_norm _ _ _ _ _ _

theorem startupScaledPhaseSecondField_norm (sigma gamma scale : ℝ) (nonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale) (scaleOne : scale ≤ 1) (outer inner : Fin 2)
    (moment : StartupL2 3) :
    ‖startupScaledPhaseSecondField sigma gamma scale nonnegative scaleNonnegative scaleOne outer inner moment‖ ≤
      (profileConstant 2 * gamma + gamma ^ 2) * ‖moment‖ :=
  startupCellDiagonalField_norm _ _ _ _ _ _

private theorem normalizedMoment_cancel (scalar frequency : ℝ) (nonzero : frequency ≠ 0)
    (value : PhysicalValue 3) :
    ((scalar / frequency : ℝ) : ℂ) • (frequency • value) = scalar • value := by
  rw [Complex.coe_smul, smul_smul, div_mul_cancel₀ _ nonzero]

theorem startupScaledPhaseFirstField_same (sigma gamma scale : ℝ) (nonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale) (scaleOne : scale ≤ 1) (direction : Fin 2)
    (field moment : StartupL2 3)
    (sameMoment : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      moment point cell = Grad.CellWeights.cellWeight cell • field point cell) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      startupScaledPhaseFirstField sigma gamma scale nonnegative scaleNonnegative scaleOne direction moment point cell =
        startupScaledPhaseSlope sigma gamma scale cell direction point • field point cell := by
  have diagonal := startupCellDiagonalField_ae
    (fun cell point => startupScaledPhaseSlope sigma gamma scale cell direction point / Grad.CellWeights.cellWeight cell)
    gamma nonnegative (fun cell point => startupScaledPhaseSlope_normalized_bound sigma gamma scale nonnegative scaleNonnegative scaleOne cell direction point)
    (fun cell => ((startupScaledPhaseSlope_smooth sigma gamma scale cell direction).div_const _).continuous.aestronglyMeasurable) moment
  filter_upwards [diagonal, sameMoment] with point formula momentFormula
  intro cell
  change startupCellDiagonalField _ _ _ _ _ moment point cell = _
  rw [formula cell, momentFormula cell]
  exact normalizedMoment_cancel _ _ (Grad.CellWeights.cellWeight_pos cell).ne' _

theorem startupScaledPhaseSecondField_same (sigma gamma scale : ℝ) (nonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale) (scaleOne : scale ≤ 1) (outer inner : Fin 2)
    (field moment : StartupL2 3)
    (sameMoment : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      moment point cell = Grad.CellWeights.cellWeight cell ^ 2 • field point cell) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      startupScaledPhaseSecondField sigma gamma scale nonnegative scaleNonnegative scaleOne outer inner moment point cell =
        startupScaledPhaseSecond sigma gamma scale cell outer inner point • field point cell := by
  have diagonal := startupCellDiagonalField_ae
    (fun cell point => startupScaledPhaseSecond sigma gamma scale cell outer inner point / Grad.CellWeights.cellWeight cell ^ 2)
    (profileConstant 2 * gamma + gamma ^ 2)
    (add_nonneg (mul_nonneg (profileConstant_nonnegative 2) nonnegative) (sq_nonneg gamma))
    (fun cell point => startupScaledPhaseSecond_normalized_bound sigma gamma scale nonnegative scaleNonnegative scaleOne cell outer inner point)
    (fun cell => ((startupScaledPhaseSecond_smooth sigma gamma scale cell outer inner).div_const _).continuous.aestronglyMeasurable) moment
  filter_upwards [diagonal, sameMoment] with point formula momentFormula
  intro cell
  change startupCellDiagonalField _ _ _ _ _ moment point cell = _
  rw [formula cell, momentFormula cell]
  exact normalizedMoment_cancel _ _ (pow_ne_zero _ (Grad.CellWeights.cellWeight_pos cell).ne') _

end Grad.CartesianStartup

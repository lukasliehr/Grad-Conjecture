import AKAY9BoundedCellDiagonalField

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000

open Set MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.AnalyticWeights.Higher

theorem startupCellDiagonalField_norm (symbol : ℤ → Spatial → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ cell point, |symbol cell point| ≤ constant)
    (measurable : ∀ cell, AEStronglyMeasurable (symbol cell) (volume.restrict openUnitDisk)) (field : StartupL2 3) :
    ‖startupCellDiagonalField symbol constant nonnegative bounded measurable field‖ ≤ constant * ‖field‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(startupCellDiagonalValue_memLp symbol constant nonnegative bounded measurable field).coeFn_toLp]
    with point same
  change startupCellDiagonalField symbol constant nonnegative bounded measurable field point =
    startupCellDiagonalValue symbol constant nonnegative bounded field point at same
  rw [same]
  exact startupCellDiagonalValue_bound symbol constant nonnegative bounded field point

def startupPhaseFirstField (sigma gamma : ℝ) (nonnegative : 0 ≤ gamma) (direction : Fin 2)
    (moment : StartupL2 3) : StartupL2 3 :=
  startupCellDiagonalField (fun cell point => startupPhaseSlope sigma gamma cell direction point / Grad.CellWeights.cellWeight cell)
    gamma nonnegative (fun cell point => startupPhaseSlope_normalized_bound sigma gamma nonnegative cell direction point)
    (fun cell => ((startupPhaseSlope_smooth sigma gamma cell direction).div_const _).continuous.aestronglyMeasurable) moment

def startupPhaseSecondField (sigma gamma : ℝ) (nonnegative : 0 ≤ gamma) (outer inner : Fin 2)
    (moment : StartupL2 3) : StartupL2 3 :=
  startupCellDiagonalField (fun cell point => startupPhaseSecond sigma gamma cell outer inner point / Grad.CellWeights.cellWeight cell ^ 2)
    (profileConstant 2 * gamma + gamma ^ 2)
    (add_nonneg (mul_nonneg (profileConstant_nonnegative 2) nonnegative) (sq_nonneg gamma))
    (fun cell point => startupPhaseSecond_normalized_bound sigma gamma nonnegative cell outer inner point)
    (fun cell => ((startupPhaseSecond_smooth sigma gamma cell outer inner).div_const _).continuous.aestronglyMeasurable) moment

theorem startupPhaseFirstField_norm (sigma gamma : ℝ) (nonnegative : 0 ≤ gamma) (direction : Fin 2)
    (moment : StartupL2 3) : ‖startupPhaseFirstField sigma gamma nonnegative direction moment‖ ≤ gamma * ‖moment‖ :=
  startupCellDiagonalField_norm _ _ _ _ _ _

theorem startupPhaseSecondField_norm (sigma gamma : ℝ) (nonnegative : 0 ≤ gamma) (outer inner : Fin 2)
    (moment : StartupL2 3) :
    ‖startupPhaseSecondField sigma gamma nonnegative outer inner moment‖ ≤
      (profileConstant 2 * gamma + gamma ^ 2) * ‖moment‖ :=
  startupCellDiagonalField_norm _ _ _ _ _ _

private theorem normalizedMoment_cancel (scalar frequency : ℝ) (nonzero : frequency ≠ 0)
    (value : PhysicalValue 3) :
    ((scalar / frequency : ℝ) : ℂ) • (frequency • value) = scalar • value := by
  rw [Complex.coe_smul, smul_smul, div_mul_cancel₀ _ nonzero]

theorem startupPhaseFirstField_same (sigma gamma : ℝ) (nonnegative : 0 ≤ gamma) (direction : Fin 2)
    (field moment : StartupL2 3)
    (sameMoment : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      moment point cell = Grad.CellWeights.cellWeight cell • field point cell) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      startupPhaseFirstField sigma gamma nonnegative direction moment point cell =
        startupPhaseSlope sigma gamma cell direction point • field point cell := by
  have diagonal := startupCellDiagonalField_ae
    (fun cell point => startupPhaseSlope sigma gamma cell direction point / Grad.CellWeights.cellWeight cell)
    gamma nonnegative (fun cell point => startupPhaseSlope_normalized_bound sigma gamma nonnegative cell direction point)
    (fun cell => ((startupPhaseSlope_smooth sigma gamma cell direction).div_const _).continuous.aestronglyMeasurable) moment
  filter_upwards [diagonal, sameMoment] with point formula momentFormula
  intro cell
  change startupCellDiagonalField _ _ _ _ _ moment point cell = _
  rw [formula cell, momentFormula cell]
  exact normalizedMoment_cancel _ _ (Grad.CellWeights.cellWeight_pos cell).ne' _

theorem startupPhaseSecondField_same (sigma gamma : ℝ) (nonnegative : 0 ≤ gamma) (outer inner : Fin 2)
    (field moment : StartupL2 3)
    (sameMoment : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      moment point cell = Grad.CellWeights.cellWeight cell ^ 2 • field point cell) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      startupPhaseSecondField sigma gamma nonnegative outer inner moment point cell =
        startupPhaseSecond sigma gamma cell outer inner point • field point cell := by
  have diagonal := startupCellDiagonalField_ae
    (fun cell point => startupPhaseSecond sigma gamma cell outer inner point / Grad.CellWeights.cellWeight cell ^ 2)
    (profileConstant 2 * gamma + gamma ^ 2)
    (add_nonneg (mul_nonneg (profileConstant_nonnegative 2) nonnegative) (sq_nonneg gamma))
    (fun cell point => startupPhaseSecond_normalized_bound sigma gamma nonnegative cell outer inner point)
    (fun cell => ((startupPhaseSecond_smooth sigma gamma cell outer inner).div_const _).continuous.aestronglyMeasurable) moment
  filter_upwards [diagonal, sameMoment] with point formula momentFormula
  intro cell
  change startupCellDiagonalField _ _ _ _ _ moment point cell = _
  rw [formula cell, momentFormula cell]
  exact normalizedMoment_cancel _ _ (pow_ne_zero _ (Grad.CellWeights.cellWeight_pos cell).ne') _

end Grad.CartesianStartup

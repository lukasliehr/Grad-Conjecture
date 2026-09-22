import AKAY8SameRoughAngularRecovery
import AKAW3JointCellRepresentative
import AAT1RealFourierDiagonal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000

open Set MeasureTheory

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.AnnularGrades Grad.ActualNativeCellMoments

/-- Pointwise bounded diagonal action; no operator-norm continuity at the axis is assumed. -/
def startupCellDiagonalValue (symbol : ℤ → Spatial → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ cell point, |symbol cell point| ≤ constant) (field : StartupL2 3) (point : Spatial) :
    Grad.GenericCarriers.CellValues 3 :=
  realLpDiagonal (fun cell => symbol cell point) constant nonnegative (fun cell => bounded cell point) (field point)

theorem startupCellDiagonalValue_apply (symbol : ℤ → Spatial → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ cell point, |symbol cell point| ≤ constant) (field : StartupL2 3) (point : Spatial) (cell : ℤ) :
    startupCellDiagonalValue symbol constant nonnegative bounded field point cell =
      (symbol cell point : ℂ) • field point cell := rfl

theorem startupCellDiagonalValue_bound (symbol : ℤ → Spatial → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ cell point, |symbol cell point| ≤ constant) (field : StartupL2 3) (point : Spatial) :
    ‖startupCellDiagonalValue symbol constant nonnegative bounded field point‖ ≤ constant * ‖field point‖ :=
  realLpDiagonal_bound _ constant nonnegative _ (field point)

theorem startupCellDiagonalValue_measurable (symbol : ℤ → Spatial → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ cell point, |symbol cell point| ≤ constant)
    (measurable : ∀ cell, AEStronglyMeasurable (symbol cell) (volume.restrict openUnitDisk)) (field : StartupL2 3) :
    AEStronglyMeasurable (startupCellDiagonalValue symbol constant nonnegative bounded field) (volume.restrict openUnitDisk) := by
  have coordinates (cell : ℤ) : AEStronglyMeasurable (fun point => (symbol cell point : ℂ) • field point cell)
      (volume.restrict openUnitDisk) :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable (measurable cell)).smul
      ((lp.evalCLM ℂ (fun _ : ℤ => PhysicalValue 3) 2 cell).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable field))
  have joined := jointCellRepresentative_aestronglyMeasurable (volume.restrict openUnitDisk)
    (fun cell point => (symbol cell point : ℂ) • field point cell) coordinates
  have same : jointCellRepresentative (fun cell point => (symbol cell point : ℂ) • field point cell) =
      startupCellDiagonalValue symbol constant nonnegative bounded field := by
    funext point
    apply lp.ext
    funext cell
    have coordinatesSame : (fun index => (symbol index point : ℂ) • field point index) =
        (fun index => startupCellDiagonalValue symbol constant nonnegative bounded field point index) :=
      funext (fun index => (startupCellDiagonalValue_apply symbol constant nonnegative bounded field point index).symm)
    have member : Memℓp (fun index => (symbol index point : ℂ) • field point index) 2 := by
      rw [coordinatesSame]
      exact (startupCellDiagonalValue symbol constant nonnegative bounded field point).property
    exact (jointCellRepresentative_same (fun index source => (symbol index source : ℂ) • field source index)
      point member cell).trans (startupCellDiagonalValue_apply symbol constant nonnegative bounded field point cell).symm
  rw [same] at joined
  exact joined

theorem startupCellDiagonalValue_memLp (symbol : ℤ → Spatial → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ cell point, |symbol cell point| ≤ constant)
    (measurable : ∀ cell, AEStronglyMeasurable (symbol cell) (volume.restrict openUnitDisk)) (field : StartupL2 3) :
    MemLp (startupCellDiagonalValue symbol constant nonnegative bounded field) 2 (volume.restrict openUnitDisk) := by
  apply (Lp.memLp field).of_le_mul (c := constant)
    (startupCellDiagonalValue_measurable symbol constant nonnegative bounded measurable field)
  exact Filter.Eventually.of_forall (startupCellDiagonalValue_bound symbol constant nonnegative bounded field)

def startupCellDiagonalField (symbol : ℤ → Spatial → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ cell point, |symbol cell point| ≤ constant)
    (measurable : ∀ cell, AEStronglyMeasurable (symbol cell) (volume.restrict openUnitDisk)) (field : StartupL2 3) :
    StartupL2 3 :=
  (startupCellDiagonalValue_memLp symbol constant nonnegative bounded measurable field).toLp _

theorem startupCellDiagonalField_ae (symbol : ℤ → Spatial → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ cell point, |symbol cell point| ≤ constant)
    (measurable : ∀ cell, AEStronglyMeasurable (symbol cell) (volume.restrict openUnitDisk)) (field : StartupL2 3) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      startupCellDiagonalField symbol constant nonnegative bounded measurable field point cell =
        (symbol cell point : ℂ) • field point cell := by
  filter_upwards [(startupCellDiagonalValue_memLp symbol constant nonnegative bounded measurable field).coeFn_toLp] with point same
  intro cell
  exact congrArg (fun value : Grad.GenericCarriers.CellValues 3 => value cell) same

end Grad.CartesianStartup

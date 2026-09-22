import AKBF14SameNativeXiMean

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000

open Set MeasureTheory

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.AnnularGrades Grad.ActualNativeCellMoments

/-- Pointwise bounded diagonal action; no operator-norm continuity at the axis is assumed. -/
def startupMomentDiagonalValue {dimension : ℕ} (symbol : ℤ → Spatial → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ cell point, |symbol cell point| ≤ constant) (field : StartupL2 dimension) (point : Spatial) :
    Grad.GenericCarriers.CellValues dimension :=
  realLpDiagonal (fun cell => symbol cell point) constant nonnegative (fun cell => bounded cell point) (field point)

theorem startupMomentDiagonalValue_apply {dimension : ℕ} (symbol : ℤ → Spatial → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ cell point, |symbol cell point| ≤ constant) (field : StartupL2 dimension) (point : Spatial) (cell : ℤ) :
    startupMomentDiagonalValue symbol constant nonnegative bounded field point cell =
      (symbol cell point : ℂ) • field point cell := rfl

theorem startupMomentDiagonalValue_bound {dimension : ℕ} (symbol : ℤ → Spatial → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ cell point, |symbol cell point| ≤ constant) (field : StartupL2 dimension) (point : Spatial) :
    ‖startupMomentDiagonalValue symbol constant nonnegative bounded field point‖ ≤ constant * ‖field point‖ :=
  realLpDiagonal_bound _ constant nonnegative _ (field point)

theorem startupMomentDiagonalValue_measurable {dimension : ℕ} (symbol : ℤ → Spatial → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ cell point, |symbol cell point| ≤ constant)
    (measurable : ∀ cell, AEStronglyMeasurable (symbol cell) (volume.restrict openUnitDisk)) (field : StartupL2 dimension) :
    AEStronglyMeasurable (startupMomentDiagonalValue symbol constant nonnegative bounded field) (volume.restrict openUnitDisk) := by
  have coordinates (cell : ℤ) : AEStronglyMeasurable (fun point => (symbol cell point : ℂ) • field point cell)
      (volume.restrict openUnitDisk) :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable (measurable cell)).smul
      ((lp.evalCLM ℂ (fun _ : ℤ => PhysicalValue dimension) 2 cell).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable field))
  have joined := jointCellRepresentative_aestronglyMeasurable (volume.restrict openUnitDisk)
    (fun cell point => (symbol cell point : ℂ) • field point cell) coordinates
  have same : jointCellRepresentative (fun cell point => (symbol cell point : ℂ) • field point cell) =
      startupMomentDiagonalValue symbol constant nonnegative bounded field := by
    funext point
    apply lp.ext
    funext cell
    have coordinatesSame : (fun index => (symbol index point : ℂ) • field point index) =
        (fun index => startupMomentDiagonalValue symbol constant nonnegative bounded field point index) :=
      funext (fun index => (startupMomentDiagonalValue_apply symbol constant nonnegative bounded field point index).symm)
    have member : Memℓp (fun index => (symbol index point : ℂ) • field point index) 2 := by
      rw [coordinatesSame]
      exact (startupMomentDiagonalValue symbol constant nonnegative bounded field point).property
    exact (jointCellRepresentative_same (fun index source => (symbol index source : ℂ) • field source index)
      point member cell).trans (startupMomentDiagonalValue_apply symbol constant nonnegative bounded field point cell).symm
  rw [same] at joined
  exact joined

theorem startupMomentDiagonalValue_memLp {dimension : ℕ} (symbol : ℤ → Spatial → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ cell point, |symbol cell point| ≤ constant)
    (measurable : ∀ cell, AEStronglyMeasurable (symbol cell) (volume.restrict openUnitDisk)) (field : StartupL2 dimension) :
    MemLp (startupMomentDiagonalValue symbol constant nonnegative bounded field) 2 (volume.restrict openUnitDisk) := by
  apply (Lp.memLp field).of_le_mul (c := constant)
    (startupMomentDiagonalValue_measurable symbol constant nonnegative bounded measurable field)
  exact Filter.Eventually.of_forall (startupMomentDiagonalValue_bound symbol constant nonnegative bounded field)

def startupMomentDiagonalField {dimension : ℕ} (symbol : ℤ → Spatial → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ cell point, |symbol cell point| ≤ constant)
    (measurable : ∀ cell, AEStronglyMeasurable (symbol cell) (volume.restrict openUnitDisk)) (field : StartupL2 dimension) :
    StartupL2 dimension :=
  (startupMomentDiagonalValue_memLp symbol constant nonnegative bounded measurable field).toLp _

theorem startupMomentDiagonalField_ae {dimension : ℕ} (symbol : ℤ → Spatial → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ cell point, |symbol cell point| ≤ constant)
    (measurable : ∀ cell, AEStronglyMeasurable (symbol cell) (volume.restrict openUnitDisk)) (field : StartupL2 dimension) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      startupMomentDiagonalField symbol constant nonnegative bounded measurable field point cell =
        (symbol cell point : ℂ) • field point cell := by
  filter_upwards [(startupMomentDiagonalValue_memLp symbol constant nonnegative bounded measurable field).coeFn_toLp] with point same
  intro cell
  exact congrArg (fun value : Grad.GenericCarriers.CellValues dimension => value cell) same

theorem startupMomentDiagonalField_norm {dimension : ℕ} (symbol : ℤ → Spatial → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ cell point, |symbol cell point| ≤ constant)
    (measurable : ∀ cell, AEStronglyMeasurable (symbol cell) (volume.restrict openUnitDisk)) (field : StartupL2 dimension) :
    ‖startupMomentDiagonalField symbol constant nonnegative bounded measurable field‖ ≤ constant * ‖field‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(startupMomentDiagonalValue_memLp symbol constant nonnegative bounded measurable field).coeFn_toLp]
    with point same
  change startupMomentDiagonalField symbol constant nonnegative bounded measurable field point =
    startupMomentDiagonalValue symbol constant nonnegative bounded field point at same
  rw [same]
  exact startupMomentDiagonalValue_bound symbol constant nonnegative bounded field point

def StartupMoments.diagonal {dimension : ℕ} (family : StartupMoments dimension)
    (symbol : ℤ → Spatial → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ cell point, |symbol cell point| ≤ constant)
    (measurable : ∀ cell, AEStronglyMeasurable (symbol cell) (volume.restrict openUnitDisk)) : StartupMoments dimension where
  field := startupMomentDiagonalField symbol constant nonnegative bounded measurable family.field
  moment grade := startupMomentDiagonalField symbol constant nonnegative bounded measurable (family.moment grade)
  zero := congrArg (startupMomentDiagonalField symbol constant nonnegative bounded measurable) family.zero
  same := by
    apply ae_all_iff.mpr
    intro grade
    filter_upwards [startupMomentDiagonalField_ae symbol constant nonnegative bounded measurable family.field,
      startupMomentDiagonalField_ae symbol constant nonnegative bounded measurable (family.moment grade),family.same]
      with point fieldAt momentAt same
    intro cell
    rw [momentAt cell,fieldAt cell,same grade cell]
    exact smul_comm _ _ _

end Grad.CartesianStartup

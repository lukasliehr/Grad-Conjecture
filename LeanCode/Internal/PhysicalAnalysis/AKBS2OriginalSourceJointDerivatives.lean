import AKBS1OriginalSourceDerivativeCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 950000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators ENNReal
namespace Grad.ActualOriginalSourceFirst
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers
open Grad.ActualNativeCellMoments Grad.CartesianStartup Grad.ActualOriginalSourceMoments

private theorem derivativeDiskLp_square {dimension : ℕ} (field : DiskL2 dimension) :
    (∫⁻ point in openUnitDisk, ENNReal.ofReal (‖field point‖^2)) = ENNReal.ofReal (‖field‖^2) := by
  rw [diskL2_norm_sq]
  exact (ofReal_integral_eq_lintegral_ofReal (Lp.memLp field).norm.integrable_sq
    (Eventually.of_forall (fun _ => sq_nonneg _))).symm

variable {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)

/-- Tonelli transfers the original first grade to the genuine joint disk and integer-cell derivative energy. -/
theorem originalSourceJointDerivative_finite (direction : Fin 2) :
    (∫⁻ point in openUnitDisk, ∑' cell : ℤ, ENNReal.ofReal
      (‖originalSourceDerivativeCoordinate parameters field direction cell point‖^2)) < ⊤ := by
  rw [lintegral_tsum (fun cell => (Lp.memLp (originalSourceDerivativeCoordinate parameters field direction cell)).norm.integrable_sq.aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
  simp_rw [derivativeDiskLp_square]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (originalSourceDerivativeCoordinate_summable parameters field direction)]
  exact ENNReal.ofReal_lt_top

def originalSourceJointDerivative (direction : Fin 2) : StartupL2 dimension :=
  (jointCellRepresentative_memLp (volume.restrict openUnitDisk)
    (fun cell point => originalSourceDerivativeCoordinate parameters field direction cell point)
    (fun cell => Lp.aestronglyMeasurable (originalSourceDerivativeCoordinate parameters field direction cell))
    (originalSourceJointDerivative_finite parameters field direction)).toLp _

theorem originalSourceJointDerivative_same (direction : Fin 2) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      originalSourceJointDerivative parameters field direction point cell =
        fderiv ℝ (originalWeightedSourceCell parameters field cell) point (spatialBasis direction) := by
  let raw := fun cell point => originalSourceDerivativeCoordinate parameters field direction cell point
  have measurable := fun cell => Lp.aestronglyMeasurable (originalSourceDerivativeCoordinate parameters field direction cell)
  have finite := originalSourceJointDerivative_finite parameters field direction
  have membership := jointCellRepresentative_memLp (volume.restrict openUnitDisk) raw measurable finite
  have actual := ae_all_iff.mpr (originalSourceDerivativeCoordinate_same parameters field direction)
  filter_upwards [membership.coeFn_toLp,finiteCellEnergy_ae_memlp (volume.restrict openUnitDisk) raw measurable finite,actual]
    with point same member actual
  intro cell
  exact ((congrArg (fun value : CellValues dimension => value cell) same).trans
    (jointCellRepresentative_same raw point member cell)).trans (actual cell)

theorem originalSourceJointField_weightedCell :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      originalSourceJointField parameters field 0 point cell = originalWeightedSourceCell parameters field cell point := by
  filter_upwards [originalSourceJointField_same parameters field 0,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point same inside
  intro cell
  simpa only [pow_zero,one_smul,originalWeightedSourceCell_same parameters field cell point inside] using same cell

end Grad.ActualOriginalSourceFirst

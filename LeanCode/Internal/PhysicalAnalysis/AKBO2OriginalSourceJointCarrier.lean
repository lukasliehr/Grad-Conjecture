import AKBO1OriginalSourceCellCoordinates
import AKAW3JointCellRepresentative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 950000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators ENNReal
namespace Grad.ActualOriginalSourceMoments
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers
open Grad.ActualNativeCellMoments Grad.ActualScalarWeakEquations Grad.CartesianStartup

private theorem sourceDiskLp_square {dimension : ℕ} (field : DiskL2 dimension) :
    (∫⁻ point in openUnitDisk, ENNReal.ofReal (‖field point‖^2)) = ENNReal.ofReal (‖field‖^2) := by
  rw [diskL2_norm_sq]
  exact (ofReal_integral_eq_lintegral_ofReal (Lp.memLp field).norm.integrable_sq
    (Eventually.of_forall (fun _ => sq_nonneg _))).symm

variable {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)

/-- The original grade already pays the full joint disk/cell square integral. -/
theorem originalSourceJoint_finite (grade : ℕ) :
    (∫⁻ point in openUnitDisk, ∑' cell : ℤ, ENNReal.ofReal
      (‖originalSourceCellCoordinate parameters field grade cell point‖^2)) < ⊤ := by
  rw [lintegral_tsum (fun cell => (Lp.memLp (originalSourceCellCoordinate parameters field grade cell)).norm.integrable_sq.aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
  simp_rw [sourceDiskLp_square]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (originalSourceCellCoordinate_summable parameters field grade)]
  exact ENNReal.ofReal_lt_top

/-- Genuine full signed-cell L2 carrier, obtained from the existing joint representative and the literal original source coordinate energy. -/
def originalSourceJointField (grade : ℕ) : StartupL2 dimension :=
  (jointCellRepresentative_memLp (volume.restrict openUnitDisk)
    (fun cell point => originalSourceCellCoordinate parameters field grade cell point)
    (fun cell => Lp.aestronglyMeasurable (originalSourceCellCoordinate parameters field grade cell))
    (originalSourceJoint_finite parameters field grade)).toLp _

theorem originalSourceJointField_same (grade : ℕ) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      originalSourceJointField parameters field grade point cell =
        cellFrequency cell^grade • (cartesianWeight parameters cell point • originalCoreCell parameters field cell point) := by
  let raw := fun cell point => originalSourceCellCoordinate parameters field grade cell point
  have measurable := fun cell => Lp.aestronglyMeasurable (originalSourceCellCoordinate parameters field grade cell)
  have finite := originalSourceJoint_finite parameters field grade
  have membership := jointCellRepresentative_memLp (volume.restrict openUnitDisk) raw measurable finite
  have actual := ae_all_iff.mpr (originalSourceCellCoordinate_ae parameters field grade)
  filter_upwards [membership.coeFn_toLp,finiteCellEnergy_ae_memlp (volume.restrict openUnitDisk) raw measurable finite,actual]
    with point same member actual
  intro cell
  exact ((congrArg (fun value : CellValues dimension => value cell) same).trans
    (jointCellRepresentative_same raw point member cell)).trans (actual cell)

end Grad.ActualOriginalSourceMoments

import AKDP7ActualFixedMatrixTensorOneHigh
import AKCG10ActualAxialLeadingSplit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set Filter MeasureTheory
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.BoundaryTrace Grad.ActualOriginalSourceMoments Grad.NonlinearProduct Grad.OriginalCartesianTameEstimate
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.RadialLedger

/-- Literal cell projection of the original all-grade value carrier. -/
theorem startupOriginalJoint_projection {dimension : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) (grade : ℕ) (cell : ℤ) :
    fieldCellProjection dimension openUnitDisk cell (originalSourceJointField parameters core grade) =
      originalSourceCellCoordinate parameters core grade cell := by
  apply Lp.ext
  filter_upwards [fieldCellProjection_ae dimension openUnitDisk (originalSourceJointField parameters core grade),
    originalSourceJointField_same parameters core grade,originalSourceCellCoordinate_ae parameters core grade cell]
    with point projected original coordinate
  exact (projected cell).trans ((original cell).trans coordinate.symm)

/-- Every actual signed axial moment of the SAME original weighted core is
paid at its own original grade, with no change of analytic width. -/
theorem startupSigned_originalGrade_bound {dimension : ℕ} (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (core : ACore parameters dimension) (family : StartupSignedFamily dimension L ell)
    (same : family.field = (originalSourceMoments parameters core).field) (power : ℕ) :
    ‖family.moment power‖ ≤ originalGradeNorm power core := by
  have pointwise (cell : ℤ) :
      ‖fieldCellProjection dimension openUnitDisk cell (family.moment power)‖ ≤
        ‖rawCartesianGradeCoordinates parameters power core.val cell‖ := by
    rw [family.projection,same]
    change ‖startupAxialFrequency L ell cell ^ power •
      fieldCellProjection dimension openUnitDisk cell (originalSourceJointField parameters core 0)‖ ≤ _
    rw [startupOriginalJoint_projection,originalSourceCellCoordinate_value]
    simp only [pow_zero,one_smul,norm_smul,norm_pow]
    have frequency := (startupAxialFrequency_norm L ell cell).trans (scaledCellWeight_le_original admissible cell)
    apply (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) frequency power) (norm_nonneg _)).trans
    have coordinate := PiLp.norm_apply_le (rawCartesianGradeCoordinates parameters power core.val cell) (zeroGradeIndex power)
    change ‖originalSourceCellCoordinate parameters core power cell‖ ≤ _ at coordinate
    rw [originalSourceCellCoordinate_value,norm_smul,norm_pow,Complex.norm_real,
      Real.norm_of_nonneg (cellFrequency_pos cell).le] at coordinate
    exact coordinate
  apply (sq_le_sq₀ (norm_nonneg _) (originalGradeNorm_nonnegative power core)).mp
  rw [Grad.CellEnergy.field_norm_sq_eq_tsum,originalGradeNorm,originalGrade_norm_sq_eq_rows]
  exact (Grad.CellEnergy.cellEnergy_summable dimension openUnitDisk (family.moment power)).tsum_le_tsum
    (fun cell => pow_le_pow_left₀ (norm_nonneg _) (pointwise cell) 2)
    (original_rows_summable parameters core)

end Grad.CartesianStartup

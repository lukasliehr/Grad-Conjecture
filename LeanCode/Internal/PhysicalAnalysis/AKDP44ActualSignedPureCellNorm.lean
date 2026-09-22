import AKDP14ActualMatrixCellEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set Filter MeasureTheory
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap
open Grad.ActualOriginalSourceMoments Grad.OriginalCartesianTameEstimate
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.RadialLedger

/-- A genuine signed moment is paid by the pure-cell endpoint of the
SAME core, rather than by its full mixed norm. -/
theorem startupSigned_originalCell_bound {dimension : ℕ} (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (core : ACore parameters dimension) (family : StartupSignedFamily dimension L ell)
    (same : family.field=(originalSourceMoments parameters core).field)
    (grade power : ℕ) (within : power≤grade) :
    ‖family.moment power‖≤originalCellNorm parameters grade core := by
  have pointwise (cell : ℤ) :
      ‖fieldCellProjection dimension openUnitDisk cell (family.moment power)‖≤
        cellFrequency cell^grade*‖apMassRow (cellFrequency cell) 0 (phaseWeightedJet parameters cell (core.val cell))‖ := by
    rw [family.projection,same]
    change ‖startupAxialFrequency L ell cell^power •
      fieldCellProjection dimension openUnitDisk cell (startupOriginalAllMoments parameters core).field‖≤_
    rw [startupOriginalAllMoments_projection,norm_smul,norm_pow,apMassRow_zero_norm]
    have frequency := (startupAxialFrequency_norm L ell cell).trans (scaledCellWeight_le_original admissible cell)
    exact mul_le_mul_of_nonneg_right
      ((pow_le_pow_left₀ (norm_nonneg _) frequency power).trans
        (pow_le_pow_right₀ (cellFrequency_one_le cell) within)) (norm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  change ‖family.moment power‖^2≤originalCellNorm parameters grade core^2
  rw [Grad.CellEnergy.field_norm_sq_eq_tsum,originalCellNorm_sq]
  exact (Grad.CellEnergy.cellEnergy_summable dimension openUnitDisk (family.moment power)).tsum_le_tsum
    (fun cell => pow_le_pow_left₀ (norm_nonneg _) (pointwise cell) 2)
    (originalCellNorm_summable parameters grade core)

end Grad.CartesianStartup

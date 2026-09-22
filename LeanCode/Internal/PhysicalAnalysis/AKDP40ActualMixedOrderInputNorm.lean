import AKDP15OriginalMatrixCoreConstruction
import AKBZ10OriginalAdjustableMixedEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap
open Grad.Constraints Grad.ActualOriginalSourceFirst Grad.OriginalCartesianTameEstimate
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Envelope

/-- A literal spatial word is one coordinate of the ordinary AP row. -/
theorem startupOriginalWord_ordinaryRow {dimension rank : ℕ}
    (field : ClosedJet dimension) (word : CartesianWord rank) :
    ‖closedContinuousToDiskL2 (closedDerivative field rank word)‖≤‖apMassRow 1 rank field‖ := by
  have bound := PiLp.norm_apply_le (apMassRow 1 rank field) (wordGradeIndex (le_refl rank) word)
  change ‖(1 : ℂ)^_ • closedContinuousToDiskL2
    (closedMultiDerivative field (orthogonalTargetIndex word))‖≤_ at bound
  simpa only [one_pow,one_smul,closedDerivative_eq_multi] using bound

/-- Actual natural cell reserves and a spatial word are paid by the
corresponding mixed-order endpoint, before adjustable interpolation. -/
theorem startupOriginalNaturalDerivative_mixedNorm {dimension : ℕ}
    (parameters : PhaseParameters) (core : ACore parameters dimension)
    (grade rank moment : ℕ) (allocated : rank+moment≤grade) (word : CartesianWord rank) :
    ‖originalMixedDerivativeCarrier parameters (unitDiskAdmissible parameters) core rank moment word‖≤
      originalMixedOrderNorm parameters grade rank core := by
  have pointwise (cell : ℤ) :
      ‖originalMixedDerivativeCoordinate parameters 1 1 core rank moment word cell‖≤
        cellFrequency cell^(grade-rank)*‖apMassRow 1 rank (phaseWeightedJet parameters cell (core.val cell))‖ := by
    rw [originalMixedDerivativeCoordinate,norm_smul,Complex.norm_pow,Complex.norm_real,
      Real.norm_of_nonneg (scaledCellWeight_nonnegative 1 1 cell),unit_scaledCellWeight]
    exact mul_le_mul
      (pow_le_pow_right₀ (cellFrequency_one_le cell) (by omega : moment≤grade-rank))
      (startupOriginalWord_ordinaryRow (phaseWeightedJet parameters cell (core.val cell)) word)
      (norm_nonneg _) (pow_nonneg (cellFrequency_pos cell).le _)
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  change ‖originalMixedDerivativeCarrier parameters (unitDiskAdmissible parameters) core rank moment word‖^2≤
    originalMixedOrderNorm parameters grade rank core^2
  rw [originalMixedOrderNorm_sq]
  unfold originalMixedDerivativeCarrier
  rw [(Grad.FullCellKernel.exchange dimension openUnitDisk).symm.norm_map,
    Grad.SchurKernel.Discrete.lp_norm_sq]
  exact (originalMixedDerivativeCoordinate_summable parameters (unitDiskAdmissible parameters) core rank moment word).tsum_le_tsum
    (fun cell => pow_le_pow_left₀ (norm_nonneg _) (pointwise cell) 2)
    (originalMixedOrderNorm_summable parameters grade rank (by omega) core)

end Grad.CartesianStartup

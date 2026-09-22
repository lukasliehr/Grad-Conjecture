import AKDP75KnownSourceLowerGraphPayment
import AKCO1ActualSignedSourceFirst

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets Grad.NonlinearProduct
open Grad.SourceCollarCoefficients
open Grad.ActualOriginalSourceFirst Grad.OriginalCartesianTameEstimate Grad.BoundaryTrace
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope

theorem startupMassRow_smul {dimension : ℕ} (mass : ℝ) (grade : ℕ) (scalar : ℂ) (field : ClosedJet dimension) :
    apMassRow mass grade (scalar • field)=scalar • apMassRow mass grade field := by
  apply PiLp.ext
  intro index
  change (mass : ℂ)^_ • closedContinuousToDiskL2 (closedMultiDerivative (scalar • field) _)=
    scalar • ((mass : ℂ)^_ • closedContinuousToDiskL2 (closedMultiDerivative field _))
  rw [closedMultiDerivative_smul,closedContinuousToDiskL2_smul,smul_comm]

theorem startupOriginalPlanar_mixedOrder {dimension : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) (grade order : ℕ) (allocated : order≤grade) :
    originalPlanarNorm parameters order core≤originalMixedOrderNorm parameters grade order core := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp
  change originalPlanarNorm parameters order core^2≤originalMixedOrderNorm parameters grade order core^2
  rw [originalPlanarNorm_sq,originalMixedOrderNorm_sq]
  apply (originalPlanarNorm_summable parameters order core).tsum_le_tsum _
    (originalMixedOrderNorm_summable parameters grade order allocated core)
  intro cell
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (cellFrequency_one_le cell))

/-- One genuine signed axial power consumes exactly one cell order of
the original mixed endpoint and no spatial order. -/
theorem startupSignedAxial_mixedOrder_bound {dimension : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) (grade order power : ℕ) (allocated : order≤grade) :
    originalMixedOrderNorm parameters grade order (originalSignedAxialCore parameters core 1 1 power)≤
      originalMixedOrderNorm parameters (grade+power) order core := by
  have each (cell : ℤ) :
      cellFrequency cell^(grade-order)*‖apMassRow 1 order (phaseWeightedJet parameters cell
        ((originalSignedAxialCore parameters core 1 1 power).val cell))‖≤
      cellFrequency cell^(grade+power-order)*‖apMassRow 1 order (phaseWeightedJet parameters cell (core.val cell))‖ := by
    rw [originalSignedAxialCore_val]
    have weighted : phaseWeightedJet parameters cell (startupAxialFrequency 1 1 cell^power • core.val cell)=
        startupAxialFrequency 1 1 cell^power • phaseWeightedJet parameters cell (core.val cell) :=
      (phaseWeightedJetLinear parameters cell).map_smul _ _
    rw [weighted,startupMassRow_smul,norm_smul,norm_pow]
    have frequency : ‖startupAxialFrequency 1 1 cell‖≤cellFrequency cell := by
      simpa only [unit_scaledCellWeight] using startupAxialFrequency_norm 1 1 cell
    have powered := pow_le_pow_left₀ (norm_nonneg _) frequency power
    have paid := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right powered (norm_nonneg
      (apMassRow 1 order (phaseWeightedJet parameters cell (core.val cell))))) (pow_nonneg (cellFrequency_pos cell).le (grade-order))
    exact paid.trans_eq (by rw [←mul_assoc,←pow_add]; congr 2; omega)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp
  change originalMixedOrderNorm parameters grade order (originalSignedAxialCore parameters core 1 1 power)^2≤
    originalMixedOrderNorm parameters (grade+power) order core^2
  rw [originalMixedOrderNorm_sq,originalMixedOrderNorm_sq]
  exact (originalMixedOrderNorm_summable parameters grade order allocated _).tsum_le_tsum
    (fun cell => pow_le_pow_left₀ (mul_nonneg (pow_nonneg (cellFrequency_pos cell).le _) (norm_nonneg _)) (each cell) 2)
    (originalMixedOrderNorm_summable parameters (grade+power) order (by omega) core)

theorem startupSignedAxial_planar_bound {dimension : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) (grade power : ℕ) :
    originalPlanarNorm parameters grade (originalSignedAxialCore parameters core 1 1 power)≤
      originalMixedOrderNorm parameters (grade+power) grade core := by
  simpa only [originalMixedOrderNorm,originalPlanarNorm,Nat.sub_self,pow_zero,one_mul] using
    startupSignedAxial_mixedOrder_bound parameters core grade grade power le_rfl

theorem startupSignedAxial_cell_bound {dimension : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) (grade power : ℕ) :
    originalCellNorm parameters grade (originalSignedAxialCore parameters core 1 1 power)≤originalCellNorm parameters (grade+power) core := by
  simpa only [startupOriginalMixedOrder_zero] using startupSignedAxial_mixedOrder_bound parameters core grade 0 power (Nat.zero_le _)

end Grad.CartesianStartup

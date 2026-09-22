import AKDR2OriginalAngularKernelNorm
import AKBO3SameOriginalSourceMoments
import AKAY33RoughAngularMapAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.CartesianStartup Grad.PDEBootstrap Grad.GenericCarriers
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.ActualAngularInverse
open Grad.ActualOriginalSourceMoments Grad.ActualScalarWeakEquations
open Grad.GaugeCoefficients.Radial Grad.Constraints

theorem originalSource_field_closed {dimension : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (originalSourceMoments parameters core).field point cell =
        closedDiskLift (phaseWeightedJet parameters cell (core.val cell)).value point := by
  filter_upwards [originalSourceMoments_same parameters core,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point represented inside
  intro cell
  rw [closedDiskLift,dif_pos (openDiskMembershipClosed point inside),phaseWeightedJet_value]
  rw [← originalCoreCell_value parameters core cell ⟨point,openDiskMembershipClosed point inside⟩]
  exact represented cell

/-- Exact field identity for the SAME original angular-integral core. -/
theorem originalAngularKernelCore_sameField {dimension : ℕ} (parameters : PhaseParameters)
    (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight)
    (bound : ℝ) (nonnegative : 0 ≤ bound)
    (bounded : ∀ angle ∈ Icc (0 : ℝ) (2*Real.pi), ‖weight angle‖ ≤ bound)
    (core : ACore parameters dimension) :
    (originalSourceMoments parameters
      (originalAngularKernelCore parameters weight smooth bound nonnegative bounded core)).field =
      startupAngularKernel dimension weight smooth (originalSourceMoments parameters core).field := by
  apply startupField_ae_ext
  apply ae_all_iff.mpr
  intro cell
  have inputSame : (fun point => (originalSourceMoments parameters core).field point cell) =ᵐ[
      volume.restrict openUnitDisk]
      fun point => closedDiskLift (phaseWeightedJet parameters cell (core.val cell)).value point := by
    filter_upwards [originalSource_field_closed parameters core] with point same
    exact same cell
  have transported := Grad.KernelIntegral.transported_ae_eq_sections
    (volume.restrict (Icc (0 : ℝ) (2*Real.pi))) openUnitDisk_isOpen.measurableSet planeRotationEquiv
    (fun angle point => by change ‖planeRotationEquiv angle point‖ < 1 ↔ ‖point‖ < 1; rw [LinearIsometryEquiv.norm_map])
    continuous_planeRotation_joint.measurable inputSame
  filter_upwards [originalSource_field_closed parameters
      (originalAngularKernelCore parameters weight smooth bound nonnegative bounded core),
    startupAngularKernel_action_ae dimension weight smooth (originalSourceMoments parameters core).field cell,
    transported,ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point outputSame action same inside
  rw [outputSame cell,action]
  have closed : point ∈ closedUnitDisk := openDiskMembershipClosed point inside
  rw [closedDiskLift,dif_pos closed]
  change (apWeightedJet parameters.sigma0 parameters.gamma 1 cell
    (kernelRotationJet weight smooth (core.val cell))).value ⟨point,closed⟩ = _
  rw [← apWeightedJet_kernelRotation,kernelRotationJet_value,← integral_smul]
  apply integral_congr_ae
  filter_upwards [same] with angle actual
  rw [actual]
  have rotatedClosed : planeRotationEquiv angle point ∈ closedUnitDisk := by
    change ‖planeRotationEquiv angle point‖ ≤ 1
    rw [LinearIsometryEquiv.norm_map]
    exact closed
  rw [closedDiskLift,dif_pos rotatedClosed]
  rfl

end Grad.OriginalCoreRealization

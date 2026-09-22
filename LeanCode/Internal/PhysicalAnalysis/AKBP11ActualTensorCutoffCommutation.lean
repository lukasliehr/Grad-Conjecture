import AKBP10SameSpatialScalarActions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

namespace StartupRadialRelated
variable {scalar : Spatial → ℝ}
variable (radial : ∀ first second : Spatial, ‖first‖ = ‖second‖ → scalar first = scalar second)
variable {L sigma gamma ell : ℝ}

include radial in
theorem qrad {weighted original : StartupL2 2} (same : StartupRadialRelated (fun _ => scalar) weighted original) :
    StartupRadialRelated (fun _ => scalar) (startupGenuineQradKernel weighted) (startupGenuineQradKernel original) :=
  same.add (((same.value quarterValueMap).tangential radial).value quarterValueMap)

include radial in
theorem genuineForce (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell)
    (coherent : LedgerCoherent data) (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    {weighted original : StartupL2 3} (same : StartupRadialRelated (fun _ => scalar) weighted original) :
    StartupRadialRelated (fun _ => scalar) (startupGenuineForceKernel admissible data coherent inverseCoherent weighted)
      (startupGenuineForceKernel admissible data coherent inverseCoherent original) :=
  (((same.current radial admissible data.gaugeDeviation coherent.2.2.2.1 inverseCoherent).matrix
    admissible data.rotatedPlanarProduct coherent.2.2.2.2.2.2.2.1).qrad radial).smul 2

include radial in
theorem thirdCorrection (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell)
    (coherent : LedgerCoherent data) (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    {weighted original : StartupL2 3} (same : StartupRadialRelated (fun _ => scalar) weighted original) :
    StartupRadialRelated (fun _ => scalar) (originalThirdCorrectionKernel admissible data coherent inverseCoherent weighted)
      (originalThirdCorrectionKernel admissible data coherent inverseCoherent original) := by
  have correction := (same.current radial admissible data.gaugeDeviation coherent.2.2.2.1 inverseCoherent).matrix
    admissible data.rotatedThirdProduct coherent.2.2.2.2.2.2.2.2
  exact (correction.sub (correction.angular
    (fun _ angle point => radial _ point (LinearIsometryEquiv.norm_map (planeRotationEquiv angle) point))
    (angularCharacter 0) (angularCharacter_smooth 0))).smul 2

include radial in
theorem genuineFlux (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell)
    (coherent : LedgerCoherent data) (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    {weighted original : StartupL2 3} (same : StartupRadialRelated (fun _ => scalar) weighted original) :
    StartupRadialRelated (fun _ => scalar) (startupGenuinePrincipalFluxKernel admissible data coherent inverseCoherent weighted)
      (startupGenuinePrincipalFluxKernel admissible data coherent inverseCoherent original) := by
  have physicalFlux := ((same.current radial admissible data.gaugeDeviation coherent.2.2.2.1 inverseCoherent).matrix
    admissible data.fluxDeviation coherent.2.2.2.2.1).value planarPartMap
  exact (physicalFlux.sub (physicalFlux.average radial)).sub
    ((((same.genuineForce radial admissible data coherent inverseCoherent).average radial).value quarterValueMap).smul (1/2))

include radial in
theorem genuineERRow (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell)
    (coherent : LedgerCoherent data) (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    {weighted original : StartupL2 3} (same : StartupRadialRelated (fun _ => scalar) weighted original) (row : Fin 3) :
    StartupRadialRelated (fun _ => scalar) (startupGenuineERKernelRow admissible data coherent inverseCoherent row weighted)
      (startupGenuineERKernelRow admissible data coherent inverseCoherent row original) := by
  fin_cases row
  · exact (same.genuineForce radial admissible data coherent inverseCoherent).value planarInclusionMap
  · exact (same.thirdCorrection radial admissible data coherent inverseCoherent).value toroidalInclusionMap
  · exact (same.genuineFlux radial admissible data coherent inverseCoherent).value planarInclusionMap

include radial in
theorem genuinePrincipalTensor (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell)
    (coherent : LedgerCoherent data) (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    {weighted original : StartupL2 3} (same : StartupRadialRelated (fun _ => scalar) weighted original) (outer inner : Fin 2) :
    StartupRadialRelated (fun _ => scalar) (startupGenuinePrincipalTensorKernel admissible data coherent inverseCoherent outer inner weighted)
      (startupGenuinePrincipalTensorKernel admissible data coherent inverseCoherent outer inner original) := by
  simp only [startupGenuinePrincipalTensorKernel,sum_apply,ContinuousLinearMap.comp_apply]
  exact StartupRadialRelated.principalRows
    (fun _ angle point => radial _ point (LinearIsometryEquiv.norm_map (planeRotationEquiv angle) point))
    (fun row => startupGenuineERKernelRow admissible data coherent inverseCoherent row weighted)
    (fun row => startupGenuineERKernelRow admissible data coherent inverseCoherent row original)
    (same.genuineERRow radial admissible data coherent inverseCoherent) outer inner

end StartupRadialRelated

theorem startupCutoff_related (cutoff : Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff)
    (compact : HasCompactSupport cutoff) (field : StartupL2 3) :
    StartupRadialRelated (fun _ => cutoff) (startupCutoffL2 cutoff smooth compact field) field := by
  filter_upwards [startupCutoffL2_ae cutoff smooth compact field] with point same
  intro cell
  change startupCutoffL2 cutoff smooth compact field point cell = cutoff point • field point cell
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact same cell

/-- Exact commutation of the actual full coefficient tensor with an interior
radial cutoff, including Qa, coefficient mixing, Qrad and all inverse covectors. -/
theorem startupGenuinePrincipalTensor_cutoff {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (cutoff : Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff) (compact : HasCompactSupport cutoff)
    (radial : ∀ first second : Spatial, ‖first‖ = ‖second‖ → cutoff first = cutoff second)
    (field : StartupL2 3) (outer inner : Fin 2) :
    startupGenuinePrincipalTensorKernel admissible data coherent inverseCoherent outer inner (startupCutoffL2 cutoff smooth compact field) =
      startupCutoffL2 cutoff smooth compact (startupGenuinePrincipalTensorKernel admissible data coherent inverseCoherent outer inner field) := by
  have transported := (startupCutoff_related cutoff smooth compact field).genuinePrincipalTensor
    radial admissible data coherent inverseCoherent outer inner
  have literal := startupCutoff_related cutoff smooth compact
    (startupGenuinePrincipalTensorKernel admissible data coherent inverseCoherent outer inner field)
  apply startupField_ae_ext
  filter_upwards [transported,literal] with point actual same
  intro cell
  exact (actual cell).trans (same cell).symm

end Grad.CartesianStartup

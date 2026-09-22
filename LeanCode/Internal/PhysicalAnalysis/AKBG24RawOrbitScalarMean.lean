import AKBG23SameScalarPrimitiveGauges

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets

/-- Actual zero angular orbit means transfer to the SAME all-cell L2 scalar
representative. The AE transport is paid jointly in the angular integral. -/
theorem startupScalarMean_zero_of_rawOrbit (field : StartupL2 1) (raw : ℤ → Spatial → PhysicalValue 1)
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ, field point cell = raw cell point)
    (orbitMean : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (∫ angle in Icc (0 : ℝ) (2*Real.pi), raw cell (planeRotationEquiv angle point)) = 0) :
    startupRealAngularKernelDim 1 (fun _ : ℝ => 1) contDiff_const field = 0 := by
  apply startupField_ae_ext
  apply ae_all_iff.mpr
  intro cell
  have sameCell : (fun point => field point cell) =ᵐ[volume.restrict openUnitDisk] raw cell := by
    filter_upwards [same] with point equality
    exact equality cell
  have transported := Grad.KernelIntegral.transported_ae_eq_sections
    (volume.restrict (Icc (0 : ℝ) (2*Real.pi))) openUnitDisk_isOpen.measurableSet planeRotationEquiv
    (fun angle point => by change ‖planeRotationEquiv angle point‖ < 1 ↔ ‖point‖ < 1; rw [LinearIsometryEquiv.norm_map])
    continuous_planeRotation_joint.measurable sameCell
  filter_upwards [startupAngularKernel_action_ae 1 (fun _ : ℝ => (1 : ℂ)) contDiff_const field cell,
    transported, orbitMean, Lp.coeFn_zero (CellValues 1) 2 (volume.restrict openUnitDisk)]
    with point action transported zero zeroField
  change (startupAngularKernel 1 (fun angle : ℝ => ((1 : ℝ) : ℂ))
    (Complex.ofRealCLM.contDiff.comp contDiff_const) field) point cell = _
  simp only [Complex.ofReal_one]
  rw [action, zeroField]
  change (∫ angle in Icc (0 : ℝ) (2*Real.pi), startupAngularCoefficient 1 (fun _ => 1) angle
    (field (planeRotationEquiv angle point) cell)) = 0
  have actual : (∫ angle in Icc (0 : ℝ) (2*Real.pi), startupAngularCoefficient 1 (fun _ => 1) angle
      (field (planeRotationEquiv angle point) cell)) =
      (((2*Real.pi)⁻¹ : ℝ) : ℂ) • ∫ angle in Icc (0 : ℝ) (2*Real.pi), raw cell (planeRotationEquiv angle point) := by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [transported] with angle equality
    rw [equality]
    simp only [startupAngularCoefficient, smul_apply, ContinuousLinearMap.id_apply, one_smul]
  rw [actual, zero cell, smul_zero]

/-- Minimal original Xi bridge consumed by the scalar primitive and force
startup: literal raw orbit mean implies all genuine compact-test scalar gauges. -/
theorem startupScalarWeakMean_of_rawOrbit (field : StartupL2 1) (raw : ℤ → Spatial → PhysicalValue 1)
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ, field point cell = raw cell point)
    (orbitMean : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (∫ angle in Icc (0 : ℝ) (2*Real.pi), raw cell (planeRotationEquiv angle point)) = 0)
    (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell 0 (startupMeanTest test) field = 0 := by
  have transpose := congrArg (fun operator : StartupL2 1 →L[ℂ] ℂ => operator field)
    (startupCoordinateTestPairing_angular (fun _ : ℝ => 1) contDiff_const cell 0 test)
  change startupCoordinateTestPairing cell 0 test
      (startupRealAngularKernelDim 1 (fun _ : ℝ => 1) contDiff_const field) =
    startupCoordinateTestPairing cell 0 (startupMeanTest test) field at transpose
  rw [startupScalarMean_zero_of_rawOrbit field raw same orbitMean, map_zero] at transpose
  exact transpose.symm

end Grad.CartesianStartup

import AKBE9RadialReflectionPolarFormula

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped Interval ContDiff
namespace Grad.ActualCartesianWeakEquations
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.CartesianStartup Grad.GenericCarriers Grad.PDEBootstrap

/-- Actual full-cell equivariant averaging agrees with the literal closed-disk
formula whenever this one cell has the indicated continuous representative.
This also applies after localizing a punctured smooth field to an annulus. -/
theorem originalAverage_closedRepresentative (field : StartupL2 2) (cell : ℤ)
    (raw : ClosedDisk → ComplexEuclidean 2) (continuousRaw : Continuous raw)
    (same : (fun point => field point cell) =ᵐ[volume.restrict openUnitDisk] closedFieldExtension raw) :
    (fun point => (originalAverageKernel field) point cell) =ᵐ[volume.restrict openUnitDisk]
      closedFieldExtension (closedEquivariantValue raw) := by
  have transported := Grad.KernelIntegral.transported_ae_eq_sections
    (volume.restrict (Icc (0 : ℝ) (2*Real.pi))) openUnitDisk_isOpen.measurableSet planeRotationEquiv
    (fun angle point => by change ‖planeRotationEquiv angle point‖ < 1 ↔ ‖point‖ < 1; rw [LinearIsometryEquiv.norm_map])
    continuous_planeRotation_joint.measurable same
  filter_upwards [startupAverageKernel_action_ae field cell,transported,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point action transported inside
  let closed : ClosedDisk := ⟨point,by change ‖point‖ ≤ 1; exact le_of_lt inside⟩
  have extension := closedFieldExtension_value (closedEquivariantValue raw) closed
  change closedFieldExtension (closedEquivariantValue raw) point = closedEquivariantValue raw closed at extension
  rw [action,extension,closedEquivariantValue_integral raw continuousRaw,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2*Real.pi),← integral_Icc_eq_integral_Ioc,
    ← integral_smul]
  apply integral_congr_ae
  filter_upwards [transported] with angle actual
  rw [actual]
  have orbit := closedFieldExtension_value raw (Grad.GaugeCoefficients.Radial.rotatedPoint angle closed)
  have orbitSame : closedFieldExtension raw (planeRotationEquiv angle point) =
      raw (Grad.GaugeCoefficients.Radial.rotatedPoint angle closed) := by
    simpa only [Grad.GaugeCoefficients.Radial.rotatedPoint,closed,physicalRotation_eq_orthogonal,
      planeRotationEquiv_apply] using orbit
  rw [orbitSame]
  simp only [startupAverageCoefficient,smul_apply,Complex.coe_smul]

end Grad.ActualCartesianWeakEquations

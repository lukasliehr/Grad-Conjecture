import AKBE15RadialTestLocalization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.ActualScalarWeakEquations
open Grad.CartesianState Grad.GaugeCoefficients.Radial
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianStartup Grad.GenericCarriers Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.ActualCartesianWeakEquations

/-- The fixed scalar mean has its literal closed-disk representative on the same cell. -/
theorem scalarMean_closedRepresentative (field : StartupL2 1) (cell : ℤ)
    (raw : ClosedDisk → ComplexEuclidean 1)
    (same : (fun point => field point cell) =ᵐ[volume.restrict openUnitDisk] closedFieldExtension raw) :
    (fun point => (startupAngularKernel 1 (fun _ => (1 : ℂ)) contDiff_const field) point cell) =ᵐ[volume.restrict openUnitDisk]
      closedFieldExtension (closedAngularMean raw) := by
  have transported := Grad.KernelIntegral.transported_ae_eq_sections
    (volume.restrict (Icc (0 : ℝ) (2*Real.pi))) openUnitDisk_isOpen.measurableSet planeRotationEquiv
    (fun angle point => by change ‖planeRotationEquiv angle point‖ < 1 ↔ ‖point‖ < 1; rw [LinearIsometryEquiv.norm_map])
    continuous_planeRotation_joint.measurable same
  filter_upwards [startupAngularKernel_action_ae 1 (fun _ => (1 : ℂ)) contDiff_const field cell,
    transported,ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point action transported inside
  let closed : ClosedDisk := ⟨point,by change ‖point‖ ≤ 1; exact inside.le⟩
  have extension := closedFieldExtension_value (closedAngularMean raw) closed
  change closedFieldExtension (closedAngularMean raw) point = closedAngularMean raw closed at extension
  rw [action,extension,closedAngularMean_eq_rotationAverage,rotationAverage_eq_compactIntegral,← integral_smul]
  apply integral_congr_ae
  filter_upwards [transported] with angle actual
  rw [actual]
  simp only [startupAngularCoefficient,smul_apply,ContinuousLinearMap.id_apply,one_smul,Complex.coe_smul]
  simp only [closed,physicalRotation_eq_orthogonal,planeRotationEquiv_apply]

/-- Exact scalar mean transpose using the existing continuous one-cell injection. -/
theorem scalarMean_closedTranspose (raw : ClosedDisk → ComplexEuclidean 1)
    (continuousRaw : Continuous raw) (test : Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    (∫ point in openUnitDisk, test point • (closedFieldExtension (closedAngularMean raw) point) 0) =
      ∫ point in openUnitDisk, startupAngularTest (fun _ => 1) test point • (closedFieldExtension raw point) 0 := by
  let value : C(ClosedDisk,ComplexEuclidean 1) := ⟨raw,continuousRaw⟩
  let field := apDiskInjection 1 (closedContinuousToDiskL2 value)
  have same : (fun point => field point (0 : ℤ)) =ᵐ[volume.restrict openUnitDisk] closedFieldExtension raw := by
    filter_upwards [apDiskInjection_ae (closedContinuousToDiskL2 value),closedContinuousToDiskL2_ae value] with point injection actual
    change (apDiskInjection 1 (closedContinuousToDiskL2 value)) point 0 = _
    rw [injection,cellSingle_apply,if_pos rfl,actual]
    rfl
  have projected := scalarMean_closedRepresentative field 0 raw same
  have transpose : (∫ point in openUnitDisk, test point •
      (startupAngularKernel 1 (fun _ => (1 : ℂ)) contDiff_const field) point 0 0) =
      ∫ point in openUnitDisk, startupAngularTest (fun _ => 1) test point • field point 0 0 := by
    simpa only [EuclideanSpace.inner_single_left,map_one,one_mul,Complex.ofReal_one] using
      startupRealAngularKernel_transposeDim 1 (fun _ => 1) contDiff_const field 0 (EuclideanSpace.single 0 1) test smooth compact
  calc
    _ = ∫ point in openUnitDisk, test point •
        (startupAngularKernel 1 (fun _ => (1 : ℂ)) contDiff_const field) point 0 0 := by
      apply integral_congr_ae
      filter_upwards [projected] with point actual
      rw [actual]
    _ = _ := transpose
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [same] with point actual
      rw [actual]

end Grad.ActualScalarWeakEquations

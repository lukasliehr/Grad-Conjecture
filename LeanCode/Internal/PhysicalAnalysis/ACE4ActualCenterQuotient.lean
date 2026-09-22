import ACE3PureModeEuler

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterVolterra
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial
open Grad.NonlinearProduct Grad.NonlinearRange Grad.NonlinearQuotientBounds Grad.RepresentedKernel.SpatialProduct

def centerWirtingerJet {dimension : ℕ} (mode : ℤ) (field : ClosedJet dimension) : ClosedJet dimension :=
  (1 / 2 : ℂ) • centerDifferential mode field

/-- The literal W2 operator, with the factors 2 and 1/2 cancelled. -/
def centerQuotientJet {dimension : ℕ} (mode : ℤ) (field : ClosedJet dimension) : ClosedJet dimension :=
  powerDilationJet 1 (centerDifferential mode field)

theorem centerQuotientJet_W2 {dimension : ℕ} (mode : ℤ) (field : ClosedJet dimension) :
    centerQuotientJet mode field = (2 : ℂ) • powerDilationJet 1 (centerWirtingerJet mode field) := by
  simp [centerQuotientJet, centerWirtingerJet, powerDilationJet_smul, smul_smul]

theorem signedCoordinate_dilation (sign scale : ℝ) (point : SpatialPlane) :
    signedComplexCoordinate sign (scale • point) = (scale : ℂ) * signedComplexCoordinate sign point := by
  simp only [signedComplexCoordinate, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

theorem centerQuotient_primitive {dimension : ℕ} (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (field : ClosedJet dimension) (pure : angularClosedJet mode field = field) (point : ClosedDisk)
    (scale : ℝ) (inside : scale ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun current : ℝ => current • smoothClosedExtension field (current • point.val))
      (signedComplexCoordinate (mode : ℝ) point.val •
        (scale • smoothClosedExtension (centerDifferential mode field) (scale • point.val))) scale := by
  have path : HasDerivAt (fun current : ℝ => current • point.val) point.val scale := by
    have derivative : HasDerivAt (fun current : ℝ => current • point.val) ((1 : ℝ) • point.val) scale :=
      (hasDerivAt_id scale).smul_const point.val
    simpa only [one_smul] using derivative
  have derivative := (hasDerivAt_id scale).smul
    (((smoothClosedExtension_smooth field).differentiable (by simp) (scale • point.val)).hasFDerivAt.comp_hasDerivAt scale path)
  have identity := congrArg (fun jet : ClosedJet dimension => jet.value (dilationPoint scale inside.1 inside.2 point))
    (pureCenter_euler mode center field pure)
  rw [coordinateMultiplyJet_value, closedJet_value_add, ContinuousMap.add_apply, eulerJet_extension_value,
    ← smoothClosedExtension_value (centerDifferential mode field), ← smoothClosedExtension_value field] at identity
  change signedComplexCoordinate (mode : ℝ) (scale • point.val) •
      smoothClosedExtension (centerDifferential mode field) (scale • point.val) =
    fderiv ℝ (smoothClosedExtension field) (scale • point.val) (scale • point.val) +
      smoothClosedExtension field (scale • point.val) at identity
  rw [map_smul, signedCoordinate_dilation, mul_smul, Complex.coe_smul, smul_comm] at identity
  apply derivative.congr_deriv
  simpa only [one_smul, id_eq, Function.comp_apply] using identity.symm

/-- Genuine smooth division of a pure first mode by its signed coordinate,
proved on the entire closed disk by a compact fundamental theorem. -/
theorem centerQuotient_factor {dimension : ℕ} (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (field : ClosedJet dimension) (pure : angularClosedJet mode field = field) :
    coordinateMultiplyJet (mode : ℝ) (centerQuotientJet mode field) = field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [coordinateMultiplyJet_value]
  change signedComplexCoordinate (mode : ℝ) point.val •
    (∫ scale in Icc (0 : ℝ) 1, scale ^ 1 • smoothClosedExtension (centerDifferential mode field) (scale • point.val)) = _
  simp only [pow_one]
  rw [← integral_smul, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have integrable : IntervalIntegrable (fun scale : ℝ => signedComplexCoordinate (mode : ℝ) point.val •
      (scale • smoothClosedExtension (centerDifferential mode field) (scale • point.val))) volume 0 1 := by
    have continuousIntegrand : Continuous (fun scale : ℝ => signedComplexCoordinate (mode : ℝ) point.val •
        (scale • smoothClosedExtension (centerDifferential mode field) (scale • point.val))) := by
      have pathContinuous : Continuous (fun scale : ℝ => scale • point.val) := by fun_prop
      have fieldContinuous : Continuous (fun scale : ℝ =>
          smoothClosedExtension (centerDifferential mode field) (scale • point.val)) :=
        (smoothClosedExtension_smooth (centerDifferential mode field)).continuous.comp pathContinuous
      have weightedContinuous : Continuous (fun scale : ℝ =>
          scale • smoothClosedExtension (centerDifferential mode field) (scale • point.val)) :=
        (continuous_id : Continuous (fun scale : ℝ => scale)).smul fieldContinuous
      exact (continuous_const : Continuous (fun _ : ℝ => signedComplexCoordinate (mode : ℝ) point.val)).smul weightedContinuous
    exact continuousIntegrand.intervalIntegrable 0 1
  have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun scale inside => centerQuotient_primitive mode center field pure point scale
      (by simpa only [uIcc_of_le zero_le_one] using inside)) integrable
  simpa only [one_smul, zero_smul, sub_zero, smoothClosedExtension_value] using integral

end Grad.ActualCenterVolterra

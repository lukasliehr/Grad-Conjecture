import BL7Kernel

noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

local instance liftKernelPeriodPositive : Fact (0 < (2 * Real.pi : ℝ)) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

theorem complexCoordinate_smul (radius : ℝ) (point : SpatialPlane) :
    signedComplexCoordinate 1 (radius • point) = (radius : ℂ) * signedComplexCoordinate 1 point := by
  simp [signedComplexCoordinate]
  ring

theorem complexCoordinate_boundary (angle : CellCircle) :
    signedComplexCoordinate 1 (boundaryCirclePoint angle) = AddCircle.toCircle angle := by
  change ((AddCircle.toCircle angle : ℂ).re : ℂ) + Complex.I * (1 : ℂ) *
    ((AddCircle.toCircle angle : ℂ).im : ℂ) = (AddCircle.toCircle angle : ℂ)
  rw [mul_one, mul_comm Complex.I]
  exact Complex.re_add_im _

theorem unitComplexCoordinate_polar (radius : ℝ) (positive : 0 < radius) (angle : CellCircle) :
    unitComplexCoordinate (radius • boundaryCirclePoint angle) = AddCircle.toCircle angle := by
  rw [unitComplexCoordinate, complexCoordinate_smul, complexCoordinate_boundary, norm_smul,
    boundaryCirclePoint_norm, mul_one, Real.norm_of_nonneg positive.le]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr positive.ne')

theorem circle_zpow_fourier (angle : CellCircle) (mode : ℤ) :
    (AddCircle.toCircle angle : ℂ) ^ mode = fourier mode angle := by
  rw [fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow]

theorem boundaryKernel_polar (mode : ℤ × ℤ) (time : ℝ) (beforeAxis : time < 1)
    (angle : CellCircle) :
    boundaryKernel mode ((1 - time) • boundaryCirclePoint angle) =
      (collarCutoff1D time : ℂ) * (Real.exp (-boundaryFrequency mode * time) : ℂ) * fourier mode.1 angle := by
  have radiusPositive : 0 < 1 - time := sub_pos.mpr beforeAxis
  rw [boundaryKernel, unitComplexCoordinate_polar _ radiusPositive, circle_zpow_fourier,
    norm_smul, boundaryCirclePoint_norm, mul_one, Real.norm_of_nonneg radiusPositive.le,
    sub_sub_cancel, Complex.ofReal_mul]

theorem boundaryKernel_boundary (mode : ℤ × ℤ) (angle : CellCircle) :
    boundaryKernel mode (boundaryCirclePoint angle) = fourier mode.1 angle := by
  have law := boundaryKernel_polar mode 0 (by norm_num) angle
  simpa only [sub_zero, one_smul, collarCutoff1D_zero, Complex.ofReal_one, mul_zero,
    Real.exp_zero, one_mul] using law

def boundaryModeJet {dimension : ℕ} (mode : ℤ × ℤ) (value : ComplexEuclidean dimension) :
    ClosedJet dimension :=
  globalClosedJet (fun point => boundaryKernel mode point • value)
    ((boundaryKernel_smooth mode).smul contDiff_const)

theorem boundaryModeJet_value {dimension : ℕ} (mode : ℤ × ℤ) (value : ComplexEuclidean dimension)
    (point : ClosedDisk) :
    (boundaryModeJet mode value).value point = boundaryKernel mode point.val • value := rfl

theorem boundaryModeJet_boundary {dimension : ℕ} (mode : ℤ × ℤ) (value : ComplexEuclidean dimension)
    (angle : CellCircle) :
    (boundaryModeJet mode value).value (boundaryDiskPoint angle) = fourier mode.1 angle • value := by
  rw [boundaryModeJet_value]
  change boundaryKernel mode (boundaryCirclePoint angle) • value = _
  rw [boundaryKernel_boundary]

theorem fourierCoeff_scalar_smul_const {dimension : ℕ} (field : CellCircle → ℂ)
    (value : ComplexEuclidean dimension) (mode : ℤ) :
    fourierCoeff (fun angle => field angle • value) mode = fourierCoeff field mode • value := by
  simp only [fourierCoeff, smul_smul, smul_eq_mul]
  exact integral_smul_const _ _

theorem boundaryModeJet_coefficient {dimension : ℕ} (mode : ℤ × ℤ) (value : ComplexEuclidean dimension)
    (frequency : ℤ) :
    fourierCoeff (fun angle : CellCircle => (boundaryModeJet mode value).value (boundaryDiskPoint angle)) frequency =
      if frequency = mode.1 then value else 0 := by
  simp_rw [boundaryModeJet_boundary]
  rw [fourierCoeff_scalar_smul_const, fourierCoeff_fourier]
  by_cases equal : frequency = mode.1
  · subst frequency
    simp
  · simp [equal]

theorem boundaryModeJet_zero_inner {dimension : ℕ} (mode : ℤ × ℤ) (value : ComplexEuclidean dimension)
    (point : ClosedDisk) (inside : ‖point.val‖ ≤ (7 / 8 : ℝ)) :
    (boundaryModeJet mode value).value point = 0 := by
  rw [boundaryModeJet_value, boundaryKernel_zero_inner mode point.val inside, zero_smul]

end Grad.BoundaryLift

import BL6ProfileEnergy
import AngularCoordinateShift

noncomputable section

open Set Filter
open scoped BigOperators ContDiff Topology

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

theorem complexCoordinate_norm (point : SpatialPlane) : ‖signedComplexCoordinate 1 point‖ = ‖point‖ := by
  rw [Complex.norm_def, Complex.normSq_apply, PiLp.norm_eq_of_L2, Fin.sum_univ_two]
  simp [signedComplexCoordinate, Real.norm_eq_abs, pow_two]

def unitComplexCoordinate (point : SpatialPlane) : ℂ := signedComplexCoordinate 1 point / (‖point‖ : ℂ)

theorem unitComplexCoordinate_norm (point : SpatialPlane) (nonzero : point ≠ 0) :
    ‖unitComplexCoordinate point‖ = 1 := by
  rw [unitComplexCoordinate, norm_div, complexCoordinate_norm, Complex.norm_real,
    Real.norm_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr nonzero)]

def boundaryKernel (mode : ℤ × ℤ) (point : SpatialPlane) : ℂ :=
  ((collarCutoff1D (1 - ‖point‖) * Real.exp (-boundaryFrequency mode * (1 - ‖point‖)) : ℝ) : ℂ) *
    unitComplexCoordinate point ^ mode.1

theorem boundaryKernel_zero_inner (mode : ℤ × ℤ) (point : SpatialPlane)
    (inside : ‖point‖ ≤ (7 / 8 : ℝ)) : boundaryKernel mode point = 0 := by
  rw [boundaryKernel, collarCutoff1D_vanishes (1 - ‖point‖) (by linarith), zero_mul,
    Complex.ofReal_zero, zero_mul]

theorem unitComplexCoordinate_contDiffAt (point : SpatialPlane) (nonzero : point ≠ 0) :
    ContDiffAt ℝ ∞ unitComplexCoordinate point := by
  have normSmooth : ContDiffAt ℝ ∞ (fun source : SpatialPlane => ‖source‖) point :=
    contDiffAt_norm ℝ nonzero
  change ContDiffAt ℝ ∞ (fun source => signedComplexCoordinate 1 source / (‖source‖ : ℂ)) point
  simpa only [div_eq_mul_inv, Function.comp_apply, Complex.ofRealCLM_apply] using
    (signedComplexCoordinate_smooth 1).contDiffAt.mul
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp point normSmooth).fun_inv
        (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr nonzero)))

theorem contDiffAt_complex_zpow {Space : Type*} [NormedAddCommGroup Space]
    [NormedSpace ℝ Space] {f : Space → ℂ} {point : Space}
    (smooth : ContDiffAt ℝ ∞ f point) (nonzero : f point ≠ 0) (power : ℤ) :
    ContDiffAt ℝ ∞ (fun source => f source ^ power) point := by
  cases power with
  | ofNat power => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using smooth.pow power
  | negSucc power =>
      simpa only [zpow_negSucc] using (smooth.pow (power + 1)).fun_inv (pow_ne_zero _ nonzero)

theorem boundaryKernel_smooth (mode : ℤ × ℤ) : ContDiff ℝ ∞ (boundaryKernel mode) := by
  rw [contDiff_iff_contDiffAt]
  intro point
  by_cases nonzero : point = 0
  · subst point
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : SpatialPlane) (by norm_num : (0 : ℝ) < 7 / 8)] with source inside
    have radius : ‖source‖ ≤ (7 / 8 : ℝ) := by
      simpa only [dist_zero_right] using (Metric.mem_ball.mp inside).le
    exact boundaryKernel_zero_inner mode source radius
  · have normSmooth : ContDiffAt ℝ ∞ (fun source : SpatialPlane => ‖source‖) point := contDiffAt_norm ℝ nonzero
    have timeSmooth : ContDiffAt ℝ ∞ (fun source : SpatialPlane => 1 - ‖source‖) point :=
      contDiffAt_const.sub normSmooth
    have profileSmooth : ContDiffAt ℝ ∞ (fun source : SpatialPlane =>
        collarCutoff1D (1 - ‖source‖) * Real.exp (-boundaryFrequency mode * (1 - ‖source‖))) point :=
      (cutoffExponentialProfile_smooth mode).contDiffAt.comp point timeSmooth
    have unitNonzero : unitComplexCoordinate point ≠ 0 := by
      intro zeroUnit
      have contradiction := unitComplexCoordinate_norm point nonzero
      rw [zeroUnit, norm_zero] at contradiction
      norm_num at contradiction
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp point profileSmooth).mul
      (contDiffAt_complex_zpow (unitComplexCoordinate_contDiffAt point nonzero) unitNonzero mode.1)

end Grad.BoundaryLift

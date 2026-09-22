import ANR12DiskL2Radial
import BL8KernelBoundary

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.BoundaryTrace Grad.BoundaryLift

/-- The literal compact polar character test, defined on the full Cartesian
plane. Its apparent axis singularity is killed by the radial test support. -/
def radialTestLift (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (point : SpatialPlane) : ComplexEuclidean 1 :=
  ((test ‖point‖ : ℂ) * unitComplexCoordinate point ^ mode) • vector

theorem radialTestLift_support (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ) :
    tsupport (radialTestLift mode vector test) ⊆ (fun point : SpatialPlane => ‖point‖) ⁻¹' tsupport test := by
  apply closure_minimal
  · intro point member
    by_contra outside
    have zero := image_eq_zero_of_notMem_tsupport (f := test) outside
    exact member (by simp only [radialTestLift, zero, Complex.ofReal_zero, zero_mul, zero_smul])
  · exact (isClosed_tsupport test).preimage continuous_norm

theorem radialTestLift_compact (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (inside : tsupport test ⊆ Ioo (0 : ℝ) 1) : HasCompactSupport (radialTestLift mode vector test) := by
  apply (isCompact_closedBall (0 : SpatialPlane) 1).of_isClosed_subset (isClosed_tsupport _)
  intro point member
  have radius := inside (radialTestLift_support mode vector test member)
  simpa only [Metric.mem_closedBall, dist_zero_right] using radius.2.le

theorem radialTestLift_inside (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (inside : tsupport test ⊆ Ioo (0 : ℝ) 1) : tsupport (radialTestLift mode vector test) ⊆ openUnitDisk := by
  intro point member
  exact (inside (radialTestLift_support mode vector test member)).2

theorem radialTestLift_smooth (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (smooth : ContDiff ℝ ∞ test) (inside : tsupport test ⊆ Ioo (0 : ℝ) 1) :
    ContDiff ℝ ∞ (radialTestLift mode vector test) := by
  rw [contDiff_iff_contDiffAt]
  intro point
  by_cases zero : point = 0
  · subst point
    have zeroOutside : (0 : ℝ) ∉ tsupport test := fun member => (inside member).1.false
    have profileZero : ∀ᶠ radius in 𝓝 (0 : ℝ), test radius = 0 := by
      filter_upwards [(isClosed_tsupport test).isOpen_compl.mem_nhds zeroOutside] with radius outside
      exact image_eq_zero_of_notMem_tsupport outside
    have radiusZero : ∀ᶠ point : SpatialPlane in 𝓝 0, test ‖point‖ = 0 := by
      exact (continuous_norm.tendsto (0 : SpatialPlane)).eventually (by simpa only [norm_zero] using profileZero)
    apply (contDiffAt_const (c := (0 : ComplexEuclidean 1))).congr_of_eventuallyEq
    filter_upwards [radiusZero] with point zeroAt
    simp only [radialTestLift, zeroAt, Complex.ofReal_zero, zero_mul, zero_smul]
  · have normSmooth : ContDiffAt ℝ ∞ (fun point : SpatialPlane => ‖point‖) point := contDiffAt_norm ℝ zero
    have unitNonzero : unitComplexCoordinate point ≠ 0 := by
      intro vanished
      have normOne := unitComplexCoordinate_norm point zero
      rw [vanished, norm_zero] at normOne
      norm_num at normOne
    exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp point (smooth.contDiffAt.comp point normSmooth)).mul
      (contDiffAt_complex_zpow (unitComplexCoordinate_contDiffAt point zero) unitNonzero mode)).smul contDiffAt_const

theorem radialTestLift_polar (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (radius : ℝ) (positive : 0 < radius) (angle : ℝ) :
    radialTestLift mode vector test (polarPlane (radius, angle)) =
      ((test radius : ℂ) * fourier mode (angle : CellCircle)) • vector := by
  have polar : polarPlane (radius, angle) = radius • boundaryCirclePoint (angle : CellCircle) := by
    rw [boundaryCirclePoint_coe, polarPlane_eq]
    rfl
  unfold radialTestLift
  rw [polarPlane_norm, abs_of_nonneg positive.le, polar,
    unitComplexCoordinate_polar radius positive, circle_zpow_fourier]

end Grad.CircularHighRegularity

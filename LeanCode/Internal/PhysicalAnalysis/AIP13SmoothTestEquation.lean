import AIP12LocalizedSupport

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace Grad.InteriorPeriodization
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.DiskExtension.Operator Grad.FourierGrade Grad.COR12Extension
open Grad.InteriorLocalization Grad.CircularHighRegularity Grad.PDEBootstrap

theorem periodizationCutoff_germ (point : SpatialPlane) (inside : point ∈ tsupport interiorCutoff.toFun) :
    periodizationCutoff.toFun =ᶠ[𝓝 point] (fun _ => 1) := by
  apply Grad.CompactCutoff.diskCutoff_germ (2 / 3 : ℝ) (1 / 24 : ℝ) (by norm_num) (by norm_num)
  rw [interiorCutoff_support] at inside
  have bound : ‖point‖ ≤ (2 / 3 : ℝ) := by simpa only [Metric.mem_closedBall, dist_zero_right] using inside
  simp only [Metric.mem_ball, dist_zero_right]
  linarith

theorem cutoff_test_laplacian_germ (test : SpatialPlane → ℝ) (point : SpatialPlane)
    (inside : point ∈ tsupport interiorCutoff.toFun) :
    testLaplacian (fun point => periodizationCutoff.toFun point * test point) point = testLaplacian test point := by
  have germ : (fun point => periodizationCutoff.toFun point * test point) =ᶠ[𝓝 point] test := by
    filter_upwards [periodizationCutoff_germ point inside] with source oneAt
    rw [oneAt, one_mul]
  have same := (germ.iteratedFDeriv ℝ 2).eq_of_nhds
  unfold testLaplacian Grad.WeakTesting.orderedTestDerivative
  simp only [Pi.add_apply]
  rw [same]

private theorem cutoffIntegral_test_laplacian (bulk : DiskL2 1)
    (vector : Grad.GenericCarriers.PhysicalValue 1) (test : SpatialPlane → ℝ) :
    diskIntegral (diskScalar interiorCutoff.toFun interiorCutoff.smooth bulk) vector
      (testLaplacian (fun point => periodizationCutoff.toFun point * test point)) =
    diskIntegral (diskScalar interiorCutoff.toFun interiorCutoff.smooth bulk) vector (testLaplacian test) := by
  unfold diskIntegral
  apply integral_congr_ae
  filter_upwards [diskScalar_ae interiorCutoff.toFun interiorCutoff.smooth bulk] with point multiplied
  by_cases inside : point ∈ tsupport interiorCutoff.toFun
  · rw [cutoff_test_laplacian_germ test point inside]
  · rw [multiplied, image_eq_zero_of_notMem_tsupport inside, zero_smul, inner_zero_right, smul_zero, smul_zero]

/-- The localized actual PDE can be tested against any globally smooth real
function: compact support follows from the field's already constructed cutoff. -/
theorem localizedDiskLaplacian_smooth_test (field : diskGrade) (laplacian : DiskL2 1)
    (equation : HasDiskWeakLaplacian (diskBulk field) laplacian)
    (vector : Grad.GenericCarriers.PhysicalValue 1) (test : SpatialPlane → ℝ)
    (smooth : ContDiff ℝ ∞ test) :
    diskIntegral (localizedDiskLaplacian field laplacian) vector test =
      diskIntegral (diskScalar interiorCutoff.toFun interiorCutoff.smooth (diskBulk field)) vector (testLaplacian test) := by
  have weak := localizedDiskLaplacian_weak field laplacian equation vector
    (fun point => periodizationCutoff.toFun point * test point)
    (periodizationCutoff.smooth.mul smooth) periodizationCutoff.compact.mul_right
  have leftIdentity := diskScalar_pairing periodizationCutoff.toFun periodizationCutoff.smooth
    (localizedDiskLaplacian field laplacian) vector test
  change diskIntegral (diskScalar periodizationCutoff.toFun periodizationCutoff.smooth
      (localizedDiskLaplacian field laplacian)) vector test =
    diskIntegral (localizedDiskLaplacian field laplacian) vector
      (fun point => periodizationCutoff.toFun point * test point) at leftIdentity
  rw [periodizationCutoff_absorbs_laplacian] at leftIdentity
  exact leftIdentity.trans (weak.trans (cutoffIntegral_test_laplacian (diskBulk field) vector test))

end Grad.InteriorPeriodization

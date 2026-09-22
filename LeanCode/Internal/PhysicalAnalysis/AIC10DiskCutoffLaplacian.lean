import AIC9DiskTestIdentities

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace Grad.InteriorLocalization
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.CircularHighWeak Grad.CircularHighRegularity

theorem localizedDiskLaplacian_integral (field : diskGrade) (laplacian : DiskL2 1)
    (vector : PhysicalValue 1) (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test)
    (compact : HasCompactSupport test) :
    diskIntegral (localizedDiskLaplacian field laplacian) vector test =
      diskIntegral laplacian vector (fun point => interiorCutoff.toFun point * test point) +
      2 * diskIntegral (diskGradX field) vector (fun point => firstTestDerivative 0 interiorCutoff.toFun point * test point) +
      2 * diskIntegral (diskGradY field) vector (fun point => firstTestDerivative 1 interiorCutoff.toFun point * test point) +
      diskIntegral (diskBulk field) vector (fun point => secondTestDerivative 0 interiorCutoff.toFun point * test point) +
      diskIntegral (diskBulk field) vector (fun point => secondTestDerivative 1 interiorCutoff.toFun point * test point) := by
  calc
    _ = apDiskPairing 1 0 vector test smooth compact (localizedDiskLaplacian field laplacian) :=
      diskIntegral_as_pairing _ vector test smooth compact
    _ = _ := by
      simp only [localizedDiskLaplacian, map_add, map_smul, smul_eq_mul,
        apDiskPairing_literal, diskScalar_pairing]
      rfl

theorem testLaplacian_integral (field : DiskL2 1) (vector : PhysicalValue 1)
    (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    diskIntegral field vector (testLaplacian test) =
      diskIntegral field vector (secondTestDerivative 0 test) +
        diskIntegral field vector (secondTestDerivative 1 test) := by
  rw [testLaplacian_second]
  exact diskIntegral_test_add field vector _ _ (secondTestDerivative_smooth 0 test smooth)
    (secondTestDerivative_smooth 1 test smooth) (secondTestDerivative_compact 0 test compact)
    (secondTestDerivative_compact 1 test compact)

theorem diskScalar_laplacian_integral (field : DiskL2 1) (vector : PhysicalValue 1)
    (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    diskIntegral (diskScalar interiorCutoff.toFun interiorCutoff.smooth field) vector (testLaplacian test) =
      diskIntegral field vector (fun point => interiorCutoff.toFun point * secondTestDerivative 0 test point) +
        diskIntegral field vector (fun point => interiorCutoff.toFun point * secondTestDerivative 1 test point) := by
  rw [testLaplacian_integral _ vector test smooth compact]
  exact congrArg₂ (fun first second : ℂ => first + second)
    (diskScalar_pairing interiorCutoff.toFun interiorCutoff.smooth field vector (secondTestDerivative 0 test))
    (diskScalar_pairing interiorCutoff.toFun interiorCutoff.smooth field vector (secondTestDerivative 1 test))

/-- Literal local Laplacian identity at H1 regularity. The source Laplacian
premise is the actual full-disk distribution predicate used by ANR. -/
theorem localizedDiskLaplacian_weak (field : diskGrade) (laplacian : DiskL2 1)
    (equation : HasDiskWeakLaplacian (diskBulk field) laplacian)
    (vector : PhysicalValue 1) (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test)
    (compact : HasCompactSupport test) :
    diskIntegral (localizedDiskLaplacian field laplacian) vector test =
      diskIntegral (diskScalar interiorCutoff.toFun interiorCutoff.smooth (diskBulk field)) vector (testLaplacian test) := by
  have xWeak : diskIntegral (diskGradX field) vector
      (fun point => firstTestDerivative 0 interiorCutoff.toFun point * test point) =
      -diskIntegral (diskBulk field) vector (firstTestDerivative 0
        (fun point => firstTestDerivative 0 interiorCutoff.toFun point * test point)) :=
    diskGradient_weak 0 field vector _
      ((firstTestDerivative_smooth 0 _ interiorCutoff.smooth).mul smooth)
      ((firstTestDerivative_compact 0 _ interiorCutoff.compact).mul_right)
      (tsupport_mul_subset_left.trans ((firstTestDerivative_supported 0 _).trans interiorCutoff_supported))
  have yWeak : diskIntegral (diskGradY field) vector
      (fun point => firstTestDerivative 1 interiorCutoff.toFun point * test point) =
      -diskIntegral (diskBulk field) vector (firstTestDerivative 1
        (fun point => firstTestDerivative 1 interiorCutoff.toFun point * test point)) :=
    diskGradient_weak 1 field vector _
      ((firstTestDerivative_smooth 1 _ interiorCutoff.smooth).mul smooth)
      ((firstTestDerivative_compact 1 _ interiorCutoff.compact).mul_right)
      (tsupport_mul_subset_left.trans ((firstTestDerivative_supported 1 _).trans interiorCutoff_supported))
  have laplacianWeak : diskIntegral laplacian vector (fun point => interiorCutoff.toFun point * test point) =
      diskIntegral (diskBulk field) vector (testLaplacian (fun point => interiorCutoff.toFun point * test point)) :=
    equation vector _ (interiorCutoff.smooth.mul smooth) interiorCutoff.compact.mul_right
      (tsupport_mul_subset_left.trans interiorCutoff_supported)
  have expansion := localizedDiskLaplacian_integral field laplacian vector test smooth compact
  have laplacianSplit := testLaplacian_integral (diskBulk field) vector
    (fun point => interiorCutoff.toFun point * test point)
    (interiorCutoff.smooth.mul smooth) interiorCutoff.compact.mul_right
  have targetSplit := diskScalar_laplacian_integral (diskBulk field) vector test smooth compact
  have cutoffX := cutoff_integral_identity (diskBulk field) vector 0 test smooth compact
  have cutoffY := cutoff_integral_identity (diskBulk field) vector 1 test smooth compact
  linear_combination expansion + 2 * xWeak + 2 * yWeak + laplacianWeak + laplacianSplit -
    targetSplit - cutoffX - cutoffY

end Grad.InteriorLocalization

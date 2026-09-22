import AIP15FourierTestLaplacian

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace Grad.InteriorPeriodization
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.DiskExtension.Operator Grad.FourierGrade Grad.COR12Extension
open Grad.InteriorLocalization Grad.CircularHighRegularity Grad.PDEBootstrap Grad.InteriorFourier

private theorem continuousTest_integrable (test : SpatialPlane → ℝ) (continuous : Continuous test)
    (field : DiskL2 1) : IntegrableOn (fun point => (test point : ℂ) * field point 0) openUnitDisk := by
  let closedTest : C(ClosedDisk, ComplexEuclidean 1) :=
    ⟨fun point => test point.val • EuclideanSpace.single 0 1,
      (continuous.comp continuous_subtype_val).smul continuous_const⟩
  have integrable := L2.integrable_inner (𝕜 := ℂ) (closedContinuousToDiskL2 closedTest) field
  apply integrable.congr
  filter_upwards [closedContinuousToDiskL2_ae closedTest,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point literal inside
  rw [literal, closedDiskLift, dif_pos (openDiskMembershipClosed point inside)]
  change inner ℂ (test point • EuclideanSpace.single 0 1) (field point) = _
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (test point) (EuclideanSpace.single 0 1), inner_smul_real_left]
  simp only [EuclideanSpace.inner_single_left, map_one, one_mul]
  rfl

private theorem diskIntegral_e0 (test : SpatialPlane → ℝ) (field : DiskL2 1) :
    diskIntegral field (EuclideanSpace.single 0 1) test =
      ∫ point in openUnitDisk, (test point : ℂ) * field point 0 := by
  unfold diskIntegral
  apply integral_congr_ae
  filter_upwards with point
  simp only [EuclideanSpace.inner_single_left, map_one, one_mul]
  rfl

theorem actualDiskCoefficient_pairing (firstMode secondMode : ℤ) (field : DiskL2 1) :
    actualDiskCoefficient firstMode secondMode field = (1 / 16 : ℂ) *
      (diskIntegral field (EuclideanSpace.single 0 1) (diskCos firstMode secondMode) +
        Complex.I * diskIntegral field (EuclideanSpace.single 0 1) (diskSin firstMode secondMode)) := by
  rw [actualDiskCoefficient_integral, diskIntegral_e0, diskIntegral_e0]
  have realIntegrable := continuousTest_integrable _ (diskCos_smooth firstMode secondMode).continuous field
  have imaginaryIntegrable := continuousTest_integrable _ (diskSin_smooth firstMode secondMode).continuous field
  have integrand (point : SpatialPlane) : negativeDiskCharacter firstMode secondMode point * field point 0 =
      (diskCos firstMode secondMode point : ℂ) * field point 0 +
        Complex.I * ((diskSin firstMode secondMode point : ℂ) * field point 0) := by
    rw [negativeDiskCharacter_literal]
    ring
  simp_rw [integrand]
  rw [integral_add realIntegrable (imaginaryIntegrable.const_mul Complex.I), integral_const_mul]

private theorem diskIntegral_test_const (scalar : ℝ) (test : SpatialPlane → ℝ)
    (field : DiskL2 1) :
    diskIntegral field (EuclideanSpace.single 0 1) (fun point => scalar * test point) =
      (scalar : ℂ) * diskIntegral field (EuclideanSpace.single 0 1) test := by
  rw [diskIntegral_e0, diskIntegral_e0]
  simp_rw [Complex.ofReal_mul, mul_assoc]
  exact integral_const_mul _ _

private theorem localizedEigenfunction (field : diskGrade) (laplacian : DiskL2 1)
    (equation : HasDiskWeakLaplacian (diskBulk field) laplacian)
    (test : SpatialPlane → ℝ) (smooth : ContDiff ℝ ∞ test) (eigenvalue : ℝ)
    (eigenfunction : testLaplacian test = fun point => eigenvalue * test point) :
    diskIntegral (localizedDiskLaplacian field laplacian) (EuclideanSpace.single 0 1) test =
      (eigenvalue : ℂ) * diskIntegral
        (diskScalar interiorCutoff.toFun interiorCutoff.smooth (diskBulk field)) (EuclideanSpace.single 0 1) test :=
  (localizedDiskLaplacian_smooth_test field laplacian equation (EuclideanSpace.single 0 1) test smooth).trans
    ((congrArg (diskIntegral (diskScalar interiorCutoff.toFun interiorCutoff.smooth (diskBulk field))
      (EuclideanSpace.single 0 1)) eigenfunction).trans (diskIntegral_test_const eigenvalue test _))

private theorem highDiskBulk_literal (field : highDiskGrade) : highDiskBulk field = diskBulk field.val := rfl

theorem localizedFourier_cos (parameter : ℝ) (source : highDiskL2) (mode : FourierMode) :
    diskIntegral (localizedDiskLaplacian (highRobinWeakInverse parameter source).val
      (weakLaplacianValue parameter source)) (EuclideanSpace.single 0 1) (diskCos mode.1 mode.2.1) =
    (-diskFrequencySquare mode : ℂ) * diskIntegral
      (diskScalar interiorCutoff.toFun interiorCutoff.smooth (highDiskBulk (highRobinWeakInverse parameter source)))
      (EuclideanSpace.single 0 1) (diskCos mode.1 mode.2.1) := by
  simpa only [Complex.ofReal_neg, highDiskBulk_literal] using localizedEigenfunction (highRobinWeakInverse parameter source).val (weakLaplacianValue parameter source)
    (weakInverse_distribution parameter source) (diskCos mode.1 mode.2.1) (diskCos_smooth mode.1 mode.2.1)
    (-diskFrequencySquare mode) (funext (diskCos_laplacian mode))

theorem localizedFourier_sin (parameter : ℝ) (source : highDiskL2) (mode : FourierMode) :
    diskIntegral (localizedDiskLaplacian (highRobinWeakInverse parameter source).val
      (weakLaplacianValue parameter source)) (EuclideanSpace.single 0 1) (diskSin mode.1 mode.2.1) =
    (-diskFrequencySquare mode : ℂ) * diskIntegral
      (diskScalar interiorCutoff.toFun interiorCutoff.smooth (highDiskBulk (highRobinWeakInverse parameter source)))
      (EuclideanSpace.single 0 1) (diskSin mode.1 mode.2.1) := by
  simpa only [Complex.ofReal_neg, highDiskBulk_literal] using localizedEigenfunction (highRobinWeakInverse parameter source).val (weakLaplacianValue parameter source)
    (weakInverse_distribution parameter source) (diskSin mode.1 mode.2.1) (diskSin_smooth mode.1 mode.2.1)
    (-diskFrequencySquare mode) (funext (diskSin_laplacian mode))

end Grad.InteriorPeriodization

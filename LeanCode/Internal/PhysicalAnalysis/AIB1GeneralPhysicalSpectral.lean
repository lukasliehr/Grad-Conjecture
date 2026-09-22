import AIP17ActualSpectralEquation

noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace Grad.OrdinaryInteriorBootstrap
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.InteriorPeriodization Grad.InteriorLocalization Grad.CircularHighRegularity
open Grad.PDEBootstrap Grad.InteriorFourier Grad.FourierGrade

private theorem diskIntegral_e0 (test : SpatialPlane → ℝ) (field : DiskL2 1) :
    diskIntegral field (EuclideanSpace.single 0 1) test =
      ∫ point in openUnitDisk, (test point : ℂ) * field point 0 := by
  unfold diskIntegral
  apply integral_congr_ae
  filter_upwards with point
  simp only [EuclideanSpace.inner_single_left, map_one, one_mul]
  rfl

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

private theorem combineEigen (field laplacian : DiskL2 1) (firstMode secondMode : ℤ) (eigenvalue : ℂ)
    (realEquation : diskIntegral laplacian (EuclideanSpace.single 0 1) (diskCos firstMode secondMode) =
      eigenvalue * diskIntegral field (EuclideanSpace.single 0 1) (diskCos firstMode secondMode))
    (imaginaryEquation : diskIntegral laplacian (EuclideanSpace.single 0 1) (diskSin firstMode secondMode) =
      eigenvalue * diskIntegral field (EuclideanSpace.single 0 1) (diskSin firstMode secondMode)) :
    actualDiskCoefficient firstMode secondMode laplacian = eigenvalue * actualDiskCoefficient firstMode secondMode field := by
  rw [actualDiskCoefficient_pairing, actualDiskCoefficient_pairing, realEquation, imaginaryEquation]
  ring

theorem localizedDiskCoefficient_laplacian (field : diskGrade) (laplacian : DiskL2 1)
    (equation : HasDiskWeakLaplacian (diskBulk field) laplacian) (mode : FourierMode) :
    actualDiskCoefficient mode.1 mode.2.1 (localizedDiskLaplacian field laplacian) =
      (-diskFrequencySquare mode : ℂ) * actualDiskCoefficient mode.1 mode.2.1
        (diskScalar interiorCutoff.toFun interiorCutoff.smooth (diskBulk field)) := by
  have realEquation := localizedEigenfunction field laplacian equation
    (diskCos mode.1 mode.2.1) (diskCos_smooth mode.1 mode.2.1)
    (-diskFrequencySquare mode) (funext (diskCos_laplacian mode))
  have imaginaryEquation := localizedEigenfunction field laplacian equation
    (diskSin mode.1 mode.2.1) (diskSin_smooth mode.1 mode.2.1)
    (-diskFrequencySquare mode) (funext (diskSin_laplacian mode))
  simp only [Complex.ofReal_neg] at realEquation imaginaryEquation
  exact combineEigen _ _ _ _ _ realEquation imaginaryEquation

private theorem supportedFourier_spectral (parameters : PhaseParameters) (value forcing : DiskL2 1)
    (supportedValue : diskScalar periodizationCutoff.toFun periodizationCutoff.smooth value = value)
    (supportedForcing : diskScalar periodizationCutoff.toFun periodizationCutoff.smooth forcing = forcing)
    (coefficientEquation : ∀ mode : FourierMode, actualDiskCoefficient mode.1 mode.2.1 forcing =
      (-diskFrequencySquare mode : ℂ) * actualDiskCoefficient mode.1 mode.2.1 value) (mode : FourierMode) :
    (frequencyWeight mode : ℂ) ^ 2 • coefficient 0 (diskFourier parameters value) mode =
      coefficient 0 (diskFourier parameters value) mode - coefficient 0 (diskFourier parameters forcing) mode := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  change (frequencyWeight mode : ℂ) ^ 2 *
    (coefficient 0 (diskFourier parameters (value)) mode) 0 =
    (coefficient 0 (diskFourier parameters (value)) mode) 0 -
      (coefficient 0 (diskFourier parameters (forcing)) mode) 0
  rw [diskFourier_supported_coefficient parameters (value)
      supportedValue mode,
    diskFourier_supported_coefficient parameters (forcing)
      supportedForcing mode]
  by_cases zero : mode.2.2 = 0
  · simp only [if_pos zero]
    rw [coefficientEquation mode]
    have frequency : (frequencyWeight mode : ℂ) ^ 2 = (diskFrequencySquare mode : ℂ) + 1 := by
      have realIdentity : frequencyWeight mode ^ 2 = diskFrequencySquare mode + 1 := by
        rw [frequencySquare_decomposition]
        simp only [cellFrequencySquare, coordinateSquare, frequencyVector_two, zero, Int.cast_zero,
          abs_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
      exact_mod_cast realIdentity
    rw [frequency]
    ring
  · simp only [if_neg zero, mul_zero, sub_self]


theorem localizedDiskFourier_spectral (parameters : PhaseParameters) (field : diskGrade) (laplacian : DiskL2 1)
    (equation : HasDiskWeakLaplacian (diskBulk field) laplacian) (mode : FourierMode) :
    (frequencyWeight mode : ℂ) ^ 2 • coefficient 0 (diskFourier parameters (diskScalar interiorCutoff.toFun interiorCutoff.smooth (diskBulk field))) mode =
      coefficient 0 (diskFourier parameters (diskScalar interiorCutoff.toFun interiorCutoff.smooth (diskBulk field))) mode -
        coefficient 0 (diskFourier parameters (localizedDiskLaplacian field laplacian)) mode :=
  supportedFourier_spectral parameters _ _ (periodizationCutoff_absorbs_bulk _)
    (periodizationCutoff_absorbs_laplacian field laplacian)
    (localizedDiskCoefficient_laplacian field laplacian equation) mode

end Grad.OrdinaryInteriorBootstrap

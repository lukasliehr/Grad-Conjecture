import AIP16FourierPairing

noncomputable section
open Set MeasureTheory

namespace Grad.InteriorPeriodization
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.DiskExtension.Operator Grad.FourierGrade Grad.COR12Extension
open Grad.InteriorLocalization Grad.CircularHighRegularity Grad.PDEBootstrap Grad.InteriorFourier

def localizedDiskField (parameter : ℝ) (source : highDiskL2) : DiskL2 1 :=
  diskScalar interiorCutoff.toFun interiorCutoff.smooth (highDiskBulk (highRobinWeakInverse parameter source))

def localizedDiskRHS (parameter : ℝ) (source : highDiskL2) : DiskL2 1 :=
  localizedDiskLaplacian (highRobinWeakInverse parameter source).val (weakLaplacianValue parameter source)

private theorem combineEigen (field laplacian : DiskL2 1) (firstMode secondMode : ℤ) (eigenvalue : ℂ)
    (realEquation : diskIntegral laplacian (EuclideanSpace.single 0 1) (diskCos firstMode secondMode) =
      eigenvalue * diskIntegral field (EuclideanSpace.single 0 1) (diskCos firstMode secondMode))
    (imaginaryEquation : diskIntegral laplacian (EuclideanSpace.single 0 1) (diskSin firstMode secondMode) =
      eigenvalue * diskIntegral field (EuclideanSpace.single 0 1) (diskSin firstMode secondMode)) :
    actualDiskCoefficient firstMode secondMode laplacian = eigenvalue * actualDiskCoefficient firstMode secondMode field := by
  rw [actualDiskCoefficient_pairing, actualDiskCoefficient_pairing, realEquation, imaginaryEquation]
  ring

theorem actualDiskCoefficient_laplacian (parameter : ℝ) (source : highDiskL2) (mode : FourierMode) :
    actualDiskCoefficient mode.1 mode.2.1 (localizedDiskRHS parameter source) =
      (-diskFrequencySquare mode : ℂ) * actualDiskCoefficient mode.1 mode.2.1 (localizedDiskField parameter source) :=
  combineEigen (localizedDiskField parameter source) (localizedDiskRHS parameter source) mode.1 mode.2.1
    (-diskFrequencySquare mode : ℂ) (localizedFourier_cos parameter source mode) (localizedFourier_sin parameter source mode)


theorem actualDiskFourier_spectral (parameters : PhaseParameters) (parameter : ℝ)
    (source : highDiskL2) (mode : FourierMode) :
    (frequencyWeight mode : ℂ) ^ 2 • coefficient 0 (diskFourier parameters (localizedDiskField parameter source)) mode =
      coefficient 0 (diskFourier parameters (localizedDiskField parameter source)) mode -
        coefficient 0 (diskFourier parameters (localizedDiskRHS parameter source)) mode := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  change (frequencyWeight mode : ℂ) ^ 2 *
    (coefficient 0 (diskFourier parameters (localizedDiskField parameter source)) mode) 0 =
    (coefficient 0 (diskFourier parameters (localizedDiskField parameter source)) mode) 0 -
      (coefficient 0 (diskFourier parameters (localizedDiskRHS parameter source)) mode) 0
  rw [diskFourier_supported_coefficient parameters (localizedDiskField parameter source)
      (periodizationCutoff_absorbs_bulk _) mode,
    diskFourier_supported_coefficient parameters (localizedDiskRHS parameter source)
      (periodizationCutoff_absorbs_laplacian _ _) mode]
  by_cases zero : mode.2.2 = 0
  · simp only [if_pos zero]
    rw [actualDiskCoefficient_laplacian]
    have frequency : (frequencyWeight mode : ℂ) ^ 2 = (diskFrequencySquare mode : ℂ) + 1 := by
      have realIdentity : frequencyWeight mode ^ 2 = diskFrequencySquare mode + 1 := by
        rw [frequencySquare_decomposition]
        simp only [cellFrequencySquare, coordinateSquare, frequencyVector_two, zero, Int.cast_zero,
          abs_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
      exact_mod_cast realIdentity
    rw [frequency]
    ring
  · simp only [if_neg zero, mul_zero, sub_self]

/-- The actual weak inverse's localized field gains two Fourier derivatives.
The higher-grade representative has exactly the same base field. -/
theorem actualInteriorFourier_H2 (parameters : PhaseParameters) (parameter : ℝ) (source : highDiskL2) :
    ∃ higher : JGrade (ComplexEuclidean 1) 2,
      inclusion 2 0 (by omega) higher = diskFourier parameters (localizedDiskField parameter source) ∧
      ‖higher‖ ≤ ‖diskFourier parameters (localizedDiskRHS parameter source)‖ +
        ‖diskFourier parameters (localizedDiskField parameter source)‖ :=
  gainTwo_from_spectralEquation 0 _ _ _ (actualDiskFourier_spectral parameters parameter source)

end Grad.InteriorPeriodization

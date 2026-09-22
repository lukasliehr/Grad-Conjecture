import AIP14RealFourierTests
import AIF1FourierGain

noncomputable section
open Set MeasureTheory
open scoped ContDiff BigOperators

namespace Grad.InteriorPeriodization
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.DiskExtension.Operator Grad.FourierGrade Grad.COR12Extension
open Grad.InteriorLocalization Grad.CircularHighRegularity Grad.PDEBootstrap Grad.InteriorFourier

theorem diskPhase_direction_zero (firstMode secondMode : ℤ) :
    diskPhase firstMode secondMode (spatialDirection 0) = -Real.pi / 2 * (firstMode : ℝ) := by
  simp [diskPhase, spatialDirection, PiLp.proj_apply]

theorem diskPhase_direction_one (firstMode secondMode : ℤ) :
    diskPhase firstMode secondMode (spatialDirection 1) = -Real.pi / 2 * (secondMode : ℝ) := by
  simp [diskPhase, spatialDirection, PiLp.proj_apply]

theorem diskCos_laplacian (mode : FourierMode) (point : SpatialPlane) :
    testLaplacian (diskCos mode.1 mode.2.1) point =
      -diskFrequencySquare mode * diskCos mode.1 mode.2.1 point := by
  rw [testLaplacian_second]
  change secondTestDerivative 0 _ point + secondTestDerivative 1 _ point = _
  rw [second_diskCos, second_diskCos, diskPhase_direction_zero, diskPhase_direction_one]
  simp only [diskFrequencySquare, coordinateSquare, frequencyVector_zero, frequencyVector_one, sq_abs]
  ring

theorem diskSin_laplacian (mode : FourierMode) (point : SpatialPlane) :
    testLaplacian (diskSin mode.1 mode.2.1) point =
      -diskFrequencySquare mode * diskSin mode.1 mode.2.1 point := by
  rw [testLaplacian_second]
  change secondTestDerivative 0 _ point + secondTestDerivative 1 _ point = _
  rw [second_diskSin, second_diskSin, diskPhase_direction_zero, diskPhase_direction_one]
  simp only [diskFrequencySquare, coordinateSquare, frequencyVector_zero, frequencyVector_one, sq_abs]
  ring

theorem negativeDiskCharacter_literal (firstMode secondMode : ℤ) (point : SpatialPlane) :
    negativeDiskCharacter firstMode secondMode point =
      (diskCos firstMode secondMode point : ℂ) +
        (diskSin firstMode secondMode point : ℂ) * Complex.I := by
  have literal : torusCharacter (-firstMode, -secondMode, 0)
      (normalizedTorusPoint (point 0) (point 1) 0) = negativeDiskCharacter firstMode secondMode point := by
    rw [← normalizedSpatialPair]
    simp only [torusCharacter, modeVector, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
      Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue,
      Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton, fourier_zero,
      mul_one, negativeDiskCharacter]
  rw [← literal, torusCharacter_normalized_apply]
  have phase : Complex.I *
      (((Real.pi / 2) * ((-firstMode : ℤ) : ℂ)) * (point 0 : ℂ) +
       ((Real.pi / 2) * ((-secondMode : ℤ) : ℂ)) * (point 1 : ℂ) + (0 : ℂ) * 0) =
      (diskPhase firstMode secondMode point : ℂ) * Complex.I := by
    simp only [diskPhase, add_apply, smul_apply,
      PiLp.proj_apply, smul_eq_mul]
    push_cast
    ring
  norm_num only [Int.cast_zero, Complex.ofReal_zero, mul_zero] at phase ⊢
  rw [phase, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rfl

end Grad.InteriorPeriodization

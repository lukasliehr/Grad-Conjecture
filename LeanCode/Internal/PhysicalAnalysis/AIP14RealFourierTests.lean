import AIP13SmoothTestEquation

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace Grad.InteriorPeriodization
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.DiskExtension.Operator Grad.FourierGrade Grad.COR12Extension
open Grad.InteriorLocalization Grad.CircularHighRegularity Grad.PDEBootstrap

def diskPhase (firstMode secondMode : ℤ) : SpatialPlane →L[ℝ] ℝ :=
  (-Real.pi / 2 * (firstMode : ℝ)) • PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 +
    (-Real.pi / 2 * (secondMode : ℝ)) • PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1

def diskCos (firstMode secondMode : ℤ) (point : SpatialPlane) : ℝ :=
  Real.cos (diskPhase firstMode secondMode point)

def diskSin (firstMode secondMode : ℤ) (point : SpatialPlane) : ℝ :=
  Real.sin (diskPhase firstMode secondMode point)

theorem diskCos_smooth (firstMode secondMode : ℤ) : ContDiff ℝ ∞ (diskCos firstMode secondMode) :=
  (diskPhase firstMode secondMode).contDiff.cos

theorem diskSin_smooth (firstMode secondMode : ℤ) : ContDiff ℝ ∞ (diskSin firstMode secondMode) :=
  (diskPhase firstMode secondMode).contDiff.sin

theorem firstTestDerivative_fderiv (direction : Fin 2) (test : SpatialPlane → ℝ) (point : SpatialPlane) :
    firstTestDerivative direction test point = fderiv ℝ test point (spatialDirection direction) := by
  rw [firstTestDerivative_ordered]
  exact iteratedFDeriv_one_apply _

theorem first_diskCos (firstMode secondMode : ℤ) (direction : Fin 2) (point : SpatialPlane) :
    firstTestDerivative direction (diskCos firstMode secondMode) point =
      -diskSin firstMode secondMode point * diskPhase firstMode secondMode (spatialDirection direction) := by
  rw [firstTestDerivative_fderiv]
  have derivative : HasFDerivAt (diskCos firstMode secondMode)
      (-diskSin firstMode secondMode point • diskPhase firstMode secondMode) point :=
    ((diskPhase firstMode secondMode).hasFDerivAt (x := point)).cos
  rw [derivative.fderiv]
  rfl

theorem first_diskSin (firstMode secondMode : ℤ) (direction : Fin 2) (point : SpatialPlane) :
    firstTestDerivative direction (diskSin firstMode secondMode) point =
      diskCos firstMode secondMode point * diskPhase firstMode secondMode (spatialDirection direction) := by
  rw [firstTestDerivative_fderiv]
  have derivative : HasFDerivAt (diskSin firstMode secondMode)
      (diskCos firstMode secondMode point • diskPhase firstMode secondMode) point :=
    ((diskPhase firstMode secondMode).hasFDerivAt (x := point)).sin
  rw [derivative.fderiv]
  rfl

theorem second_diskCos (firstMode secondMode : ℤ) (direction : Fin 2) (point : SpatialPlane) :
    secondTestDerivative direction (diskCos firstMode secondMode) point =
      -(diskPhase firstMode secondMode (spatialDirection direction)) ^ 2 * diskCos firstMode secondMode point := by
  rw [← firstTestDerivative_repeat direction _ (diskCos_smooth firstMode secondMode)]
  have firstIdentity : firstTestDerivative direction (diskCos firstMode secondMode) =
      fun point => -diskSin firstMode secondMode point * diskPhase firstMode secondMode (spatialDirection direction) := by
    funext point
    exact first_diskCos firstMode secondMode direction point
  rw [firstIdentity, firstTestDerivative_fderiv]
  have derivative := (((diskPhase firstMode secondMode).hasFDerivAt (x := point)).sin.neg).mul_const
    (diskPhase firstMode secondMode (spatialDirection direction))
  dsimp only [diskCos, diskSin, Pi.neg_apply] at *
  rw [derivative.fderiv]
  simp only [smul_apply, neg_apply, smul_eq_mul]
  ring

theorem second_diskSin (firstMode secondMode : ℤ) (direction : Fin 2) (point : SpatialPlane) :
    secondTestDerivative direction (diskSin firstMode secondMode) point =
      -(diskPhase firstMode secondMode (spatialDirection direction)) ^ 2 * diskSin firstMode secondMode point := by
  rw [← firstTestDerivative_repeat direction _ (diskSin_smooth firstMode secondMode)]
  have firstIdentity : firstTestDerivative direction (diskSin firstMode secondMode) =
      fun point => diskCos firstMode secondMode point * diskPhase firstMode secondMode (spatialDirection direction) := by
    funext point
    exact first_diskSin firstMode secondMode direction point
  rw [firstIdentity, firstTestDerivative_fderiv]
  have derivative := (((diskPhase firstMode secondMode).hasFDerivAt (x := point)).cos).mul_const
    (diskPhase firstMode secondMode (spatialDirection direction))
  dsimp only [diskCos, diskSin] at *
  rw [derivative.fderiv]
  simp only [smul_apply, smul_eq_mul]
  ring

end Grad.InteriorPeriodization

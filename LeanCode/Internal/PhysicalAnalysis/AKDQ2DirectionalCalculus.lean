import AKDQ1ProjectedAngularIdentity
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section
open scoped ContDiff

namespace Grad.PhysicalEquilibrium

variable {Domain Value : Type*} [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]

/-- Actual variable-direction derivative of a field. -/
def directionalAction (field : Domain → Value) (direction : Domain → Domain) : Domain → Value :=
  fun point => fderiv ℝ field point (direction point)

theorem directionalAction_fderiv (field : Domain → Value) (direction : Domain → Domain)
    (point : Domain) (smooth : ContDiffAt ℝ ∞ field point)
    (directionDiff : DifferentiableAt ℝ direction point) (increment : Domain) :
    fderiv ℝ (directionalAction field direction) point increment =
      fderiv ℝ field point (fderiv ℝ direction point increment) +
        fderiv ℝ (fderiv ℝ field) point increment (direction point) := by
  have first := ((smooth.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have derivative := first.clm_apply directionDiff.hasFDerivAt
  exact congrArg (fun mapping : Domain →L[ℝ] Value => mapping increment) derivative.fderiv

theorem directionalAction_contDiffOn (field : Domain → Value) (direction : Domain → Domain)
    (domain : Set Domain) (domainOpen : IsOpen domain)
    (smooth : ContDiffOn ℝ ∞ field domain) (directionSmooth : ContDiffOn ℝ ∞ direction domain) :
    ContDiffOn ℝ ∞ (directionalAction field direction) domain :=
  (smooth.fderiv_of_isOpen (m := ∞) domainOpen (by simp)).clm_apply directionSmooth

/-- Commuting actual vector fields give commuting actions. The second
Fréchet derivative is symmetric by the real C-infinity hypothesis. -/
theorem directionalAction_commute (field : Domain → Value)
    (first second : Domain → Domain) (point : Domain)
    (smooth : ContDiffAt ℝ ∞ field point)
    (firstDiff : DifferentiableAt ℝ first point)
    (secondDiff : DifferentiableAt ℝ second point)
    (commute : fderiv ℝ first point (second point) = fderiv ℝ second point (first point)) :
    directionalAction (directionalAction field first) second point =
      directionalAction (directionalAction field second) first point := by
  change fderiv ℝ (directionalAction field first) point (second point) =
    fderiv ℝ (directionalAction field second) point (first point)
  rw [directionalAction_fderiv field first point smooth firstDiff,
    directionalAction_fderiv field second point smooth secondDiff, commute,
    (smooth.isSymmSndFDerivAt (by simp; norm_cast)).eq (second point) (first point)]

end Grad.PhysicalEquilibrium

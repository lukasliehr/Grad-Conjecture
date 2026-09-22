import APR1OriginalDiskCore
import AIP1OriginalZeroGrade

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace Grad.OrdinaryDiskForward
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak
open Grad.OrdinaryDiskReconstruction Grad.InteriorPeriodization Grad.NonlinearQuotientBounds

/-- The unchanged original inverse-phase single-cell core at every grade. -/
def normalizedGradeCore (parameters : PhaseParameters) (grade : ℕ) :
    ClosedJet 1 →ₗ[ℂ] GradeCore parameters 1 grade :=
  GradeCore.ofCoreLinear.comp (normalizedSingleCore parameters)

theorem normalizedGradeCore_phase (parameters : PhaseParameters) (grade : ℕ) (field : ClosedJet 1) :
    phaseZeroCore parameters grade (normalizedGradeCore parameters grade field) = field :=
  phaseWeightedJet_inverse_left parameters 0 field

/-- The literal original M2 grade is exactly the ordinary disk H^q norm
after the original phase is cancelled at cell zero; lambda0=1 at every q. -/
theorem normalizedGradeCore_norm (parameters : PhaseParameters) (grade : ℕ) (field : ClosedJet 1) :
    ‖normalizedGradeCore parameters grade field‖ = ‖unitSobolevRow grade field‖ := by
  rw [gradeCore_norm_eq_cartesianGradeSeminorm, cartesianGradeSeminorm_apply,
    gradeCoreCoordinates_apply]
  have coordinates : cartesianGradeCoordinates parameters grade
      (normalizedSingleCore parameters field) =
      lp.single (E := fun _ : ℤ => CartesianGradeRow 1 grade) 2 0 (cellGradeRowLinear (grade := grade) parameters 0
        (phaseInverseWeightedJet parameters 0 field)) := by
    apply Subtype.ext
    funext cell
    by_cases zero : cell = 0
    · subst cell
      simp [cartesianGradeCoordinates, rawCartesianGradeCoordinates,
        normalizedSingleCore, singletonCore]
    · simp [cartesianGradeCoordinates, rawCartesianGradeCoordinates,
        normalizedSingleCore, singletonCore, zero]
  change ‖cartesianGradeCoordinates parameters grade (normalizedSingleCore parameters field)‖ = _
  rw [coordinates, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
  have row := phaseZero_row parameters grade (phaseInverseWeightedJet parameters 0 field)
  rw [phaseWeightedJet_inverse_left] at row
  exact (congrArg norm row).symm

def normalizedGradeCoreInto (parameters : PhaseParameters) (grade : ℕ) :
    ClosedJet 1 →ₗ[ℂ] AGrade parameters 1 grade :=
  (aGradeEta parameters).toLinearMap.comp (normalizedGradeCore parameters grade)

theorem normalizedGradeCoreInto_norm (parameters : PhaseParameters) (grade : ℕ) (field : ClosedJet 1) :
    ‖normalizedGradeCoreInto parameters grade field‖ = ‖unitDiskCoreInto grade field‖ := by
  change ‖aGradeEta parameters (normalizedGradeCore parameters grade field)‖ = _
  rw [aGradeEta_norm, normalizedGradeCore_norm, unitDiskCore_norm]

theorem ordinaryCore_injective (grade : ℕ) : Function.Injective (unitDiskCoreInto grade) := by
  intro first second equality
  apply closedL2Core_injective
  exact (unitDiskBulk_core grade first).symm.trans
    ((congrArg (unitDiskBulk grade) equality).trans (unitDiskBulk_core grade second))

end Grad.OrdinaryDiskForward

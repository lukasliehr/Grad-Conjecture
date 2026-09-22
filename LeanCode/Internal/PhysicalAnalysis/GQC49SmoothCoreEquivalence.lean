import GQC42CompensatedTransfer

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.GaugeTransfer

section Current

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge))
    (laws : ∀ grade, ActualProjectionLaws admissible gauge grade)

def compensatedCoreForward : circularCompensatedCore admissible →ₗ[ℂ]
    currentCompensatedCore admissible gauge coherent where
  toFun data := ⟨compensatedForward admissible gauge coherent inverseCoherent data.val,
    compensatedForward_mem admissible gauge coherent inverseCoherent laws data⟩
  map_add' first second := by
    apply Subtype.ext
    exact (compensatedForward admissible gauge coherent inverseCoherent).map_add first.val second.val
  map_smul' scalar data := by
    apply Subtype.ext
    exact (compensatedForward admissible gauge coherent inverseCoherent).map_smul scalar data.val

def compensatedCoreBackward : currentCompensatedCore admissible gauge coherent →ₗ[ℂ]
    circularCompensatedCore admissible where
  toFun data := ⟨compensatedBackward L sigma gamma ell data.val,
    compensatedBackward_mem admissible gauge coherent data⟩
  map_add' first second := by
    apply Subtype.ext
    exact (compensatedBackward L sigma gamma ell).map_add first.val second.val
  map_smul' scalar data := by
    apply Subtype.ext
    exact (compensatedBackward L sigma gamma ell).map_smul scalar data.val

/-- The genuine smooth compensated-core isomorphism, using the actual
constructed complement inverse and the literal fixed circular inverse. -/
def compensatedCoreEquivalence : circularCompensatedCore admissible ≃ₗ[ℂ]
    currentCompensatedCore admissible gauge coherent where
  toLinearMap := compensatedCoreForward admissible gauge coherent inverseCoherent laws
  invFun := compensatedCoreBackward admissible gauge coherent
  left_inv data := Subtype.ext (compensatedBackward_forward admissible gauge coherent inverseCoherent laws data)
  right_inv data := Subtype.ext (compensatedForward_backward admissible gauge coherent inverseCoherent laws data)

theorem compensatedCoreEquivalence_apply (data : circularCompensatedCore admissible) :
    (compensatedCoreEquivalence admissible gauge coherent inverseCoherent laws data).val =
      compensatedForward admissible gauge coherent inverseCoherent data.val := rfl

theorem compensatedCoreEquivalence_symm_apply (data : currentCompensatedCore admissible gauge coherent) :
    ((compensatedCoreEquivalence admissible gauge coherent inverseCoherent laws).symm data).val =
      compensatedBackward L sigma gamma ell data.val := rfl

end Current

end Grad.GaugeCoefficients.Physical.Compensated

import GQC41CompensatedCore

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.GaugeTransfer

def compensatedBackward (L sigma gamma ell : ℝ) :
    CompensatedData L sigma gamma ell →ₗ[ℂ] CompensatedData L sigma gamma ell :=
  LinearMap.prodMap LinearMap.id (apSmoothCircle L sigma gamma ell)

theorem compensatedBackward_reconstruct {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : CompensatedData L sigma gamma ell)
    (meanZero : APSmoothMeanZero admissible data.1) :
    compensatedReconstruct admissible (compensatedBackward L sigma gamma ell data) =
      apSmoothCircle L sigma gamma ell (compensatedReconstruct admissible data) := by
  change apSmoothCovariant admissible data.1 + apSmoothCircle L sigma gamma ell data.2 =
    apSmoothCircle L sigma gamma ell (apSmoothCovariant admissible data.1 + data.2)
  exact (congrArg (fun field : APSmooth L sigma gamma ell 3 =>
    field + apSmoothCircle L sigma gamma ell data.2)
      (apSmoothCovariant_circle admissible data.1 meanZero).symm).trans
        (map_add (apSmoothCircle L sigma gamma ell) (apSmoothCovariant admissible data.1) data.2).symm

section Current

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge))

/-- Literal AO20. Θ is fixed and the actual E_a G_a w is removed from
the remainder. No projection is inserted into the nonlinear residual. -/
def compensatedForward : CompensatedData L sigma gamma ell →ₗ[ℂ] CompensatedData L sigma gamma ell :=
  (LinearMap.fst ℂ _ _).prod (LinearMap.snd ℂ _ _ -
    (apSmoothExtension admissible gauge coherent inverseCoherent).comp
      ((apSmoothGauge admissible gauge coherent).comp (compensatedReconstruct admissible)))

theorem compensatedForward_reconstruct (data : CompensatedData L sigma gamma ell) :
    compensatedReconstruct admissible (compensatedForward admissible gauge coherent inverseCoherent data) =
      apSmoothCurrent admissible gauge coherent inverseCoherent (compensatedReconstruct admissible data) := by
  change apSmoothCovariant admissible data.1 + (data.2 -
    apSmoothExtension admissible gauge coherent inverseCoherent
      (apSmoothGauge admissible gauge coherent (compensatedReconstruct admissible data))) =
    (apSmoothCovariant admissible data.1 + data.2) -
      apSmoothExtension admissible gauge coherent inverseCoherent
        (apSmoothGauge admissible gauge coherent (compensatedReconstruct admissible data))
  abel

variable (laws : ∀ grade, ActualProjectionLaws admissible gauge grade)

include laws in
theorem compensatedForward_mem (data : circularCompensatedCore admissible) :
    compensatedForward admissible gauge coherent inverseCoherent data.val ∈
      currentCompensatedCore admissible gauge coherent := by
  have original := (mem_compensatedFlatCore admissible data.val).mp data.property.1
  constructor
  · apply (mem_compensatedFlatCore admissible _).mpr
    refine ⟨original.1, ?_⟩
    rw [compensatedForward_reconstruct]
    exact apSmoothCurrent_preserves_firstJet admissible gauge coherent inverseCoherent _ original.2
  · change apSmoothGauge admissible gauge coherent
      (compensatedReconstruct admissible (compensatedForward admissible gauge coherent inverseCoherent data.val)) = 0
    exact (congrArg (apSmoothGauge admissible gauge coherent)
      (compensatedForward_reconstruct admissible gauge coherent inverseCoherent data.val)).trans
        (apSmoothCurrent_gauge_zero admissible gauge coherent inverseCoherent laws _)

theorem compensatedBackward_mem (data : currentCompensatedCore admissible gauge coherent) :
    compensatedBackward L sigma gamma ell data.val ∈ circularCompensatedCore admissible := by
  have original := (mem_compensatedFlatCore admissible data.val).mp data.property.1
  constructor
  · apply (mem_compensatedFlatCore admissible _).mpr
    refine ⟨original.1, ?_⟩
    rw [compensatedBackward_reconstruct admissible data.val original.1.1]
    exact apSmoothCircle_preserves_firstJet admissible _ original.2
  · change apSmoothComplement L sigma gamma ell
      (compensatedReconstruct admissible (compensatedBackward L sigma gamma ell data.val)) = 0
    rw [compensatedBackward_reconstruct admissible data.val original.1.1]
    exact (apSmoothCircle_fixed_iff _).mp (apSmoothCircle_idempotent admissible _)

include laws in
theorem compensatedBackward_forward (data : circularCompensatedCore admissible) :
    compensatedBackward L sigma gamma ell (compensatedForward admissible gauge coherent inverseCoherent data.val) = data.val := by
  have original := (mem_compensatedFlatCore admissible data.val).mp data.property.1
  refine compensatedData_ext admissible (first := compensatedBackward L sigma gamma ell
    (compensatedForward admissible gauge coherent inverseCoherent data.val)) (second := data.val) rfl ?_
  calc
    _ = apSmoothCircle L sigma gamma ell
        (compensatedReconstruct admissible (compensatedForward admissible gauge coherent inverseCoherent data.val)) :=
      compensatedBackward_reconstruct admissible _ original.1.1
    _ = apSmoothCircle L sigma gamma ell
        (apSmoothCurrent admissible gauge coherent inverseCoherent (compensatedReconstruct admissible data.val)) :=
      congrArg (apSmoothCircle L sigma gamma ell) (compensatedForward_reconstruct admissible gauge coherent inverseCoherent data.val)
    _ = apSmoothCircle L sigma gamma ell (compensatedReconstruct admissible data.val) :=
      apSmoothCurrent_circle_left admissible gauge coherent inverseCoherent laws _
    _ = compensatedReconstruct admissible data.val := (apSmoothCircle_fixed_iff _).mpr data.property.2

include laws in
theorem compensatedForward_backward (data : currentCompensatedCore admissible gauge coherent) :
    compensatedForward admissible gauge coherent inverseCoherent (compensatedBackward L sigma gamma ell data.val) = data.val := by
  have original := (mem_compensatedFlatCore admissible data.val).mp data.property.1
  refine compensatedData_ext admissible (first := compensatedForward admissible gauge coherent inverseCoherent
    (compensatedBackward L sigma gamma ell data.val)) (second := data.val) rfl ?_
  calc
    _ = apSmoothCurrent admissible gauge coherent inverseCoherent
        (compensatedReconstruct admissible (compensatedBackward L sigma gamma ell data.val)) :=
      compensatedForward_reconstruct admissible gauge coherent inverseCoherent _
    _ = apSmoothCurrent admissible gauge coherent inverseCoherent
        (apSmoothCircle L sigma gamma ell (compensatedReconstruct admissible data.val)) :=
      congrArg (apSmoothCurrent admissible gauge coherent inverseCoherent)
        (compensatedBackward_reconstruct admissible data.val original.1.1)
    _ = apSmoothCurrent admissible gauge coherent inverseCoherent (compensatedReconstruct admissible data.val) :=
      apSmoothCurrent_circle_right admissible gauge coherent inverseCoherent laws _
    _ = compensatedReconstruct admissible data.val :=
      apSmoothCurrent_fixed admissible gauge coherent inverseCoherent _ data.property.2

end Current

end Grad.GaugeCoefficients.Physical.Compensated

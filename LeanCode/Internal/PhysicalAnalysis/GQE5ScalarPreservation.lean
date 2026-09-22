import GQE4SmoothContractions

noncomputable section
set_option maxHeartbeats 300000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation

def physicalPsi {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) :
    CompensatedData L sigma gamma ell →ₗ[ℂ] APSmooth L sigma gamma ell 1 :=
  (apSmoothRotation admissible 1).comp (LinearMap.fst ℂ _ _)

def physicalScalar {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) :
    CompensatedData L sigma gamma ell →ₗ[ℂ] APSmooth L sigma gamma ell 1 :=
  physicalPsi admissible + (apSmoothProjectedTangent admissible).comp (compensatedReconstruct admissible)

def physicalRadial {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) :
    CompensatedData L sigma gamma ell →ₗ[ℂ] APSmooth L sigma gamma ell 1 :=
  (apSmoothRadial admissible).comp (compensatedReconstruct admissible)

theorem tangentRowJet_covariant (frequency : ℂ) (field : ClosedJet 1) :
    apProductJet tangentRowJet (covariantJet frequency field) = Grad.NonlinearRange.rotationJet field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  change (apProductJet tangentRowJet (covariantJet frequency field)).value point 0 =
    (Grad.NonlinearRange.rotationJet field).value point 0
  rw [apProductJet_value, tangentRowJet_value]
  exact covariantJet_tangent _ _ point

theorem apSmoothTangent_covariant {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 1) :
    apSmoothTangent admissible (apSmoothCovariant admissible field) = apSmoothRotation admissible 1 field :=
  apSmoothJet_ext admissible (apSmoothTangent admissible (apSmoothCovariant admissible field))
    (apSmoothRotation admissible 1 field) (fun cell =>
      (apSmoothFixedJet_jet admissible tangentRowJet (apSmoothCovariant admissible field) cell).trans
        ((congrArg (apProductJet tangentRowJet) (apSmoothCovariant_jet admissible field cell)).trans
          ((tangentRowJet_covariant (Grad.GaugeCoefficients.Physical.Frame.seedScaledFrequency L ell cell)
            (apSmoothJet admissible 1 cell field)).trans (apSmoothRotation_jet admissible field cell).symm)))

section Transfer
variable {L sigma gamma ell : ℝ} {admissible : Admissible L sigma gamma ell}
  {gauge : CoefficientFamily L sigma gamma ell 3 3}
  (smooth : SmoothCompensatedCoreIsomorphism admissible gauge)

theorem transfer_theta (data : circularCompensatedCore admissible) :
    (smooth.equivalence data).val.1 = data.val.1 := by
  have identity := congrArg (Prod.fst : CompensatedData L sigma gamma ell → APSmooth L sigma gamma ell 1) (smooth.forward data)
  exact identity

theorem transfer_circle_reconstruction (data : circularCompensatedCore admissible) :
    apSmoothCircle L sigma gamma ell (compensatedReconstruct admissible (smooth.equivalence data).val) =
      compensatedReconstruct admissible data.val := by
  exact (smooth.backwardReconstruction (smooth.equivalence data)).symm.trans
    (congrArg (fun core : circularCompensatedCore admissible => compensatedReconstruct admissible core.val)
      (smooth.equivalence.symm_apply_apply data))

theorem transfer_projected_tangent (data : circularCompensatedCore admissible) :
    apSmoothProjectedTangent admissible (compensatedReconstruct admissible (smooth.equivalence data).val) =
      apSmoothProjectedTangent admissible (compensatedReconstruct admissible data.val) :=
  (apSmoothProjectedTangent_circle admissible
    (compensatedReconstruct admissible (smooth.equivalence data).val)).symm.trans
      (congrArg (apSmoothProjectedTangent admissible) (transfer_circle_reconstruction smooth data))

theorem transfer_physicalPsi (data : circularCompensatedCore admissible) :
    physicalPsi admissible (smooth.equivalence data).val = physicalPsi admissible data.val :=
  congrArg (apSmoothRotation admissible 1) (transfer_theta smooth data)

theorem transfer_physicalScalar (data : circularCompensatedCore admissible) :
    physicalScalar admissible (smooth.equivalence data).val = physicalScalar admissible data.val :=
  congrArg₂ (fun first second : APSmooth L sigma gamma ell 1 => first + second)
    (transfer_physicalPsi smooth data) (transfer_projected_tangent smooth data)

theorem transfer_physicalRadial (data : circularCompensatedCore admissible) :
    physicalRadial admissible (smooth.equivalence data).val = physicalRadial admissible data.val :=
  (apSmoothRadial_circle admissible
    (compensatedReconstruct admissible (smooth.equivalence data).val)).symm.trans
      (congrArg (apSmoothRadial admissible) (transfer_circle_reconstruction smooth data))

/-- AO23 concerns the actual mean-free physical scalar and radial
contraction; no equality of the reconstructed physical vectors is asserted. -/
theorem smoothScalarPreservation (data : circularCompensatedCore admissible) :
    physicalPsi admissible (smooth.equivalence data).val = physicalPsi admissible data.val ∧
    physicalScalar admissible (smooth.equivalence data).val = physicalScalar admissible data.val ∧
    physicalRadial admissible (smooth.equivalence data).val = physicalRadial admissible data.val :=
  ⟨transfer_physicalPsi smooth data, transfer_physicalScalar smooth data, transfer_physicalRadial smooth data⟩

end Transfer
end Grad.GaugeCoefficients.Physical.Compensated

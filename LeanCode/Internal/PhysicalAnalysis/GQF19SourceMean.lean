import GQF18CircularSourceJets

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.NonlinearDivision Grad.NonlinearRange

variable {L sigma gamma ell : ℝ}

theorem apSmoothMeanZero_removeMean (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 1) :
    APSmoothMeanZero admissible (apSmoothRemoveMean L sigma gamma ell 1 field) := by
  intro cell
  have identity := congrArg (angularClosedJet 0) (apSmoothRemoveMean_jet admissible field cell)
  have cancel (jet : ClosedJet 1) : angularClosedJet 0 (jet - angularClosedJet 0 jet) = 0 := by
    change angularClosedJetLinear 1 0 (jet - angularClosedJet 0 jet) = 0
    rw [map_sub]
    change angularClosedJet 0 jet - angularClosedJet 0 (angularClosedJet 0 jet) = 0
    rw [angularClosedJet_projection]
    simp
  exact identity.trans (cancel _)

theorem apSmoothMeanZero_rotation (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 1) : APSmoothMeanZero admissible (apSmoothRotation admissible 1 field) := by
  intro cell
  exact (congrArg (angularClosedJet 0) (apSmoothRotation_jet admissible field cell)).trans
    (angularClosedJet_rotation_zero _)

theorem closedFirstJetZero_rotation {dimension : ℕ} (field : ClosedJet dimension)
    (flat : ClosedFirstJetZero field) : ClosedFirstJetZero (rotationJet field) := by
  refine ⟨rotationJet_origin_zero field, ?_⟩
  intro coordinate
  rw [partialJet_rotation_origin, flat.2 0, flat.2 1, smul_zero, smul_zero, sub_zero]

theorem apSmoothRotation_preserves_firstJet (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (field : APSmooth L sigma gamma ell dimension)
    (flat : APSmoothAxisFirstJetZero admissible field) :
    APSmoothAxisFirstJetZero admissible (apSmoothRotation admissible dimension field) := by
  apply apSmoothAxisFirstJetZero_of_closed admissible
  intro cell
  exact (congrArg ClosedFirstJetZero (apSmoothRotation_jet admissible field cell)).mpr
    (closedFirstJetZero_rotation _ (apSmoothAxisFirstJetZero_closed admissible field flat cell))

theorem scalarRemainder_firstJet (admissible : Admissible L sigma gamma ell)
    (state : compensatedFlatCore admissible) :
    APSmoothAxisFirstJetZero admissible (apSmoothScalar L sigma gamma ell state.val.2) := by
  apply apSmoothAxisFirstJetZero_of_closed admissible
  intro cell
  have axis := compensatedFlatCore_axis admissible state cell
  apply (congrArg ClosedFirstJetZero (apSmoothValueMap_jet admissible toroidalPartMap state.val.2 cell)).mpr
  constructor
  · rw [valueMapJet_value, axis.1, map_zero]
  · intro coordinate
    rw [partialJet_valueMap, valueMapJet_value]
    apply PiLp.ext
    intro component
    fin_cases component
    exact axis.2.2.2 coordinate

theorem radialProjection_idempotent_algebra {V : Type*} [AddCommGroup V] [Module ℂ V]
    (J T : V →ₗ[ℂ] V) (square : ∀ field, J (J field) = -field)
    (projected : ∀ field, T (T field) = T field) (field : V) :
    (field + J (T (J field))) + J (T (J (field + J (T (J field))))) = field + J (T (J field)) := by
  rw [map_add, square, map_add, map_neg, projected, map_add, map_neg]
  abel

theorem apSmoothQrad_idempotent (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 2) :
    apSmoothQrad L sigma gamma ell (apSmoothQrad L sigma gamma ell field) = apSmoothQrad L sigma gamma ell field :=
  radialProjection_idempotent_algebra (apSmoothQuarter L sigma gamma ell)
    (apSmoothTangential L sigma gamma ell) (apSmoothQuarter_square admissible)
      (apSmoothTangential_idempotent admissible) field

end Grad.GaugeCoefficients.Physical.Compensated

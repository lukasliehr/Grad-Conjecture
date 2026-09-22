import GQC47LiteralAxisCompensation

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearDivision
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Frame

theorem compensatedReconstruct_jet {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : CompensatedData L sigma gamma ell) (cell : ℤ) :
    apSmoothJet admissible 3 cell (compensatedReconstruct admissible data) =
      covariantJet (seedScaledFrequency L ell cell) (apSmoothJet admissible 1 cell data.1) +
        apSmoothJet admissible 3 cell data.2 :=
  (map_add (apSmoothJet admissible 3 cell) (apSmoothCovariant admissible data.1) data.2).trans
    (congrArg (fun jet : ClosedJet 3 => jet + apSmoothJet admissible 3 cell data.2)
      (apSmoothCovariant_jet admissible data.1 cell))

/-- The exact actual core conditions imply the literal nonzero planar
Hessian cancellation and scalar first-jet zero on every original cell. -/
theorem compensatedFlatCore_axis {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : compensatedFlatCore admissible) (cell : ℤ) :
    (apSmoothJet admissible 3 cell data.val.2).value closedOrigin = 0 ∧
      (∀ coordinate, (partialJet coordinate (apSmoothJet admissible 3 cell data.val.2)).value closedOrigin 0 =
        -((partialJet coordinate (partialJet 0 (apSmoothJet admissible 1 cell data.val.1))).value closedOrigin 0)) ∧
      (∀ coordinate, (partialJet coordinate (apSmoothJet admissible 3 cell data.val.2)).value closedOrigin 1 =
        -((partialJet coordinate (partialJet 1 (apSmoothJet admissible 1 cell data.val.1))).value closedOrigin 0)) ∧
      ∀ coordinate, (partialJet coordinate (apSmoothJet admissible 3 cell data.val.2)).value closedOrigin 2 = 0 := by
  have original := (mem_compensatedFlatCore admissible data.val).mp data.property
  have thetaFlat := apSmoothAxisFirstJetZero_closed admissible data.val.1 original.1.2 cell
  have reconstructedFlat := apSmoothAxisFirstJetZero_closed admissible
    (compensatedReconstruct admissible data.val) original.2 cell
  have covariantFlat := (congrArg ClosedFirstJetZero (compensatedReconstruct_jet admissible data.val cell)).mp reconstructedFlat
  exact closedCompensated_axis (seedScaledFrequency L ell cell) _ _ thetaFlat covariantFlat

theorem apSmoothAxisFirstJetZero_of_closed {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (field : APSmooth L sigma gamma ell dimension)
    (flat : ∀ cell, ClosedFirstJetZero (apSmoothJet admissible dimension cell field)) :
    APSmoothAxisFirstJetZero admissible field := by
  refine ⟨fun cell => (flat cell).1, ?_⟩
  intro coordinate cell
  exact (congrArg (fun jet : ClosedJet dimension => jet.value closedOrigin)
    (apSmoothPartial_jet admissible field coordinate cell)).trans ((flat cell).2 coordinate)

theorem closedCompensated_axis_converse (frequency : ℂ) (theta : ClosedJet 1) (remainder : ClosedJet 3)
    (thetaFlat : ClosedFirstJetZero theta) (valueZero : remainder.value closedOrigin = 0)
    (first : ∀ coordinate, (partialJet coordinate remainder).value closedOrigin 0 =
      -((partialJet coordinate (partialJet 0 theta)).value closedOrigin 0))
    (second : ∀ coordinate, (partialJet coordinate remainder).value closedOrigin 1 =
      -((partialJet coordinate (partialJet 1 theta)).value closedOrigin 0))
    (scalar : ∀ coordinate, (partialJet coordinate remainder).value closedOrigin 2 = 0) :
    ClosedFirstJetZero (covariantJet frequency theta + remainder) := by
  constructor
  · rw [closedJet_value_add, ContinuousMap.add_apply, covariantJet_axis_value frequency theta thetaFlat,
      valueZero, zero_add]
  · intro coordinate
    change (partialJetLinear 3 coordinate (_ + _)).value closedOrigin = 0
    rw [map_add, partialJetLinear_apply, partialJetLinear_apply, closedJet_value_add, ContinuousMap.add_apply,
      covariantJet_partial_value]
    apply PiLp.ext
    intro component
    fin_cases component
    · change (partialJet coordinate (partialJet 0 theta)).value closedOrigin 0 +
        (partialJet coordinate remainder).value closedOrigin 0 = 0
      rw [first coordinate, add_neg_cancel]
    · change (partialJet coordinate (partialJet 1 theta)).value closedOrigin 0 +
        (partialJet coordinate remainder).value closedOrigin 1 = 0
      rw [second coordinate, add_neg_cancel]
    · change frequency * (partialJet coordinate theta).value closedOrigin 0 +
        (partialJet coordinate remainder).value closedOrigin 2 = 0
      rw [thetaFlat.2 coordinate, scalar coordinate]
      simp

end Grad.GaugeCoefficients.Physical.Compensated

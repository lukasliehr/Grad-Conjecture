import GQC64BoundedCoreTransfer
import GQC51CompensatedAxisConsumer

noncomputable section
set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.NonlinearDivision
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Frame

def LiteralCompensatedAxis (theta : ClosedJet 1) (remainder : ClosedJet 3) : Prop :=
  remainder.value closedOrigin = 0 ∧
    (∀ coordinate, (partialJet coordinate remainder).value closedOrigin 0 =
      -((partialJet coordinate (partialJet 0 theta)).value closedOrigin 0)) ∧
    (∀ coordinate, (partialJet coordinate remainder).value closedOrigin 1 =
      -((partialJet coordinate (partialJet 1 theta)).value closedOrigin 0)) ∧
    ∀ coordinate, (partialJet coordinate remainder).value closedOrigin 2 = 0

/-- The core really has Dv_c=-D²Theta, together with the scalar zero
first jet. This is an equivalence, not merely a consequence of a stricter core. -/
theorem compensatedFlatCore_literal_iff {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : CompensatedData L sigma gamma ell) :
    data ∈ compensatedFlatCore admissible ↔
      (APSmoothMeanZero admissible data.1 ∧ APSmoothAxisFirstJetZero admissible data.1) ∧
        ∀ cell, LiteralCompensatedAxis (apSmoothJet admissible 1 cell data.1) (apSmoothJet admissible 3 cell data.2) := by
  constructor
  · intro member
    exact ⟨((mem_compensatedFlatCore admissible data).mp member).1, fun cell => compensatedFlatCore_axis admissible ⟨data, member⟩ cell⟩
  · rintro ⟨theta, axis⟩
    apply (mem_compensatedFlatCore admissible data).mpr
    refine ⟨theta, apSmoothAxisFirstJetZero_of_closed admissible _ ?_⟩
    intro cell
    have flat := closedCompensated_axis_converse (seedScaledFrequency L ell cell) _ _
      (apSmoothAxisFirstJetZero_closed admissible data.1 theta.2 cell)
      (axis cell).1 (axis cell).2.1 (axis cell).2.2.1 (axis cell).2.2.2
    exact (congrArg ClosedFirstJetZero (compensatedReconstruct_jet admissible data cell)).mpr flat

theorem fixedComplementJet_planar (field : ClosedJet 3) :
    valueMapJet planarPartMap (fixedComplementJet field) = tangentialJet (valueMapJet planarPartMap field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [valueMapJet_value]
  change planarPartMap ((valueMapJet planarInclusionMap (tangentialJet (valueMapJet planarPartMap field)) +
    valueMapJet toroidalInclusionMap (angularClosedJet 0 (valueMapJet toroidalPartMap field))).value point) = _
  rw [closedJet_value_add, ContinuousMap.add_apply, map_add, valueMapJet_value, valueMapJet_value]
  have first := congrArg (fun mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2 =>
    mapping ((tangentialJet (valueMapJet planarPartMap field)).value point)) planarPart_planarInclusion
  have second := congrArg (fun mapping : ComplexEuclidean 1 →L[ℂ] ComplexEuclidean 2 =>
    mapping ((angularClosedJet 0 (valueMapJet toroidalPartMap field)).value point)) planarPart_toroidalInclusion
  exact (congrArg₂ (fun left right : ComplexEuclidean 2 => left + right) first second).trans (add_zero _)

theorem fixedComplementJet_scalar (field : ClosedJet 3) :
    valueMapJet toroidalPartMap (fixedComplementJet field) = angularClosedJet 0 (valueMapJet toroidalPartMap field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [valueMapJet_value]
  change toroidalPartMap ((valueMapJet planarInclusionMap (tangentialJet (valueMapJet planarPartMap field)) +
    valueMapJet toroidalInclusionMap (angularClosedJet 0 (valueMapJet toroidalPartMap field))).value point) = _
  rw [closedJet_value_add, ContinuousMap.add_apply, map_add, valueMapJet_value, valueMapJet_value]
  have first := congrArg (fun mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 1 =>
    mapping ((tangentialJet (valueMapJet planarPartMap field)).value point)) toroidalPart_planarInclusion
  have second := congrArg (fun mapping : ComplexEuclidean 1 →L[ℂ] ComplexEuclidean 1 =>
    mapping ((angularClosedJet 0 (valueMapJet toroidalPartMap field)).value point)) toroidalPart_toroidalInclusion
  exact (congrArg₂ (fun left right : ComplexEuclidean 1 => left + right) first second).trans (zero_add _)

theorem compensatedBackward_planar {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : CompensatedData L sigma gamma ell) (cell : ℤ) :
    valueMapJet planarPartMap (apSmoothJet admissible 3 cell (compensatedBackward L sigma gamma ell data).2) =
      valueMapJet planarPartMap (apSmoothJet admissible 3 cell data.2) -
        tangentialJet (valueMapJet planarPartMap (apSmoothJet admissible 3 cell data.2)) := by
  have same := congrArg (valueMapJet planarPartMap) (apSmoothCircle_jet admissible data.2 cell)
  exact same.trans ((map_sub (valueMapJetLinear 3 2 planarPartMap) _ _).trans
    (congrArg (fun jet : ClosedJet 2 => valueMapJet planarPartMap (apSmoothJet admissible 3 cell data.2) - jet)
      (fixedComplementJet_planar _)))

theorem compensatedBackward_scalar {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : CompensatedData L sigma gamma ell) (cell : ℤ) :
    valueMapJet toroidalPartMap (apSmoothJet admissible 3 cell (compensatedBackward L sigma gamma ell data).2) =
      valueMapJet toroidalPartMap (apSmoothJet admissible 3 cell data.2) -
        angularClosedJet 0 (valueMapJet toroidalPartMap (apSmoothJet admissible 3 cell data.2)) := by
  have same := congrArg (valueMapJet toroidalPartMap) (apSmoothCircle_jet admissible data.2 cell)
  exact same.trans ((map_sub (valueMapJetLinear 3 1 toroidalPartMap) _ _).trans
    (congrArg (fun jet : ClosedJet 1 => valueMapJet toroidalPartMap (apSmoothJet admissible 3 cell data.2) - jet)
      (fixedComplementJet_scalar _)))

end Grad.GaugeCoefficients.Physical.Compensated

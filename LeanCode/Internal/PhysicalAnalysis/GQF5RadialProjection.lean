import GQF4InterfaceConsumer

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger

theorem quarterJet_square (field : ClosedJet 2) :
    valueMapJet quarterValueMap (valueMapJet quarterValueMap field) = -field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simpa only [valueMapJet_value, closedJet_value_neg, ContinuousMap.neg_apply] using
    quarterValueMap_square (field.value point)

theorem quarter_positive_commute :
    quarterValueMap.comp positiveHelicity = positiveHelicity.comp quarterValueMap := by
  apply ContinuousLinearMap.ext
  intro value
  simp [positiveHelicity]

theorem quarter_negative_commute :
    quarterValueMap.comp negativeHelicity = negativeHelicity.comp quarterValueMap := by
  apply ContinuousLinearMap.ext
  intro value
  simp [negativeHelicity]

theorem averageJet_quarter (field : ClosedJet 2) :
    equivariantAverageJet (valueMapJet quarterValueMap field) =
      valueMapJet quarterValueMap (equivariantAverageJet field) := by
  simp only [equivariantAverageJet_eq, angularClosedJet_valueMap, valueMapJet_add,
    valueMapJet_comp, quarter_positive_commute, quarter_negative_commute]

theorem reflectedJet_quarter (field : ClosedJet 2) :
    reflectedVectorJet (valueMapJet quarterValueMap field) =
      -valueMapJet quarterValueMap (reflectedVectorJet field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simp only [reflectedVectorJet_eq, ← valueMapJet_orthogonal, valueMapJet_value,
    closedJet_value_neg, ContinuousMap.neg_apply]
  change reflectionValueMap (quarterValueMap (field.value _)) =
    -quarterValueMap (reflectionValueMap (field.value _))
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [reflectionValueMap, reflectionValueLinear, quarterValueMap, quarterValueLinear]

theorem quarter_tangential_quarter (field : ClosedJet 2) :
    valueMapJet quarterValueMap (tangentialJet (valueMapJet quarterValueMap field)) =
      -(1 / 2 : ℂ) • (equivariantAverageJet field +
        reflectedVectorJet (equivariantAverageJet field)) := by
  rw [tangentialJet_eq, averageJet_quarter, reflectedJet_quarter]
  change (valueMapJetLinear 2 2 quarterValueMap)
    ((1 / 2 : ℂ) • (valueMapJet quarterValueMap (equivariantAverageJet field) -
      -valueMapJet quarterValueMap (reflectedVectorJet (equivariantAverageJet field)))) = _
  rw [map_smul, map_sub, map_neg]
  change (1 / 2 : ℂ) •
    (valueMapJet quarterValueMap (valueMapJet quarterValueMap (equivariantAverageJet field)) -
      -valueMapJet quarterValueMap (valueMapJet quarterValueMap
        (reflectedVectorJet (equivariantAverageJet field)))) = _
  rw [quarterJet_square, quarterJet_square]
  module

theorem planarComplement_planar (field : ClosedJet 2) :
    valueMapJet planarPartMap (fixedComplementJet (valueMapJet planarInclusionMap field)) =
      tangentialJet field := by
  change valueMapJet planarPartMap
    (valueMapJet planarInclusionMap (tangentialJet
      (valueMapJet planarPartMap (valueMapJet planarInclusionMap field))) +
      valueMapJet toroidalInclusionMap (angularClosedJet 0
        (valueMapJet toroidalPartMap (valueMapJet planarInclusionMap field)))) = _
  simp only [valueMapJet_add, valueMapJet_comp, planarPart_planarInclusion,
    planarPart_toroidalInclusion, valueMapJet_zero, add_zero]
  have identity (jet : ClosedJet 2) :
      valueMapJet (ContinuousLinearMap.id ℂ (ComplexEuclidean 2)) jet = jet := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    exact valueMapJet_value _ _ _
  rw [identity, identity]

theorem apSmoothTangential_jet {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (field : APSmooth L sigma gamma ell 2) (cell : ℤ) :
    apSmoothJet admissible 2 cell (apSmoothTangential L sigma gamma ell field) =
      tangentialJet (apSmoothJet admissible 2 cell field) := by
  change apSmoothJet admissible 2 cell (apSmoothValueMap L sigma gamma ell planarPartMap
    (apSmoothComplement L sigma gamma ell
      (apSmoothValueMap L sigma gamma ell planarInclusionMap field))) = _
  rw [apSmoothValueMap_jet, apSmoothComplement_jet, apSmoothValueMap_jet,
    planarComplement_planar]

/-- Literal N radial projection, with the actual equivariant average and reflection. -/
theorem apSmoothQrad_jet {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (field : APSmooth L sigma gamma ell 2) (cell : ℤ) :
    apSmoothJet admissible 2 cell (apSmoothQrad L sigma gamma ell field) =
      apSmoothJet admissible 2 cell field - (1 / 2 : ℂ) •
        (equivariantAverageJet (apSmoothJet admissible 2 cell field) +
          reflectedVectorJet (equivariantAverageJet (apSmoothJet admissible 2 cell field))) := by
  have expand : apSmoothQrad L sigma gamma ell field = field +
      apSmoothQuarter L sigma gamma ell (apSmoothTangential L sigma gamma ell
        (apSmoothQuarter L sigma gamma ell field)) := rfl
  rw [expand, map_add]
  have inner := apSmoothValueMap_jet admissible quarterValueMap field cell
  have middle := apSmoothTangential_jet admissible (apSmoothQuarter L sigma gamma ell field) cell
  have outer := apSmoothValueMap_jet admissible quarterValueMap
    (apSmoothTangential L sigma gamma ell (apSmoothQuarter L sigma gamma ell field)) cell
  change apSmoothJet admissible 2 cell (apSmoothQuarter L sigma gamma ell field) = _ at inner
  change apSmoothJet admissible 2 cell (apSmoothQuarter L sigma gamma ell
    (apSmoothTangential L sigma gamma ell (apSmoothQuarter L sigma gamma ell field))) = _ at outer
  have mapped := outer.trans ((congrArg (valueMapJet quarterValueMap) middle).trans
    ((congrArg (fun jet => valueMapJet quarterValueMap (tangentialJet jet)) inner).trans
      (quarter_tangential_quarter (apSmoothJet admissible 2 cell field))))
  exact (congrArg (fun jet : ClosedJet 2 => apSmoothJet admissible 2 cell field + jet) mapped).trans
    (by module)

end Grad.GaugeCoefficients.Physical.Compensated

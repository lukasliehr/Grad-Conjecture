import GQF12RadialRotation

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Radial
open Grad.NonlinearRange

theorem storedQuarter_tangent_dot (point : ClosedDisk) (value : ComplexEuclidean 3) :
    storedTangentDot point (storedQuarterMap value) =
      (point.val 0 : ℂ) * value 0 + (point.val 1 : ℂ) * value 1 := by
  simp [storedTangentDot, storedQuarterMap, planarInclusionMap, planarPartMap,
    quarterValueMap, quarterValueLinear]
  ring

theorem planarComplement_rotation_quarter (field : ClosedJet 3) :
    valueMapJet planarPartMap (fixedComplementJet (valueMapJet storedQuarterMap (rotationJet field))) =
      -valueMapJet planarPartMap (fixedComplementJet field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have mean := eq_neg_of_add_eq_zero_right (radialRotation_mean field point)
  have converted : closedAngularMean (fun other => storedTangentDot other
      ((valueMapJet storedQuarterMap (rotationJet field)).value other)) point =
      -closedAngularMean (fun other => storedTangentDot other (field.value other)) point := by
    simpa only [valueMapJet_value, storedQuarter_tangent_dot] using mean
  rw [valueMapJet_value, closedJet_value_neg, ContinuousMap.neg_apply, valueMapJet_value,
    fixedComplementJet_value, fixedComplementJet_value,
    cartesianComplementValue_eq_polar _ (valueMapJet storedQuarterMap (rotationJet field)).value.continuous,
    cartesianComplementValue_eq_polar _ field.value.continuous,
    fixedComplementValue_coordinates, fixedComplementValue_coordinates, converted]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [planarPartMap]

theorem planarStoredQuarter_rotation_inclusion (field : ClosedJet 2) :
    valueMapJet planarPartMap (valueMapJet storedQuarterMap
      (rotationJet (valueMapJet planarInclusionMap field))) =
        valueMapJet quarterValueMap (rotationJet field) := by
  rw [rotationJet_valueMap]
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simp only [valueMapJet_value, storedQuarterMap_planar]
  change ((planarPartMap.comp planarInclusionMap)
    (quarterValueMap ((rotationJet field).value point))) = _
  rw [planarPart_planarInclusion, ContinuousLinearMap.id_apply]

/-- The derivative passes through the actual tangential moment with its
literal sign. This is a consequence of mean(R(Y·v))=0, not a spectral deletion. -/
theorem tangentialJet_quarter_rotation (field : ClosedJet 2) :
    tangentialJet (valueMapJet quarterValueMap (rotationJet field)) = -tangentialJet field := by
  have identity := planarComplement_rotation_quarter (valueMapJet planarInclusionMap field)
  rw [planarComplement_jet, planarStoredQuarter_rotation_inclusion,
    planarComplement_planar] at identity
  exact identity

theorem planarCovariantJet (frequency : ℂ) (field : ClosedJet 1) :
    valueMapJet planarPartMap (covariantJet frequency field) = gradientJet field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [valueMapJet_value, covariantJet_value, gradientJet_value]
  rfl

theorem tangentialJet_gradient (field : ClosedJet 1) (meanZero : angularClosedJet 0 field = 0) :
    tangentialJet (gradientJet field) = 0 := by
  have zero := congrArg (valueMapJet planarPartMap) (covariantJet_complement_zero 0 field meanZero)
  rw [planarComplement_jet, planarCovariantJet, valueMapJet_map_zero] at zero
  exact zero

end Grad.GaugeCoefficients.Physical.Compensated

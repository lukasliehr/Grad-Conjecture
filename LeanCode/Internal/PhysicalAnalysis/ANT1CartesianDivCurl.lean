import ANM4ScalarRotation
import ANS7ExactAngularInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.CartesianScalarElimination
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.NonlinearRange Grad.NonlinearDivision Grad.ActualMeanInverse Grad.CircularHighWeak

/-- The ordinary planar divergence, expressed through the accepted curl and J. -/
def vectorDivLinear : ClosedJet 2 →ₗ[ℂ] ClosedJet 1 :=
  planarCurlLinear.comp (valueMapJetLinear 2 2 quarterValueMap)

def vectorDivJet (field : ClosedJet 2) : ClosedJet 1 := vectorDivLinear field

theorem vectorDivJet_actual (field : ClosedJet 2) :
    vectorDivJet field = planarDivJet (valueMapJet planarInclusionMap field) := by
  have law := planarCurlJet_quarter_planar (valueMapJet planarInclusionMap field)
  have planar : valueMapJet planarPartMap (valueMapJet planarInclusionMap field) = field := by
    rw [valueMapJet_comp, planarPart_planarInclusion, valueMapJet_id]
  rw [planar] at law
  exact law

theorem vectorDivJet_value (field : ClosedJet 2) (point : ClosedDisk) :
    (vectorDivJet field).value point 0 =
      (partialJet 0 field).value point 0 + (partialJet 1 field).value point 1 := by
  change (planarCurlJet (valueMapJet quarterValueMap field)).value point 0 = _
  rw [planarCurlJet_value, partialJet_valueMap, partialJet_valueMap, valueMapJet_value, valueMapJet_value]
  simp [quarterValueMap, quarterValueLinear]

theorem vectorDivJet_quarter (field : ClosedJet 2) :
    vectorDivJet (valueMapJet quarterValueMap field) = -planarCurlJet field := by
  change planarCurlJet (valueMapJet quarterValueMap (valueMapJet quarterValueMap field)) = _
  rw [quarterJet_square]
  exact map_neg planarCurlLinear field

theorem scalarRotation_sub (first second : ClosedJet 1) :
    rotationJet (first - second) = rotationJet first - rotationJet second :=
  map_sub rotationJetLinear first second

theorem scalarRotation_smul (scalar : ℂ) (field : ClosedJet 1) :
    rotationJet (scalar • field) = scalar • rotationJet field :=
  map_smul rotationJetLinear scalar field

/-- The exact Cartesian curl commutator, including the axis and boundary. -/
theorem rotationJet_curl (field : ClosedJet 2) :
    rotationJet (planarCurlJet field) = planarCurlJet (rotationJet field) - vectorDivJet field := by
  change rotationJet (valueMapJet (matrixUnit (input := 2) (output := 1) 0 1) (partialJet 0 field) -
    valueMapJet (matrixUnit (input := 2) (output := 1) 0 0) (partialJet 1 field)) = _
  rw [scalarRotation_sub, rotationJet_valueMap, rotationJet_valueMap,
    rotation_partial_zero, rotation_partial_one]
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  have coordinateZero : coordinate = 0 := Subsingleton.elim _ _
  subst coordinate
  simp only [sub_eq_add_neg, closedJet_value_add, closedJet_value_neg,
    ContinuousMap.add_apply, ContinuousMap.neg_apply, PiLp.add_apply, PiLp.neg_apply,
    valueMapJet_value, matrixUnit_apply, operatorBasis, PiLp.smul_apply, smul_eq_mul, ite_true, mul_one]
  change ((partialJet 0 (rotationJet field)).value point 1 - (partialJet 1 field).value point 1) -
    ((partialJet 1 (rotationJet field)).value point 0 + (partialJet 0 field).value point 0) =
      (planarCurlJet (rotationJet field)).value point 0 - (vectorDivJet field).value point 0
  rw [planarCurlJet_value, vectorDivJet_value]
  ring

/-- The exact Cartesian divergence commutator. -/
theorem rotationJet_div (field : ClosedJet 2) :
    rotationJet (vectorDivJet field) = vectorDivJet (rotationJet field) + planarCurlJet field := by
  have law := rotationJet_curl (valueMapJet quarterValueMap field)
  rw [rotationJet_valueMap, vectorDivJet_quarter, sub_neg_eq_add] at law
  exact law

theorem vectorDivJet_rotationPlusQuarter (field : ClosedJet 2) :
    vectorDivJet (rotationJet field + valueMapJet quarterValueMap field) =
      rotationJet (vectorDivJet field) - (2 : ℂ) • planarCurlJet field := by
  change vectorDivLinear (rotationJet field + valueMapJet quarterValueMap field) = _
  rw [map_add]
  change vectorDivJet (rotationJet field) + vectorDivJet (valueMapJet quarterValueMap field) = _
  rw [vectorDivJet_quarter, rotationJet_div]
  module

theorem planarCurlJet_rotationPlusQuarter (field : ClosedJet 2) :
    planarCurlJet (rotationJet field + valueMapJet quarterValueMap field) =
      rotationJet (planarCurlJet field) + (2 : ℂ) • vectorDivJet field := by
  change planarCurlLinear (rotationJet field + valueMapJet quarterValueMap field) = _
  rw [map_add]
  change planarCurlJet (rotationJet field) + vectorDivJet field = _
  rw [rotationJet_curl]
  module

end Grad.CartesianScalarElimination

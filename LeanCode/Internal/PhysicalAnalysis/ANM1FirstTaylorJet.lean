import GQF44ActualConsumer
import AXL6LinearTangential

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.ActualMeanInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.ChartAxisLift Grad.NonlinearRange Grad.AxisSplit Grad.NonlinearDivision
open Grad.NonlinearQuotientBounds (coordinateJet constantValueJet constantValueJet_value)

/-- The actual homogeneous first Taylor polynomial has exactly the two
Cartesian first derivatives of the given smooth jet at the axis. -/
theorem firstTaylor_partial (field : ClosedJet 2) (direction : Fin 2) :
    (partialJet direction (linearColumnJet ((partialJet 0 field).value closedOrigin)
      ((partialJet 1 field).value closedOrigin))).value closedOrigin =
        (partialJet direction field).value closedOrigin := by
  change (partialJetLinear 2 direction
    (coordinateJet 0 (constantValueJet ((partialJet 0 field).value closedOrigin)) +
      coordinateJet 1 (constantValueJet ((partialJet 1 field).value closedOrigin)))).value closedOrigin = _
  rw [map_add, partialJetLinear_apply, partialJetLinear_apply, closedJet_value_add, ContinuousMap.add_apply,
    partialJet_coordinate_value, partialJet_coordinate_value]
  fin_cases direction <;> simp [closedOrigin, spatialBasis, constantValueJet_value]

/-- Zero curl at the axis kills the first Taylor jet of the genuine
smooth tangential projection. No extra derivative-zero premise is used. -/
theorem tangentialJet_firstJet_zero (field : ClosedJet 2)
    (curl : (planarCurlJet field).value closedOrigin 0 = 0) :
    ClosedFirstJetZero (tangentialJet field) := by
  refine ⟨tangentialJet_origin_zero field, ?_⟩
  let polynomial := linearColumnJet ((partialJet 0 field).value closedOrigin)
    ((partialJet 1 field).value closedOrigin)
  have symmetric : (partialJet 0 field).value closedOrigin 1 =
      (partialJet 1 field).value closedOrigin 0 := by
    rw [planarCurlJet_value] at curl
    exact sub_eq_zero.mp curl
  have polynomialZero : tangentialJet polynomial = 0 :=
    tangentialJet_linearColumn_zero _ _ symmetric
  have remainderZero (word : CartesianWord 1) :
      closedDerivative (field - polynomial) 1 word ⟨0, by simp [closedUnitDisk]⟩ = 0 := by
    have wordConstant : word = fun _ => word 0 := by funext position; fin_cases position; rfl
    rw [wordConstant]
    change (partialJetLinear 2 (word 0) (field - polynomial)).value closedOrigin = 0
    rw [map_sub, partialJetLinear_apply, partialJetLinear_apply]
    simp only [sub_eq_add_neg, closedJet_value_add, closedJet_value_neg,
      ContinuousMap.add_apply, ContinuousMap.neg_apply]
    rw [firstTaylor_partial]
    exact add_neg_cancel _
  have projectedZero := tangentialJet_preserves_zero_derivatives (field - polynomial) remainderZero
  have projected : tangentialJet (field - polynomial) = tangentialJet field := by
    change tangentialJetLinear (field - polynomial) = _
    rw [map_sub]
    change tangentialJet field - tangentialJet polynomial = _
    rw [polynomialZero, sub_zero]
  intro direction
  have derivative := projectedZero (fun _ => direction)
  rw [projected] at derivative
  exact derivative

end Grad.ActualMeanInverse

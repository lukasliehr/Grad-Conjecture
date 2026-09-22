import ANP5GradientAndCurl

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.RawCircularSectors
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Algebra Grad.NonlinearDivision

theorem average_rawVector (mode : ℤ) (field : ClosedJet 2) :
    equivariantAverageJet (rawVectorJet mode field) =
      if mode = 0 then equivariantAverageJet field else 0 := by
  have law := (rawVectorJet_zero (rawVectorJet mode field)).symm.trans
    (rawVectorJet_projection 0 mode field)
  by_cases zero : mode = 0
  · subst mode
    exact law.trans ((if_pos rfl).trans ((rawVectorJet_zero field).trans (if_pos rfl).symm))
  · exact law.trans ((if_neg (Ne.symm zero)).trans (if_neg zero).symm)

theorem rawVector_tangential_value (mode : ℤ) (field : ClosedJet 2) :
    rawVectorJet mode (tangentialJet field) = if mode = 0 then tangentialJet field else 0 := by
  have fixed := (rawVectorJet_zero (tangentialJet field)).trans (tangentialJet_average_fixed field)
  have law := (congrArg (rawVectorJet mode) fixed).symm.trans
    (rawVectorJet_projection mode 0 (tangentialJet field))
  by_cases zero : mode = 0
  · subst mode
    exact law.trans ((if_pos rfl).trans (fixed.trans (if_pos rfl).symm))
  · exact law.trans ((if_neg zero).trans (if_neg zero).symm)

theorem tangential_rawVector_value (mode : ℤ) (field : ClosedJet 2) :
    tangentialJet (rawVectorJet mode field) = if mode = 0 then tangentialJet field else 0 := by
  rw [tangentialJet_eq, average_rawVector]
  by_cases zero : mode = 0
  · rw [if_pos zero, if_pos zero]
    rfl
  · rw [if_neg zero, if_neg zero]
    change (1 / 2 : ℂ) • (0 - reflectedVectorLinear 0) = 0
    rw [map_zero, sub_self, smul_zero]

theorem rawVectorJet_tangential (mode : ℤ) (field : ClosedJet 2) :
    rawVectorJet mode (tangentialJet field) = tangentialJet (rawVectorJet mode field) :=
  (rawVector_tangential_value mode field).trans (tangential_rawVector_value mode field).symm

theorem rawVectorJet_quarter (mode : ℤ) (field : ClosedJet 2) :
    rawVectorJet mode (valueMapJet quarterValueMap field) = valueMapJet quarterValueMap (rawVectorJet mode field) := by
  simp only [rawVectorJet_eq, angularClosedJet_valueMap, valueMapJet_add,
    valueMapJet_comp, quarter_positive_commute, quarter_negative_commute]

/-- Every angular projector preserves a literal zero axis value. -/
theorem angular_axis_value_zero {dimension : ℕ} (mode : ℤ) (field : ClosedJet dimension)
    (zero : field.value closedOrigin = 0) : (angularClosedJet mode field).value closedOrigin = 0 := by
  have original : ∀ word : CartesianWord 0, closedDerivative field 0 word closedOrigin = 0 := by
    intro word
    rw [Subsingleton.elim word emptyCartesianWord, closedDerivative_zero_order]
    exact zero
  have projected := angularClosedJet_preserves_zero_derivatives mode field original emptyCartesianWord
  simpa only [closedDerivative_zero_order, closedOrigin] using projected

theorem rawVectorJet_axis_value_zero (mode : ℤ) (field : ClosedJet 2)
    (zero : field.value closedOrigin = 0) : (rawVectorJet mode field).value closedOrigin = 0 := by
  rw [rawVectorJet_eq, closedJet_value_add, ContinuousMap.add_apply, valueMapJet_value, valueMapJet_value,
    angular_axis_value_zero (mode + 1) field zero, angular_axis_value_zero (mode - 1) field zero,
    map_zero, map_zero, zero_add]

theorem closedFirstJetZero_add {dimension : ℕ} (first second : ClosedJet dimension)
    (firstZero : ClosedFirstJetZero first) (secondZero : ClosedFirstJetZero second) :
    ClosedFirstJetZero (first + second) := by
  constructor
  · rw [closedJet_value_add, ContinuousMap.add_apply, firstZero.1, secondZero.1, zero_add]
  · intro coordinate
    change (partialJetLinear dimension coordinate (first + second)).value closedOrigin = 0
    rw [map_add, closedJet_value_add, ContinuousMap.add_apply]
    exact (congrArg₂ (fun first second : ComplexEuclidean dimension => first + second)
      (firstZero.2 coordinate) (secondZero.2 coordinate)).trans (zero_add _)

theorem rawVectorJet_firstJet_zero (mode : ℤ) (field : ClosedJet 2) (zero : ClosedFirstJetZero field) :
    ClosedFirstJetZero (rawVectorJet mode field) :=
  closedFirstJetZero_add _ _
    (closedFirstJetZero_valueMap positiveHelicity _ (closedFirstJetZero_angular field zero (mode + 1)))
    (closedFirstJetZero_valueMap negativeHelicity _ (closedFirstJetZero_angular field zero (mode - 1)))

end Grad.RawCircularSectors

import ANB20LiteralScalarBoundaryConsumer
import AUN4ExactUniquenessConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.ActualScalarAxis
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearDivision
open Grad.GaugeCoefficients.Physical.Compensated Grad.ActualCenterVolterra Grad.RawCircularSectors

/-- A signed first derivative at the origin sees precisely its signed angular
projection. A pinned center mode therefore kills that actual derivative. -/
theorem centerDifferential_origin_pinned {dimension : ℕ} (field : ClosedJet dimension)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (pinned : CenterPinned (angularClosedJet sign field)) :
    (centerDifferential sign field).value closedOrigin = 0 := by
  have law := centerDifferential_angular sign signed sign field
  rw [sub_self] at law
  have value : (centerDifferential sign (angularClosedJet sign field)).value closedOrigin = 0 := by
    simp only [centerDifferential, sub_eq_add_neg, closedJet_value_add, closedJet_value_neg,
      closedJet_value_smul, ContinuousMap.add_apply, ContinuousMap.neg_apply, ContinuousMap.smul_apply,
      pinned.2, smul_zero, neg_zero, add_zero]
  exact (angular_zero_origin (centerDifferential sign field)).symm.trans
    ((congrArg (fun jet : ClosedJet dimension => jet.value closedOrigin) law.symm).trans value)

/-- Mean exclusion and the two literal pinned center modes imply the whole
actual zero first Cartesian jet; no radial assumption is used. -/
theorem scalar_firstJet_of_center_pins {dimension : ℕ} (field : ClosedJet dimension)
    (meanZero : angularClosedJet 0 field = 0)
    (pinned : ∀ sign : ℤ, sign = 1 ∨ sign = -1 → CenterPinned (angularClosedJet sign field)) :
    ClosedFirstJetZero field := by
  constructor
  · exact (angular_zero_origin field).symm.trans
      ((congrArg (fun jet : ClosedJet dimension => jet.value closedOrigin) meanZero).trans (by rfl))
  · exact partial_axis_of_signed_zero field
      (centerDifferential_origin_pinned field 1 (Or.inl rfl) (pinned 1 (Or.inl rfl)))
      (centerDifferential_origin_pinned field (-1) (Or.inr rfl) (pinned (-1) (Or.inr rfl)))

theorem center_pins_of_firstJet {dimension : ℕ} (field : ClosedJet dimension) (flat : ClosedFirstJetZero field)
    (mode : ℤ) : CenterPinned (angularClosedJet mode field) := closedFirstJetZero_angular field flat mode

end Grad.ActualScalarAxis

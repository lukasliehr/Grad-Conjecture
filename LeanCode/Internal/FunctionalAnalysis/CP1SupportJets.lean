import GaugeConsumer
import BLConsumer
import AxisJetConsumer

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Cor18

open Grad.ClosedJets Grad.CartesianState Grad.Constraints

/-- A closed jet vanishing on a centered ball has zero closed-disk lift
near the plane origin. -/
theorem closedDiskLift_eventually_zero {dimension : ℕ} (field : ClosedJet dimension)
    (radius : ℝ) (radiusPositive : 0 < radius) (radiusSmall : radius < 1)
    (vanishes : ∀ point : ClosedDisk, ‖point.val‖ ≤ radius → field.value point = 0) :
    closedDiskLift field.value =ᶠ[nhds (0 : SpatialPlane)]
      (fun _ => (0 : ComplexEuclidean dimension)) := by
  have ballNhds : Metric.ball (0 : SpatialPlane) radius ∈ nhds (0 : SpatialPlane) :=
    Metric.ball_mem_nhds 0 radiusPositive
  apply Filter.eventuallyEq_of_mem ballNhds
  intro point pointNear
  have pointNorm : ‖point‖ < radius := by
    simpa [Metric.mem_ball, dist_eq_norm] using pointNear
  have pointMember : point ∈ closedUnitDisk := by
    show ‖point‖ ≤ 1
    exact le_trans pointNorm.le radiusSmall.le
  show closedDiskLift field.value point = 0
  rw [closedDiskLift]
  simp only [pointMember, dif_pos]
  exact vanishes ⟨point, pointMember⟩ pointNorm.le

/-- The origin sits in the open disk. -/
theorem originPoint_open_membership :
    (Grad.AxisSplit.originPoint : ClosedDisk).val ∈ openUnitDisk := by
  show ‖(Grad.AxisSplit.originPoint : ClosedDisk).val‖ < 1
  rw [Grad.AxisSplit.originPoint_val, norm_zero]
  norm_num

/-- Vanishing on a centered ball forces zero value at the axis. -/
theorem vanishing_ball_originValue {dimension : ℕ} (field : ClosedJet dimension)
    (radius : ℝ) (radiusPositive : 0 < radius)
    (vanishes : ∀ point : ClosedDisk, ‖point.val‖ ≤ radius → field.value point = 0) :
    Grad.AxisSplit.originValue field = 0 := by
  apply vanishes
  rw [Grad.AxisSplit.originPoint_val, norm_zero]
  exact radiusPositive.le

/-- Vanishing on a centered ball forces zero closed first derivatives at
the axis, through the actual closed derivative extension. -/
theorem vanishing_ball_closedDerivative_one {dimension : ℕ} (field : ClosedJet dimension)
    (radius : ℝ) (radiusPositive : 0 < radius) (radiusSmall : radius < 1)
    (vanishes : ∀ point : ClosedDisk, ‖point.val‖ ≤ radius → field.value point = 0)
    (word : CartesianWord 1) (point : ClosedDisk)
    (interior : point.val ∈ openUnitDisk) (atOrigin : point.val = 0) :
    closedDerivative field 1 word point = 0 := by
  rw [closedDerivative_spec field 1 word point interior]
  have liftLocal := closedDiskLift_eventually_zero field radius radiusPositive
    radiusSmall vanishes
  rw [atOrigin]
  show cartesianDerivative 1 word (closedDiskLift field.value) 0 = 0
  rw [cartesianDerivative]
  rw [iteratedFDeriv_one_apply]
  rw [Filter.EventuallyEq.fderiv_eq liftLocal]
  simp

/-- The two jet vocabularies at once: vanishing on a centered ball gives
the axis-split origin pair and the constraints first-jet predicate. -/
theorem vanishing_ball_originPartial {dimension : ℕ} (field : ClosedJet dimension)
    (radius : ℝ) (radiusPositive : 0 < radius) (radiusSmall : radius < 1)
    (vanishes : ∀ point : ClosedDisk, ‖point.val‖ ≤ radius → field.value point = 0)
    (direction : Fin 2) :
    Grad.AxisSplit.originPartial direction field = 0 := by
  rw [Grad.AxisSplit.originPartial_eq_closedDerivative]
  exact vanishing_ball_closedDerivative_one field radius radiusPositive radiusSmall
    vanishes (fun _ => direction) Grad.AxisSplit.originPoint
    originPoint_open_membership Grad.AxisSplit.originPoint_val

theorem vanishing_ball_zeroCartesianFirstJets {dimension : ℕ}
    (field : ClosedJet dimension) (radius : ℝ) (radiusPositive : 0 < radius)
    (radiusSmall : radius < 1)
    (vanishes : ∀ point : ClosedDisk, ‖point.val‖ ≤ radius → field.value point = 0) :
    ZeroCartesianFirstJets field := by
  intro order orderSmall word
  interval_cases order
  · have wordEmpty : word = emptyCartesianWord := by
      funext position
      exact absurd position.isLt (by omega)
    rw [wordEmpty, closedDerivative_zero_order]
    apply vanishes
    show ‖(0 : SpatialPlane)‖ ≤ radius
    rw [norm_zero]
    exact radiusPositive.le
  · apply vanishing_ball_closedDerivative_one field radius radiusPositive
      radiusSmall vanishes word
    · show ‖(0 : SpatialPlane)‖ < 1
      rw [norm_zero]
      norm_num
    · rfl

end Grad.Cor18

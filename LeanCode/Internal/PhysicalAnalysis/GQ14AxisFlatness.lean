import GQ13TransferPrerequisite

noncomputable section

set_option maxHeartbeats 1500000

open Filter Asymptotics
open scoped Topology

namespace Grad.GaugeCoefficients.Physical.GaugeTransfer

open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.NonlinearDivision

/-- A quantitative local form of zero value and zero first Cartesian
derivative. Its equivalence with the actual derivative is proved below. -/
def ClosedAxisFlat {Value : Type*} [NormedAddCommGroup Value] (field : ClosedDisk → Value) : Prop :=
  ∀ tolerance : ℝ, 0 < tolerance → ∃ radius : ℝ, 0 < radius ∧
    ∀ point : ClosedDisk, ‖point.val‖ < radius → ‖field point‖ ≤ tolerance * ‖point.val‖

theorem ClosedAxisFlat.origin {Value : Type*} [NormedAddCommGroup Value]
    {field : ClosedDisk → Value} (flat : ClosedAxisFlat field) : field closedOrigin = 0 := by
  obtain ⟨radius, positive, bound⟩ := flat 1 zero_lt_one
  have zero := bound closedOrigin (by simpa [closedOrigin] using positive)
  exact norm_le_zero_iff.mp (by simpa [closedOrigin] using zero)

theorem ClosedAxisFlat.of_bound {Source Target : Type*} [NormedAddCommGroup Source] [NormedAddCommGroup Target]
    {field : ClosedDisk → Source} (flat : ClosedAxisFlat field) (mapping : ClosedDisk → Target)
    (constant : ℝ) (nonnegative : 0 ≤ constant) (bound : ∀ point, ‖mapping point‖ ≤ constant * ‖field point‖) :
    ClosedAxisFlat mapping := by
  intro tolerance positive
  have denominator : 0 < constant + 1 := by positivity
  obtain ⟨radius, radiusPositive, estimate⟩ := flat (tolerance / (constant + 1)) (div_pos positive denominator)
  refine ⟨radius, radiusPositive, fun point inside => ?_⟩
  calc
    ‖mapping point‖ ≤ constant * ‖field point‖ := bound point
    _ ≤ (constant + 1) * ‖field point‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ ≤ (constant + 1) * (tolerance / (constant + 1) * ‖point.val‖) :=
      mul_le_mul_of_nonneg_left (estimate point inside) denominator.le
    _ = tolerance * ‖point.val‖ := by field_simp

theorem ClosedAxisFlat.add {Value : Type*} [NormedAddCommGroup Value]
    {first second : ClosedDisk → Value} (firstFlat : ClosedAxisFlat first) (secondFlat : ClosedAxisFlat second) :
    ClosedAxisFlat (fun point => first point + second point) := by
  intro tolerance positive
  obtain ⟨firstRadius, firstPositive, firstBound⟩ := firstFlat (tolerance / 2) (by positivity)
  obtain ⟨secondRadius, secondPositive, secondBound⟩ := secondFlat (tolerance / 2) (by positivity)
  refine ⟨min firstRadius secondRadius, lt_min firstPositive secondPositive, fun point inside => ?_⟩
  calc
    _ ≤ ‖first point‖ + ‖second point‖ := norm_add_le _ _
    _ ≤ tolerance / 2 * ‖point.val‖ + tolerance / 2 * ‖point.val‖ :=
      add_le_add (firstBound point (lt_of_lt_of_le inside (min_le_left _ _)))
        (secondBound point (lt_of_lt_of_le inside (min_le_right _ _)))
    _ = _ := by ring

theorem ClosedAxisFlat.neg {Value : Type*} [NormedAddCommGroup Value]
    {field : ClosedDisk → Value} (flat : ClosedAxisFlat field) : ClosedAxisFlat (fun point => -field point) :=
  flat.of_bound _ 1 zero_le_one (fun point => by rw [norm_neg, one_mul])

theorem ClosedAxisFlat.sub {Value : Type*} [NormedAddCommGroup Value]
    {first second : ClosedDisk → Value} (firstFlat : ClosedAxisFlat first) (secondFlat : ClosedAxisFlat second) :
    ClosedAxisFlat (fun point => first point - second point) := by
  simpa only [sub_eq_add_neg] using firstFlat.add secondFlat.neg

theorem ClosedAxisFlat.pullback {Value : Type*} [NormedAddCommGroup Value]
    {field : ClosedDisk → Value} (flat : ClosedAxisFlat field) (mapping : ClosedDisk → ClosedDisk)
    (normPreserving : ∀ point, ‖(mapping point).val‖ = ‖point.val‖) :
    ClosedAxisFlat (fun point => field (mapping point)) := by
  intro tolerance positive
  obtain ⟨radius, radiusPositive, bound⟩ := flat tolerance positive
  refine ⟨radius, radiusPositive, fun point inside => ?_⟩
  simpa only [normPreserving] using bound (mapping point) (by simpa only [normPreserving] using inside)

theorem closedAxisFlat_iff_littleO {Value : Type} [NormedAddCommGroup Value] (field : ClosedDisk → Value) :
    ClosedAxisFlat field ↔ (closedFieldExtension field) =o[𝓝 (0 : SpatialPlane)] (fun point => point) := by
  rw [Asymptotics.isLittleO_iff]
  constructor
  · intro flat tolerance positive
    obtain ⟨radius, radiusPositive, bound⟩ := flat tolerance positive
    filter_upwards [Metric.ball_mem_nhds (0 : SpatialPlane) radiusPositive] with point inside
    have near : ‖point‖ < radius := by simpa only [Metric.mem_ball, dist_zero_right] using inside
    unfold closedFieldExtension
    split_ifs with inDisk
    · exact bound ⟨point, inDisk⟩ near
    · simp only [norm_zero]
      positivity
  · intro little tolerance positive
    obtain ⟨radius, radiusPositive, bound⟩ := Metric.mem_nhds_iff.mp (little positive)
    refine ⟨radius, radiusPositive, fun point inside => ?_⟩
    have estimate := bound (by simpa only [Metric.mem_ball, dist_zero_right] using inside)
    change ‖closedFieldExtension field point.val‖ ≤ tolerance * ‖point.val‖ at estimate
    simpa only [closedFieldExtension_value] using estimate

theorem closedAxisFlat_iff_firstJet {Value : Type} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : ClosedDisk → Value) :
    ClosedAxisFlat field ↔ field closedOrigin = 0 ∧
      HasFDerivAt (closedFieldExtension field) (0 : SpatialPlane →L[ℝ] Value) (0 : SpatialPlane) := by
  constructor
  · intro flat
    refine ⟨flat.origin, ?_⟩
    have atOrigin : closedFieldExtension field (0 : SpatialPlane) = 0 := by
      change closedFieldExtension field closedOrigin.val = 0
      rw [closedFieldExtension_value, flat.origin]
    rw [hasFDerivAt_iff_isLittleO]
    simpa only [atOrigin, sub_zero, zero_apply] using (closedAxisFlat_iff_littleO field).mp flat
  · rintro ⟨zero, derivative⟩
    have atOrigin : closedFieldExtension field (0 : SpatialPlane) = 0 := by
      change closedFieldExtension field closedOrigin.val = 0
      rw [closedFieldExtension_value, zero]
    apply (closedAxisFlat_iff_littleO field).mpr
    rw [hasFDerivAt_iff_isLittleO] at derivative
    simpa only [atOrigin, sub_zero, zero_apply] using derivative

end Grad.GaugeCoefficients.Physical.GaugeTransfer

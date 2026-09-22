import ASG26CompactWeakTests

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

def scalarAnchoredPrimitive (lower : ℝ) (function : ℝ → ℝ) (radius : ℝ) : ℝ :=
  ∫ point in lower..radius, function point

theorem scalarAnchoredPrimitive_derivative (lower : ℝ) (function : ℝ → ℝ)
    (continuousFunction : Continuous function) (radius : ℝ) :
    HasDerivAt (scalarAnchoredPrimitive lower function) (function radius) radius :=
  intervalIntegral.integral_hasDerivAt_right (continuousFunction.intervalIntegrable lower radius)
    continuousFunction.stronglyMeasurable.stronglyMeasurableAtFilter continuousFunction.continuousAt

theorem scalarAnchoredPrimitive_smooth (lower : ℝ) (function : ℝ → ℝ)
    (smooth : ContDiff ℝ ∞ function) : ContDiff ℝ ∞ (scalarAnchoredPrimitive lower function) := by
  apply contDiff_infty_iff_deriv.2
  refine ⟨fun radius => (scalarAnchoredPrimitive_derivative lower function smooth.continuous radius).differentiableAt, ?_⟩
  have derivative : deriv (scalarAnchoredPrimitive lower function) = function :=
    funext (fun radius => (scalarAnchoredPrimitive_derivative lower function smooth.continuous radius).deriv)
  rwa [derivative]

/-- A compactly supported test of zero integral has a compactly supported
smooth primitive strictly inside the same open interval, as used in AG2. -/
theorem scalarAnchoredPrimitive_compact (lower : ℝ) (bounded : lower < 1)
    (function : ℝ → ℝ) (smooth : ContDiff ℝ ∞ function) (compact : HasCompactSupport function)
    (supported : tsupport function ⊆ Ioo lower 1) (zeroIntegral : (∫ point in lower..1, function point) = 0) :
    HasCompactSupport (scalarAnchoredPrimitive lower function) ∧
      tsupport (scalarAnchoredPrimitive lower function) ⊆ Ioo lower 1 := by
  let supportSet := tsupport function ∪ {((lower + 1) / 2 : ℝ)}
  have compactSet : IsCompact supportSet := compact.union isCompact_singleton
  have nonempty : supportSet.Nonempty := ⟨(lower + 1) / 2, Or.inr rfl⟩
  have insideSet : supportSet ⊆ Ioo lower 1 := by
    rintro radius (member | member)
    · exact supported member
    · have same : radius = (lower + 1) / 2 := member
      rw [same]
      constructor <;> linarith
  obtain ⟨left, leftIn, leftLeast⟩ := compactSet.exists_isMinOn nonempty continuous_id.continuousOn
  obtain ⟨right, rightIn, rightGreatest⟩ := compactSet.exists_isMaxOn nonempty continuous_id.continuousOn
  have lowerLeft : lower < left := (insideSet leftIn).1
  have rightUpper : right < 1 := (insideSet rightIn).2
  have functionZeroLeft (point : ℝ) (before : point < left) : function point = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro member
    have order : left ≤ point := leftLeast (Or.inl member)
    linarith
  have functionZeroRight (point : ℝ) (after : right < point) : function point = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro member
    have order : point ≤ right := rightGreatest (Or.inl member)
    linarith
  have primitiveZeroLeft (radius : ℝ) (before : radius < left) : scalarAnchoredPrimitive lower function radius = 0 := by
    unfold scalarAnchoredPrimitive
    calc
      _ = ∫ _point in lower..radius, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro point inside
        exact functionZeroLeft point (inside.2.trans_lt (max_lt lowerLeft before))
      _ = 0 := by simp
  have primitiveZeroRight (radius : ℝ) (after : right < radius) : scalarAnchoredPrimitive lower function radius = 0 := by
    have tail : (∫ point in radius..1, function point) = 0 := by
      calc
        _ = ∫ _point in radius..1, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro point inside
          exact functionZeroRight point ((lt_min after rightUpper).trans_le inside.1)
        _ = 0 := by simp
    have split := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (smooth.continuous.intervalIntegrable lower radius) (smooth.continuous.intervalIntegrable radius 1)
    rw [tail, zeroIntegral, add_zero] at split
    exact split
  have supportBound : Function.support (scalarAnchoredPrimitive lower function) ⊆ Icc left right := by
    intro radius member
    constructor
    · by_contra outside
      exact member (primitiveZeroLeft radius (lt_of_not_ge outside))
    · by_contra outside
      exact member (primitiveZeroRight radius (lt_of_not_ge outside))
  refine ⟨HasCompactSupport.of_support_subset_isCompact isCompact_Icc supportBound, ?_⟩
  have closureBound : tsupport (scalarAnchoredPrimitive lower function) ⊆ Icc left right :=
    closure_minimal supportBound isClosed_Icc
  intro radius member
  have inside := closureBound member
  exact ⟨lowerLeft.trans_le inside.1, inside.2.trans_lt rightUpper⟩

end Grad.AnnularSourceGraph

import AKCY4OriginalStateTaylorBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3500
open Set

namespace Grad.NashMoser.OriginalIteration
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.SmoothingFamily Grad.Q24Realization Grad.NashMoser.OriginalLimit Grad.SmoothForward
open Grad.NonlinearQuotientBounds Grad.PhysicalCoordinates

variable (parameters : PhaseParameters) (reference : Seed.Parameters)
    (inside : reference ∈ Seed.parameterDomain)

theorem originalStateNorm_le_size (base grade lower : ℕ) (large : 3 ≤ lower)
    (ordered : lower ≤ base+grade) (state : stateSmoothRange parameters reference inside) :
    ‖stateSmoothEmbedding parameters reference inside lower large state‖ ≤
      stateSize parameters reference inside base grade state := by
  have bound := xLowering_norm_le parameters ordered (stateToGrade parameters (base+grade) state.val)
  rw [xLowering_core] at bound
  exact bound

variable (cellLength : ℝ) (base loss : ℕ) (baseLarge : 4 ≤ base) (lossLarge : 6 ≤ loss)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (patchInside : seedPatch ⊆ Seed.parameterDomain) (curvatureBound lowStateBound : ℝ)

include baseLarge lossLarge compact patchInside

/-- QYP23's actual loss six is dominated by the once-fixed Newton loss.
The base shift and original analytic width stay fixed across all grades. -/
theorem originalResidual_shifted (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (finite : OriginalFiniteParameter) (state : stateSmoothRange parameters reference inside),
      finite.1 ∈ seedPatch → ‖finite.2‖ ≤ curvatureBound →
      ChartAxisCondition (smoothingChartCore parameters state.val) →
      stateSize parameters reference inside base 0 state ≤ lowStateBound →
      sourceSize parameters base grade
        (originalNonlinearSource parameters cellLength reference inside finite state) ≤
      constant * (1+stateSize parameters reference inside base (grade+loss) state) := by
  obtain ⟨constant,nonnegative,estimate⟩ := originalResidual_norm_bound parameters cellLength reference inside
    (base+grade) (by omega) seedPatch compact patchInside curvatureBound lowStateBound
  refine ⟨constant,nonnegative,fun finite state seed curvature axis low => ?_⟩
  have lowActual := (originalStateNorm_le_size parameters reference inside base 0 4 realLowLarge
    (by omega) state).trans low
  have bound := estimate finite state seed curvature axis lowActual
  have high := originalStateNorm_le_size parameters reference inside base (grade+loss) (base+grade+6)
    (realHighLarge (base+grade)) (by omega) state
  exact bound.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl high) nonnegative)

theorem originalForward_shifted (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (finite : OriginalFiniteParameter) (state : stateSmoothRange parameters reference inside)
        (seed : finite.1 ∈ seedPatch) (axis : ChartAxisCondition (smoothingChartCore parameters state.val)),
      ‖finite.2‖ ≤ curvatureBound →
      stateSize parameters reference inside base 0 state ≤ lowStateBound →
      ∀ direction : stateSmoothRange parameters reference inside,
      sourceSize parameters base grade
        (literalPhysicalSmoothForward parameters cellLength reference inside finite.1 (patchInside seed)
          (finite.2,state) axis direction) ≤
      constant * ((1+stateSize parameters reference inside base (grade+loss) state) *
        stateSize parameters reference inside base 0 direction +
        stateSize parameters reference inside base (grade+loss) direction) := by
  obtain ⟨constant,nonnegative,estimate⟩ := originalForward_norm_bound parameters cellLength reference inside
    (base+grade) (by omega) seedPatch compact patchInside curvatureBound lowStateBound
  refine ⟨constant,nonnegative,fun finite state seed axis curvature low direction => ?_⟩
  have bound := estimate finite state seed axis curvature
    ((originalStateNorm_le_size parameters reference inside base 0 4 realLowLarge (by omega) state).trans low) direction
  have highState := originalStateNorm_le_size parameters reference inside base (grade+loss) (base+grade+6)
    (realHighLarge (base+grade)) (by omega) state
  have highDirection := originalStateNorm_le_size parameters reference inside base (grade+loss) (base+grade+6)
    (realHighLarge (base+grade)) (by omega) direction
  have lowDirection := originalStateNorm_le_size parameters reference inside base 0 4 realLowLarge (by omega) direction
  exact bound.trans (mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul (add_le_add le_rfl highState) lowDirection (norm_nonneg _)
      (by positivity)) highDirection) nonnegative)

theorem originalStateTaylor_shifted (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (finite : OriginalFiniteParameter) (state direction : stateSmoothRange parameters reference inside)
        (seed : finite.1 ∈ seedPatch)
        (axis : ChartAxisCondition (smoothingChartCore parameters state.val)) (highStateBound : ℝ),
      ‖finite.2‖ ≤ curvatureBound →
      (∀ t ∈ Icc (0:ℝ) 1,
        ChartAxisCondition (smoothingChartCore parameters (state+t•direction).val) ∧
        stateSize parameters reference inside base 0 (state+t•direction) ≤ lowStateBound ∧
        stateSize parameters reference inside base (grade+loss) (state+t•direction) ≤ highStateBound) →
      sourceSize parameters base grade
        (originalLiteralTaylorRemainder parameters cellLength reference inside (finite.1,finite.2,state)
          (patchInside seed) axis (finite.1,finite.2,state+direction)) ≤
      constant * ((1+highStateBound) * (stateSize parameters reference inside base 0 direction)^2 +
        2*stateSize parameters reference inside base (grade+loss) direction *
          stateSize parameters reference inside base 0 direction) := by
  obtain ⟨constant,nonnegative,estimate⟩ := originalStateTaylor_norm_bound parameters reference inside
    cellLength (base+grade) (by omega) seedPatch compact patchInside curvatureBound lowStateBound
  refine ⟨constant,nonnegative,fun finite state direction seed axis highStateBound curvature segment => ?_⟩
  have bound := estimate finite state direction seed axis highStateBound curvature (fun t ht =>
    ⟨(segment t ht).1,
      (originalStateNorm_le_size parameters reference inside base 0 4 realLowLarge (by omega) _).trans (segment t ht).2.1,
      (originalStateNorm_le_size parameters reference inside base (grade+loss) (base+grade+6)
        (realHighLarge (base+grade)) (by omega) _).trans (segment t ht).2.2⟩)
  have highDirection := originalStateNorm_le_size parameters reference inside base (grade+loss) (base+grade+6)
    (realHighLarge (base+grade)) (by omega) direction
  have lowDirection := originalStateNorm_le_size parameters reference inside base 0 4 realLowLarge (by omega) direction
  have highNonnegative : 0 ≤ highStateBound :=
    (apply_nonneg (stateSize parameters reference inside base (grade+loss)) (state+0•direction)).trans
      (segment 0 (by constructor <;> norm_num)).2.2
  have square : ‖stateSmoothEmbedding parameters reference inside 4 realLowLarge direction‖^2 ≤
      (stateSize parameters reference inside base 0 direction)^2 := by
    nlinarith [norm_nonneg (stateSmoothEmbedding parameters reference inside 4 realLowLarge direction)]
  exact bound.trans (mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left square (by linarith))
    (mul_le_mul (mul_le_mul_of_nonneg_left highDirection (by norm_num)) lowDirection (norm_nonneg _)
      (mul_nonneg (by norm_num) (apply_nonneg _ _)))) nonnegative)

end Grad.NashMoser.OriginalIteration

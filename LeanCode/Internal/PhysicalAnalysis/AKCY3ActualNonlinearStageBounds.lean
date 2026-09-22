import AKCY2OriginalSmoothedNewtonStep

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3500
open Set
open scoped BigOperators ContDiff

namespace Grad.NashMoser.OriginalIteration
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.SmoothingFamily Grad.Q24Realization Grad.NashMoser.OriginalLimit Grad.SmoothForward
open Grad.NonlinearQuotientBounds Grad.PhysicalCoordinates

variable (parameters : PhaseParameters) (cellLength : ℝ) (reference : Seed.Parameters)
    (inside : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 4 ≤ grade)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (patchInside : seedPatch ⊆ Seed.parameterDomain) (curvatureBound lowStateBound : ℝ)

include compact patchInside

/-- Actual zeroth-order QYP23 estimate, uniform on the fixed seed patch and
low-state ball. No finite-iterate high norm is hidden in the constant. -/
theorem originalResidual_norm_bound :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (finite : OriginalFiniteParameter) (state : stateSmoothRange parameters reference inside),
      finite.1 ∈ seedPatch → ‖finite.2‖ ≤ curvatureBound →
      ChartAxisCondition (smoothingChartCore parameters state.val) →
      ‖stateSmoothEmbedding parameters reference inside 4 realLowLarge state‖ ≤ lowStateBound →
      ‖sourceSmoothEmbedding parameters grade (by omega)
        (originalNonlinearSource parameters cellLength reference inside finite state)‖ ≤
      constant * (1+‖stateSmoothEmbedding parameters reference inside (grade+6) (realHighLarge grade) state‖) := by
  obtain ⟨constant, nonnegative, estimate⟩ := physicalMixedDerivativeEstimate parameters cellLength reference inside
    grade large 0 seedPatch compact patchInside curvatureBound lowStateBound
  refine ⟨constant, nonnegative, fun finite state seed curvature axis low => ?_⟩
  let point := realMixedCoreEmbed parameters reference inside (grade+6) (realHighLarge grade)
    (finite.1,finite.2,state)
  have inDomain := (realMixedDomain_core_iff parameters reference inside (grade+6) (realHighLarge grade)
    (finite.1,finite.2,state)).2 ⟨patchInside seed,axis⟩
  have pointLow : ‖stateLowering parameters reference inside realLowLarge (realLowLeHigh grade)
      point.ofLp.2.ofLp.2‖ ≤ lowStateBound := by
    change ‖stateLowering parameters reference inside realLowLarge (realLowLeHigh grade)
      (stateSmoothEmbedding parameters reference inside (grade+6) (realHighLarge grade) state)‖ ≤ _
    rw [stateLowering_core]
    exact low
  have bound := estimate point (fun index => Fin.elim0 index) seed curvature inDomain pointLow
  simp only [iteratedFDeriv_zero_apply, realMixedCompletedOneHigh,
    Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_empty, mul_one, add_zero] at bound
  rw [originalNonlinearSource_completed parameters cellLength reference inside finite state
    (patchInside seed) axis]
  exact bound

/-- Actual first state derivative, on the same fixed patch. Its high-state
factor multiplies only the grade-four direction. -/
theorem originalForward_norm_bound :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (finite : OriginalFiniteParameter) (state : stateSmoothRange parameters reference inside)
        (seed : finite.1 ∈ seedPatch) (axis : ChartAxisCondition (smoothingChartCore parameters state.val)),
      ‖finite.2‖ ≤ curvatureBound →
      ‖stateSmoothEmbedding parameters reference inside 4 realLowLarge state‖ ≤ lowStateBound →
      ∀ direction : stateSmoothRange parameters reference inside,
      ‖sourceSmoothEmbedding parameters grade (by omega)
        (literalPhysicalSmoothForward parameters cellLength reference inside finite.1 (patchInside seed)
          (finite.2,state) axis direction)‖ ≤
      constant * ((1+‖stateSmoothEmbedding parameters reference inside (grade+6) (realHighLarge grade) state‖) *
        ‖stateSmoothEmbedding parameters reference inside 4 realLowLarge direction‖ +
        ‖stateSmoothEmbedding parameters reference inside (grade+6) (realHighLarge grade) direction‖) := by
  obtain ⟨constant, nonnegative, estimate⟩ := physicalMixedDerivativeEstimate parameters cellLength reference inside
    grade large 1 seedPatch compact patchInside curvatureBound lowStateBound
  refine ⟨constant, nonnegative, fun finite state seed axis curvature low direction => ?_⟩
  let point := realMixedCoreEmbed parameters reference inside (grade+6) (realHighLarge grade)
    (finite.1,finite.2,state)
  let vector := stateSmoothEmbedding parameters reference inside (grade+6) (realHighLarge grade) direction
  have inDomain := (realMixedDomain_core_iff parameters reference inside (grade+6) (realHighLarge grade)
    (finite.1,finite.2,state)).2 ⟨patchInside seed,axis⟩
  have pointLow : ‖stateLowering parameters reference inside realLowLarge (realLowLeHigh grade)
      point.ofLp.2.ofLp.2‖ ≤ lowStateBound := by
    change ‖stateLowering parameters reference inside realLowLarge (realLowLeHigh grade)
      (stateSmoothEmbedding parameters reference inside (grade+6) (realHighLarge grade) state)‖ ≤ _
    rw [stateLowering_core]
    exact low
  have bound := estimate point
    (fun _ => physicalStateDirection parameters reference inside (grade+6) (realHighLarge grade) vector)
    seed curvature inDomain pointLow
  rw [iteratedFDeriv_one_apply, physicalStateDirection_oneHigh] at bound
  change ‖(fderiv ℝ (completedRealPhysicalMixedSlice parameters cellLength reference inside grade (by omega))
    point) (physicalStateDirection parameters reference inside (grade+6) (realHighLarge grade) vector)‖ ≤ _ at bound
  have identity : actualPhysicalSmoothForward parameters cellLength reference inside finite.1 grade large
      (finite.2,state) vector =
      (fderiv ℝ (completedRealPhysicalMixedSlice parameters cellLength reference inside grade (by omega))
        point) (physicalStateDirection parameters reference inside (grade+6) (realHighLarge grade) vector) := by
    rw [actualPhysicalSmoothForward_mixed parameters cellLength reference inside finite.1 (patchInside seed)
      grade large (finite.2,state) axis]
    rfl
  rw [← identity] at bound
  change ‖actualPhysicalSmoothForward parameters cellLength reference inside finite.1 grade large
    (finite.2,state) (stateSmoothEmbedding parameters reference inside (grade+6) (realHighLarge grade) direction)‖ ≤ _ at bound
  rw [actualPhysicalSmoothForward_core_value parameters cellLength reference inside finite.1 (patchInside seed)
    grade large (finite.2,state) axis direction] at bound
  dsimp only [vector] at bound
  rw [stateLowering_core] at bound
  exact bound

end Grad.NashMoser.OriginalIteration

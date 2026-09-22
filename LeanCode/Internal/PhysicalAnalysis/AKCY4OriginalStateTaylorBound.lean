import AKCY3ActualNonlinearStageBounds

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

theorem originalStateStep_difference (grade : ℕ) (large : 3 ≤ grade)
    (finite : OriginalFiniteParameter) (state direction : stateSmoothRange parameters reference inside) :
    realMixedCoreEmbed parameters reference inside grade large (finite.1,finite.2,state+direction)-
      realMixedCoreEmbed parameters reference inside grade large (finite.1,finite.2,state) =
    physicalStateDirection parameters reference inside grade large
      (stateSmoothEmbedding parameters reference inside grade large direction) := by
  rw [originalMixedCoreEmbed_difference, physicalStateDirection_core]
  congr 1
  change (finite.1-finite.1,finite.2-finite.2,state+direction-state) = (0,0,direction)
  apply Prod.ext (sub_self _)
  apply Prod.ext (sub_self _)
  abel

theorem originalStateStep_segment (grade : ℕ) (large : 3 ≤ grade)
    (finite : OriginalFiniteParameter) (state direction : stateSmoothRange parameters reference inside)
    (t : ℝ) :
    realMixedCoreEmbed parameters reference inside grade large (finite.1,finite.2,state)+
      t • (realMixedCoreEmbed parameters reference inside grade large (finite.1,finite.2,state+direction)-
        realMixedCoreEmbed parameters reference inside grade large (finite.1,finite.2,state)) =
    realMixedCoreEmbed parameters reference inside grade large (finite.1,finite.2,state+t•direction) := by
  rw [originalStateStep_difference, physicalStateDirection_core]
  change originalMixedCoreEmbedding parameters reference inside grade large (finite.1,finite.2,state)+
    t • originalMixedCoreEmbedding parameters reference inside grade large (0,0,direction) = _
  rw [← map_smul, ← map_add]
  change originalMixedCoreEmbedding parameters reference inside grade large
    (finite.1+t•0,finite.2+t•0,state+t•direction) = _
  simp only [smul_zero,add_zero,originalMixedCoreEmbedding_apply]

/-- The actual second derivative supplies the written Newton Taylor bound
on any SAME-parameter admissible chord. The displayed high bound belongs
to this chord and is not part of the constant. -/
theorem originalStateTaylor_norm_bound (cellLength : ℝ) (grade : ℕ) (large : 4 ≤ grade)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (patchInside : seedPatch ⊆ Seed.parameterDomain) (curvatureBound lowStateBound : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (finite : OriginalFiniteParameter) (state direction : stateSmoothRange parameters reference inside)
        (seed : finite.1 ∈ seedPatch)
        (axis : ChartAxisCondition (smoothingChartCore parameters state.val)) (highStateBound : ℝ),
      ‖finite.2‖ ≤ curvatureBound →
      (∀ t ∈ Icc (0:ℝ) 1,
        ChartAxisCondition (smoothingChartCore parameters (state+t•direction).val) ∧
        ‖stateSmoothEmbedding parameters reference inside 4 realLowLarge (state+t•direction)‖ ≤ lowStateBound ∧
        ‖stateSmoothEmbedding parameters reference inside (grade+6) (realHighLarge grade)
          (state+t•direction)‖ ≤ highStateBound) →
      ‖sourceSmoothEmbedding parameters grade (by omega)
        (originalLiteralTaylorRemainder parameters cellLength reference inside (finite.1,finite.2,state)
          (patchInside seed) axis (finite.1,finite.2,state+direction))‖ ≤
      constant * ((1+highStateBound) *
        ‖stateSmoothEmbedding parameters reference inside 4 realLowLarge direction‖^2 +
        2*‖stateSmoothEmbedding parameters reference inside (grade+6) (realHighLarge grade) direction‖ *
          ‖stateSmoothEmbedding parameters reference inside 4 realLowLarge direction‖) := by
  obtain ⟨constant,nonnegative,estimate⟩ := originalLiteralTaylorRemainder_bound parameters cellLength reference inside
    grade large seedPatch compact patchInside curvatureBound lowStateBound
  refine ⟨constant,nonnegative,fun finite state direction seed axis highStateBound curvature segment => ?_⟩
  have endpoint := (segment 1 (by constructor <;> norm_num)).1
  simp only [one_smul] at endpoint
  have bound := estimate (finite.1,finite.2,state) (finite.1,finite.2,state+direction)
    (patchInside seed) axis (patchInside seed) endpoint highStateBound ?_
  · rw [originalStateStep_difference, physicalStateDirection_lowering,
      physicalStateDirection_norm, physicalStateDirection_norm, stateLowering_core] at bound
    exact bound
  intro t ht
  rw [originalStateStep_segment]
  refine ⟨seed,curvature,?_,?_,(segment t ht).2.2⟩
  · exact (realMixedDomain_core_iff parameters reference inside (grade+6) (realHighLarge grade)
      (finite.1,finite.2,state+t•direction)).2 ⟨patchInside seed,(segment t ht).1⟩
  · change ‖stateLowering parameters reference inside realLowLarge (realLowLeHigh grade)
      (stateSmoothEmbedding parameters reference inside (grade+6) (realHighLarge grade) (state+t•direction))‖ ≤ _
    rw [stateLowering_core]
    exact (segment t ht).2.1

end Grad.NashMoser.OriginalIteration

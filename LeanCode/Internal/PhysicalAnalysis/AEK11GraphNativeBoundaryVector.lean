import AEK10UniformGraphOuterTuple

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open scoped BigOperators

namespace Grad.AnnularCurrentSource

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.AxisCore Grad.RealFixedRanges
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse

/-- The literal source triple extracted from the direct seven-slot trace.
This definition is available at every split grade, including `(0,0)`. -/
def graphSourceBoundaryVector (parameters : PhaseParameters) (angular cell : ℕ)
    (source : SourceBoundaryTuple) : NegativeTrace parameters angular cell 3 :=
  fullNegativeKernelAction parameters angular cell
    (sourceTupleProjectionKernel parameters)
    (sevenSlotFlatten parameters angular cell
      (sevenSlotTrace parameters angular cell 0 0 source))

/-- Literal coefficient form of the graph source projection: the output is
exactly the last three slots `(F0,RF0,F2)` of the direct seven-slot trace. -/
theorem graphSourceBoundaryVector_coefficient (parameters : PhaseParameters)
    (angular cell : ℕ) (source : SourceBoundaryTuple) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell
      (graphSourceBoundaryVector parameters angular cell source) mode =
      WithLp.toLp 2 ![
        negativeTraceCoefficient parameters angular cell
          (sourceBoundaryToNegative parameters angular cell (source 0)) mode 0,
        negativeTraceCoefficient parameters angular cell
          (sourceBoundaryToNegative parameters angular cell (source 1)) mode 0,
        negativeTraceCoefficient parameters angular cell
          (sourceBoundaryToNegative parameters angular cell (source 2)) mode 0] := by
  unfold graphSourceBoundaryVector sourceTupleProjectionKernel
  rw [constantMatrixKernel_action_coefficient, sourceTupleProjection_apply]
  rfl

/-- The graph-native source contribution `-T⁻¹ H(F0,RF0,F2)` in the
actual high boundary carrier. -/
def graphSourceBoundaryLiftOnHigh {parameters : PhaseParameters} {L compact : ℝ}
    (state : BoundaryInverseState parameters L compact) (angular cell : ℕ)
    (source : SourceBoundaryTuple) : HighBoundaryPrimitive parameters angular cell :=
  actualSourceBoundaryTerm state angular cell
    (graphSourceBoundaryVector parameters angular cell source)

/-- The complete known boundary vector `T⁻¹ datum - T⁻¹ H source`,
with the solved AI11 sign. -/
def actualHighGraphBoundaryVector {parameters : PhaseParameters} {L compact : ℝ}
    (state : BoundaryInverseState parameters L compact) (angular cell : ℕ)
    (datum : HighBoundaryPrimitive parameters angular cell)
    (source : SourceBoundaryTuple) : HighBoundaryPrimitive parameters angular cell :=
  actualBoundaryInverseOnHigh state angular cell datum +
    graphSourceBoundaryLiftOnHigh state angular cell source

/-- The direct graph projection agrees exactly with the legacy ambient-source
projection whenever their outer tuples agree. -/
theorem graphSourceBoundaryVector_eq_original
    (parameters : PhaseParameters) (L : ℝ) (angular cell : ℕ)
    (tuple : SourceBoundaryTuple)
    (source : ZAmbient parameters (angular + cell + 2))
    (same : tuple = sourceOuterTrace parameters L (angular + cell) source) :
    graphSourceBoundaryVector parameters angular cell tuple =
      originalSourceBoundaryVector parameters L angular cell source := by
  unfold graphSourceBoundaryVector originalSourceBoundaryVector actualSevenSlotTrace
  rw [same]

theorem graphSourceBoundaryLiftOnHigh_eq_original
    {parameters : PhaseParameters} {L compact : ℝ}
    (state : BoundaryInverseState parameters L compact) (angular cell : ℕ)
    (tuple : SourceBoundaryTuple)
    (source : ZAmbient parameters (angular + cell + 2))
    (same : tuple = sourceOuterTrace parameters L (angular + cell) source) :
    graphSourceBoundaryLiftOnHigh state angular cell tuple =
      originalSourceBoundaryLiftOnHigh state angular cell source := by
  apply Subtype.ext
  change (actualSourceBoundaryTerm state angular cell
      (graphSourceBoundaryVector parameters angular cell tuple)).val =
    fullNegativeKernelAction parameters angular cell
      (actualSourceBoundaryLiftKernel state)
      (originalSourceBoundaryVector parameters L angular cell source)
  rw [actualSourceBoundaryTerm_kernel]
  congr 1
  exact graphSourceBoundaryVector_eq_original parameters L angular cell tuple source same

theorem actualHighGraphBoundaryVector_eq_known
    {parameters : PhaseParameters} {L compact : ℝ}
    (state : BoundaryInverseState parameters L compact) (angular cell : ℕ)
    (datum : HighBoundaryPrimitive parameters angular cell)
    (tuple : SourceBoundaryTuple)
    (source : ZAmbient parameters (angular + cell + 2))
    (same : tuple = sourceOuterTrace parameters L (angular + cell) source) :
    actualHighGraphBoundaryVector state angular cell datum tuple =
      actualHighKnownBoundaryVector state angular cell datum source := by
  unfold actualHighGraphBoundaryVector actualHighKnownBoundaryVector
  rw [graphSourceBoundaryLiftOnHigh_eq_original state angular cell tuple source same]

/-- The source-only seven-slot trace has no larger norm than its genuine
three-coordinate source tuple. -/
theorem sevenSlotTrace_source_bound (parameters : PhaseParameters)
    (angular cell : ℕ) (source : SourceBoundaryTuple) :
    ‖sevenSlotTrace parameters angular cell 0 0 source‖ ≤ ‖source‖ := by
  have squared := sevenSlotTrace_bound_sq parameters angular cell 0 0 source
  simp only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
    zero_add] at squared
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp squared

theorem graphSourceBoundaryVector_bound (parameters : PhaseParameters)
    (angular cell : ℕ) (source : SourceBoundaryTuple) :
    ‖graphSourceBoundaryVector parameters angular cell source‖ ≤
      fullKernelMoment parameters (angular + cell + 1)
        (sourceTupleProjectionKernel parameters) * ‖source‖ := by
  unfold graphSourceBoundaryVector
  apply (fullNegativeKernelAction_bound parameters angular cell
    (sourceTupleProjectionKernel parameters) _).trans
  rw [sevenSlotFlatten_norm]
  exact mul_le_mul_of_nonneg_left
    (sevenSlotTrace_source_bound parameters angular cell source)
    (fullKernelMoment_nonnegative parameters _ _)

/-- Fixed moment constant for the actual graph-native source lift. -/
def graphSourceLiftMomentConstant (parameters : PhaseParameters) (L compact : ℝ)
    (moment : ℕ) : ℝ :=
  Classical.choose
    (actualSourceBoundaryLift_physicalMoments parameters L compact moment)

theorem graphSourceLiftMomentConstant_nonnegative
    (parameters : PhaseParameters) (L compact : ℝ) (moment : ℕ) :
    0 ≤ graphSourceLiftMomentConstant parameters L compact moment :=
  (Classical.choose_spec
    (actualSourceBoundaryLift_physicalMoments parameters L compact moment)).1

theorem graphSourceLiftMomentConstant_bound
    (parameters : PhaseParameters) (L compact : ℝ) (moment : ℕ)
    (state : BoundaryInverseState parameters L compact) :
    fullKernelMoment parameters moment (actualSourceBoundaryLiftKernel state) ≤
      graphSourceLiftMomentConstant parameters L compact moment *
        state.val.val.size moment :=
  (Classical.choose_spec
    (actualSourceBoundaryLift_physicalMoments parameters L compact moment)).2 state

/-- Uniform source lift estimate in the genuine outer-tuple norm. -/
theorem graphSourceBoundaryLiftOnHigh_bound
    (parameters : PhaseParameters) (L compact : ℝ)
    (state : BoundaryInverseState parameters L compact) (angular cell : ℕ)
    (source : SourceBoundaryTuple) :
    ‖graphSourceBoundaryLiftOnHigh state angular cell source‖ ≤
      graphSourceLiftMomentConstant parameters L compact (angular + cell + 1) *
        state.val.val.size (angular + cell + 1) *
        (fullKernelMoment parameters (angular + cell + 1)
          (sourceTupleProjectionKernel parameters) * ‖source‖) := by
  change ‖(graphSourceBoundaryLiftOnHigh state angular cell source).val‖ ≤ _
  rw [graphSourceBoundaryLiftOnHigh, actualSourceBoundaryTerm_kernel]
  have action := fullNegativeKernelAction_bound parameters angular cell
    (actualSourceBoundaryLiftKernel state)
    (graphSourceBoundaryVector parameters angular cell source)
  have moment := graphSourceLiftMomentConstant_bound parameters L compact
    (angular + cell + 1) state
  have vector := graphSourceBoundaryVector_bound parameters angular cell source
  exact action.trans (mul_le_mul moment vector (norm_nonneg _)
    (mul_nonneg
      (graphSourceLiftMomentConstant_nonnegative parameters L compact _)
      (state.val.val.size_nonnegative _)))

/-- Uniform graph-native source lift estimate in the two genuine radial graph
norms, independent of the inner collar radius. -/
theorem highGraphSourceBoundaryLiftOnHigh_bound
    (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (state : BoundaryInverseState parameters L compact) (angular cell : ℕ)
    (graphs : HighRadialSourceGraphs parameters lower (angular + cell)) :
    ‖graphSourceBoundaryLiftOnHigh state angular cell
      (highGraphOuterTuple parameters lower positive
        (lowerHalf.trans_lt (by norm_num)) (angular + cell) graphs)‖ ≤
      graphSourceLiftMomentConstant parameters L compact (angular + cell + 1) *
        state.val.val.size (angular + cell + 1) *
        fullKernelMoment parameters (angular + cell + 1)
          (sourceTupleProjectionKernel parameters) *
        uniformSourceOuterConstant * (2 * ‖graphs.1‖ + ‖graphs.2‖) := by
  have lift := graphSourceBoundaryLiftOnHigh_bound parameters L compact state angular cell
    (highGraphOuterTuple parameters lower positive
      (lowerHalf.trans_lt (by norm_num)) (angular + cell) graphs)
  have tuple := highGraphOuterTuple_uniform_bound parameters lower positive lowerHalf
    (angular + cell) graphs
  calc
    _ ≤ graphSourceLiftMomentConstant parameters L compact (angular + cell + 1) *
        state.val.val.size (angular + cell + 1) *
        (fullKernelMoment parameters (angular + cell + 1)
          (sourceTupleProjectionKernel parameters) *
          ‖highGraphOuterTuple parameters lower positive
            (lowerHalf.trans_lt (by norm_num)) (angular + cell) graphs‖) := lift
    _ ≤ graphSourceLiftMomentConstant parameters L compact (angular + cell + 1) *
        state.val.val.size (angular + cell + 1) *
        (fullKernelMoment parameters (angular + cell + 1)
          (sourceTupleProjectionKernel parameters) *
          (uniformSourceOuterConstant * (2 * ‖graphs.1‖ + ‖graphs.2‖))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left tuple
          (fullKernelMoment_nonnegative parameters _ _))
        (mul_nonneg
          (graphSourceLiftMomentConstant_nonnegative parameters L compact _)
          (state.val.val.size_nonnegative _))
    _ = _ := by ring

end Grad.AnnularCurrentSource

import GC20RangeExtension

noncomputable section

open MeasureTheory Set

namespace Grad.GaugeCoefficients.Physical.WeightedTrace

variable (Value : Type*) [NormedAddCommGroup Value] [InnerProductSpace ℝ Value]

/-- H¹ on the collar in its literal L²(value) plus L²(radial derivative)
Hilbert graph norm: the closure of genuine C¹ graphs, not arbitrary pairs. -/
def CollarH1 (lower : ℝ) : Submodule ℝ (CollarH1Ambient Value lower) :=
  (LinearMap.range (collarGraphLinear Value lower)).topologicalClosure

instance collarH1_complete [CompleteSpace Value] (lower : ℝ) : CompleteSpace (CollarH1 Value lower) :=
  (LinearMap.range (collarGraphLinear Value lower)).isClosed_topologicalClosure.completeSpace_coe

def collarH1Core (lower : ℝ) : collarSmoothGraph Value →ₗ[ℝ] CollarH1 Value lower :=
  (collarGraphLinear Value lower).codRestrict (CollarH1 Value lower)
    (fun core => Submodule.le_topologicalClosure _ ⟨core, rfl⟩)

theorem collarH1Core_denseRange (lower : ℝ) : DenseRange (collarH1Core Value lower) := by
  let source := LinearMap.range (collarGraphLinear Value lower)
  have inclusionDense : DenseRange (Set.inclusion (Submodule.le_topologicalClosure source)) :=
    (denseRange_inclusion_iff _).2 (fun _ member => member)
  apply inclusionDense.mono
  rintro _ ⟨point, rfl⟩
  rcases point.property with ⟨core, equality⟩
  exact ⟨core, Subtype.ext equality⟩

def collarH1Coordinate (lower : ℝ) (entry : Fin 2) : CollarH1 Value lower →L[ℝ] CollarL2 Value lower :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => CollarL2 Value lower) entry).comp (CollarH1 Value lower).subtypeL

theorem collarH1Coordinate_core_zero (lower : ℝ) (core : collarSmoothGraph Value) :
    collarH1Coordinate Value lower 0 (collarH1Core Value lower core) =
      collarContinuousL2 Value lower core.val.1 := rfl

theorem collarH1Coordinate_core_one (lower : ℝ) (core : collarSmoothGraph Value) :
    collarH1Coordinate Value lower 1 (collarH1Core Value lower core) =
      collarContinuousL2 Value lower core.val.2 := rfl

theorem collarH1_norm_sq (lower : ℝ) (field : CollarH1 Value lower) :
    ‖field‖ ^ 2 = ‖collarH1Coordinate Value lower 0 field‖ ^ 2 + ‖collarH1Coordinate Value lower 1 field‖ ^ 2 := by
  change ‖field.val‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  rfl

variable [CompleteSpace Value]

theorem collarH1Trace_exists (lower : ℝ) (lowerOne : lower < 1) :
    ∃ trace : CollarH1 Value lower →L[ℝ] Value,
      (∀ core, trace (collarH1Core Value lower core) = core.val.1 1) ∧
      (∀ field, ‖trace field‖ ≤ Real.sqrt (collarTraceConstant lower) * ‖field‖) :=
  collarRange_extension (collarGraphLinear Value lower) (collarEndpointLinear Value)
    (Real.sqrt (collarTraceConstant lower)) (Real.sqrt_nonneg _) (collarGraph_endpoint_bound Value lower lowerOne)

def collarH1Trace (lower : ℝ) (lowerOne : lower < 1) : CollarH1 Value lower →L[ℝ] Value :=
  (collarH1Trace_exists Value lower lowerOne).choose

theorem collarH1Trace_core (lower : ℝ) (lowerOne : lower < 1) (core : collarSmoothGraph Value) :
    collarH1Trace Value lower lowerOne (collarH1Core Value lower core) = core.val.1 1 :=
  (collarH1Trace_exists Value lower lowerOne).choose_spec.1 core

/-- CT_GC20 on the full H¹ completion, with the frequency normalized exactly
as in the terminal-window proof. The endpoint is its unique continuous trace. -/
theorem scalar_collar_H1_trace (lower frequency : ℝ) (lowerOne : lower < 1) (oneLe : 1 ≤ frequency)
    (field : CollarH1 Value lower) :
    ‖collarH1Trace Value lower lowerOne field‖ ^ 2 ≤ collarTraceConstant lower *
      (frequency * ‖collarH1Coordinate Value lower 0 field‖ ^ 2 +
        frequency⁻¹ * ‖collarH1Coordinate Value lower 1 field‖ ^ 2) := by
  have closed : IsClosed {point : CollarH1 Value lower |
      ‖collarH1Trace Value lower lowerOne point‖ ^ 2 ≤ collarTraceConstant lower *
        (frequency * ‖collarH1Coordinate Value lower 0 point‖ ^ 2 +
          frequency⁻¹ * ‖collarH1Coordinate Value lower 1 point‖ ^ 2)} := by
    apply isClosed_le
    · exact (collarH1Trace Value lower lowerOne).continuous.norm.pow 2
    · exact continuous_const.mul ((continuous_const.mul ((collarH1Coordinate Value lower 0).continuous.norm.pow 2)).add
        (continuous_const.mul ((collarH1Coordinate Value lower 1).continuous.norm.pow 2)))
  apply isClosed_property (collarH1Core_denseRange Value lower) closed _ field
  intro core
  simp only [collarH1Trace_core, collarH1Coordinate_core_zero, collarH1Coordinate_core_one,
    collarContinuousL2_norm_sq Value lower lowerOne.le]
  exact scalar_collar_trace core.val.1 core.val.2 lower frequency lowerOne oneLe
    core.val.1.continuous core.val.2.continuous (fun point _ => core.property point)

theorem collarH1Trace_unique (lower : ℝ) (lowerOne : lower < 1)
    (trace : CollarH1 Value lower →L[ℝ] Value)
    (coreLaw : ∀ core, trace (collarH1Core Value lower core) = core.val.1 1) :
    trace = collarH1Trace Value lower lowerOne := by
  apply ContinuousLinearMap.ext
  intro field
  apply isClosed_property (collarH1Core_denseRange Value lower)
    (isClosed_eq trace.continuous (collarH1Trace Value lower lowerOne).continuous) _ field
  intro core
  rw [coreLaw, collarH1Trace_core]

omit [CompleteSpace Value] in
/-- The two graph coordinates retain ordinary dr, with no radial or
frequency weight hidden in the H¹ realization. -/
theorem collarL2_norm_sq (lower : ℝ) (field : CollarL2 Value lower) :
    ‖field‖ ^ 2 = ∫ point in Icc lower 1, ‖field point‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem scalar_collar_H1_integral_trace (lower frequency : ℝ) (lowerOne : lower < 1) (oneLe : 1 ≤ frequency)
    (field : CollarH1 Value lower) :
    ‖collarH1Trace Value lower lowerOne field‖ ^ 2 ≤ collarTraceConstant lower *
      (frequency * (∫ point in Icc lower 1, ‖collarH1Coordinate Value lower 0 field point‖ ^ 2) +
        frequency⁻¹ * (∫ point in Icc lower 1, ‖collarH1Coordinate Value lower 1 field point‖ ^ 2)) := by
  simpa only [collarL2_norm_sq] using scalar_collar_H1_trace Value lower frequency lowerOne oneLe field

end Grad.GaugeCoefficients.Physical.WeightedTrace

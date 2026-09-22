import SBT7SourceTraces

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.SourceBoundaryTrace
open Grad.ClosedJets Grad.CartesianState Grad.AxisCore Grad.QuotientProjection
open Grad.FlatSourceProjection Grad.NonlinearProduct Grad.NonlinearQuotientBounds
open Grad.BoundaryTrace Grad.CompatibleCompletion Grad.SourceCollarDivision

/-- The three original Hilbert boundary factors, ordered F0, R F0, F2. -/
abbrev SourceBoundaryTuple := PiLp 2 (fun _ : Fin 3 => SourceBoundary 1)

def sourceOuterTrace (parameters : PhaseParameters) (L : ℝ) (power : ℕ) :
    ZAmbient parameters (power + 2) →L[ℂ] SourceBoundaryTuple :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => SourceBoundary 1)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![forceOuterTrace parameters power,
      rotationOuterTrace parameters power, fourthOuterTrace parameters L power])

theorem sourceOuterTrace_components (parameters : PhaseParameters) (L : ℝ) (power : ℕ)
    (field : ZAmbient parameters (power + 2)) :
    (fun coordinate => sourceOuterTrace parameters L power field coordinate) =
      ![forceOuterTrace parameters power field, rotationOuterTrace parameters power field,
        fourthOuterTrace parameters L power field] := by
  funext coordinate
  fin_cases coordinate <;> rfl

theorem sourceOuterTrace_norm_sq (parameters : PhaseParameters) (L : ℝ) (power : ℕ)
    (field : ZAmbient parameters (power + 2)) :
    ‖sourceOuterTrace parameters L power field‖ ^ 2 =
      ‖forceOuterTrace parameters power field‖ ^ 2 +
      ‖rotationOuterTrace parameters power field‖ ^ 2 +
      ‖fourthOuterTrace parameters L power field‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  rfl

theorem sourceBoundaryTuple_literal_norm (parameters : PhaseParameters) (power : ℕ)
    (field : SourceBoundaryTuple) :
    ‖field‖ ^ 2 = ∑ coordinate : Fin 3, ∑' mode : ℤ × ℤ,
      Real.exp (2 * boundaryPhase parameters mode.2) * annularFrequency mode.1 mode.2 ^ (2 * power) *
        ‖sourceBoundaryCoefficient parameters power (field coordinate) mode‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro coordinate _
  exact sourceBoundary_norm_sq parameters power (field coordinate)

def sourceOuterTraceConstant (L : ℝ) (power : ℕ) : ℝ :=
  Real.sqrt (2 * highForceTraceConstant power ^ 2 + fourthOuterTraceConstant L power ^ 2)

theorem sourceOuterTrace_bound (parameters : PhaseParameters) (L : ℝ) (positive : 0 < L) (power : ℕ)
    (field : ZAmbient parameters (power + 2)) :
    ‖sourceOuterTrace parameters L power field‖ ≤ sourceOuterTraceConstant L power * ‖field‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [sourceOuterTrace_norm_sq, mul_pow,
    Real.sq_sqrt (by positivity : 0 ≤ 2 * highForceTraceConstant power ^ 2 + fourthOuterTraceConstant L power ^ 2)]
  have force := pow_le_pow_left₀ (norm_nonneg _) (forceOuterTrace_bound parameters power field) 2
  have rotation := pow_le_pow_left₀ (norm_nonneg _) (rotationOuterTrace_bound parameters power field) 2
  have fourth := pow_le_pow_left₀ (norm_nonneg _) (fourthOuterTrace_bound parameters L positive power field) 2
  nlinarith

theorem sourceOuterTrace_core (parameters : PhaseParameters) (L : ℝ) (power : ℕ)
    (field : SmoothQuotient parameters) (mode : ℤ × ℤ) :
    (fun coordinate => sourceBoundaryCoefficient parameters power
      (sourceOuterTrace parameters L power (quotientEta parameters (power + 2) field) coordinate) mode) =
      ![originalBoundaryCoefficient parameters (tangentialBoundaryCore parameters (cartesianSourceVector field)) mode,
        originalBoundaryCoefficient parameters (rotationCore parameters
          (tangentialBoundaryCore parameters (cartesianSourceVector field))) mode,
        (L : ℂ)⁻¹ • originalBoundaryCoefficient parameters (field 3) mode] := by
  funext coordinate
  have components := congrFun (sourceOuterTrace_components parameters L power
    (quotientEta parameters (power + 2) field)) coordinate
  rw [components]
  fin_cases coordinate
  · exact forceOuterTrace_core parameters power field mode
  · exact rotationOuterTrace_core parameters power field mode
  · exact fourthOuterTrace_core parameters L power field mode

theorem sourceBoundaryCoefficient_ext {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    {first second : SourceBoundary dimension}
    (same : ∀ mode, sourceBoundaryCoefficient parameters power first mode =
      sourceBoundaryCoefficient parameters power second mode) : first = second := by
  apply lp.ext
  funext mode
  rw [← sourceBoundary_weighted parameters power first mode,
    ← sourceBoundary_weighted parameters power second mode, same mode]

theorem sourceOuterTrace_unique (parameters : PhaseParameters) (L : ℝ) (power : ℕ)
    (other : ZAmbient parameters (power + 2) →L[ℂ] SourceBoundaryTuple)
    (coreLaw : ∀ core, other (quotientEta parameters (power + 2) core) =
      sourceOuterTrace parameters L power (quotientEta parameters (power + 2) core)) :
    other = sourceOuterTrace parameters L power := by
  apply ContinuousLinearMap.ext
  exact congrFun ((quotientEta_denseRange parameters (power + 2)).equalizer
    other.continuous (sourceOuterTrace parameters L power).continuous (funext coreLaw))

end Grad.SourceBoundaryTrace

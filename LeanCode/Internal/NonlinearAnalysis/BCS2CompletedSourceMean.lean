import BCS1OriginalBoundaryMean

noncomputable section

open Set MeasureTheory
open scoped Topology Interval BigOperators

namespace Grad.SourceBoundarySupport

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.BoundaryTrace
open Grad.SourceBoundaryTrace Grad.QuotientProjection Grad.RealFixedRanges

/-- Evaluation of the original unweighted source-boundary coefficient. -/
def sourceBoundaryCoefficientCLM {dimension : ℕ} (parameters : PhaseParameters)
    (power : ℕ) (mode : ℤ × ℤ) :
    SourceBoundary dimension →L[ℂ] ComplexEuclidean dimension :=
  ((sourceBoundaryWeight parameters power mode : ℂ)⁻¹) •
    lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode

@[simp] theorem sourceBoundaryCoefficientCLM_apply {dimension : ℕ}
    (parameters : PhaseParameters) (power : ℕ) (mode : ℤ × ℤ)
    (field : SourceBoundary dimension) :
    sourceBoundaryCoefficientCLM parameters power mode field =
      sourceBoundaryCoefficient parameters power field mode := rfl

/-- The literal F2 boundary has vanishing angular mean on the whole original
completed prescribed source space. No flat source restriction is imposed. -/
theorem fourthOuterTrace_prescribed_mean (parameters : PhaseParameters)
    (L : ℝ) (power : ℕ) (large : 3 ≤ power + 2)
    (source : sourceRange parameters (power + 2) large) (cell : ℤ) :
    sourceBoundaryCoefficient parameters power
      (fourthOuterTrace parameters L power source.val) (0, cell) = 0 := by
  let evaluation := ((sourceBoundaryCoefficientCLM (dimension := 1) parameters
    power (0, cell)).comp (fourthOuterTrace parameters L power)).restrictScalars ℝ
  have equalFunctions := (sourceSmoothEmbedding_denseRange parameters (power + 2) large).equalizer
    (evaluation.comp (sourceInclusion parameters (power + 2) large)).continuous
    (continuous_const : Continuous (fun _ : sourceRange parameters (power + 2) large =>
      (0 : ComplexEuclidean 1))) (by
        funext core
        exact fourthOuterTrace_prescribed_core_mean parameters L power core cell)
  exact congrFun equalFunctions source

/-- Immediate consumer in the unchanged three-component outer tuple. -/
theorem sourceOuterTrace_prescribed_fourth_mean (parameters : PhaseParameters)
    (L : ℝ) (power : ℕ) (large : 3 ≤ power + 2)
    (source : sourceRange parameters (power + 2) large) (cell : ℤ) :
    sourceBoundaryCoefficient parameters power
      (sourceOuterTrace parameters L power source.val 2) (0, cell) = 0 :=
  fourthOuterTrace_prescribed_mean parameters L power large source cell

end Grad.SourceBoundarySupport

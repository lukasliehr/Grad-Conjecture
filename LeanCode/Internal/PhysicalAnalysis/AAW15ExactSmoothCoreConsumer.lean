import AAW14ActualDenseSmoothGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades Grad.AnnularConverse
open Grad.GaugeCoefficients.Physical.WeightedTrace

section Consumer
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

/-- AG12's actual finite Fourier smooth inverse at any prescribed grade:
original width, genuine physical curves, finite support, and both original
boundary values. Every premise is a property of the prescribed source. -/
theorem annularSmoothCore_consumer (angular cell inserted : ℕ) (core : AnnularSmoothDataCore)
    (mode : HighAnnularMode) :
    let data := annularGradedSmoothData lower angular cell inserted core
    HasAnnularDataGrade lower angular cell inserted data ∧
    (ContDiffOn ℝ ∞ (annularSolutionXiCurve parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2 mode) (Icc lower 1) ∧
      ContDiffOn ℝ ∞ (annularSolutionQCurve parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2 mode) (Icc lower 1) ∧
      ContDiffOn ℝ ∞ (annularSolutionPCurve parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2 mode) (Icc lower 1)) ∧
    (mode ∉ annularSmoothDataSupport core →
      annularSolutionXiCurve parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2 mode = 0 ∧
      annularSolutionQCurve parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2 mode = 0 ∧
      annularSolutionPCurve parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2 mode = 0) ∧
    (annularSolutionXiCurve parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2 mode lower =
      annularInnerDatum parameters lower mode (data.2 mode) ∧
      annularSolutionPCurve parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2 mode 1 =
      annularOuterDatum parameters mode (data.1.2.2.2 mode)) := by
  dsimp only
  refine ⟨annularGradedSmoothData_hasGrade lower angular cell inserted core,
    annularGradedSmoothData_solution parameters lower length positive bounded lengthPositive widthHalf widthLength angular cell inserted core mode,
    ?_, annularSolutionCurves_boundary parameters lower length positive bounded lengthPositive widthHalf widthLength _ _ mode⟩
  intro outside
  exact annularSolution_curves_zero parameters lower length positive bounded lengthPositive widthHalf widthLength _ _
    (annularGradedSmoothData_cut lower angular cell inserted core) mode outside

/-- The smooth finite inverse is dense in the literal complete natural
boundary weak graph. AAV's independently proved converse identifies this
whole graph; it is not defined as a closure of the chosen approximants. -/
theorem annularDenseSmoothGraph_consumer :
    DenseRange (annularFiniteSmoothGraph parameters lower length positive bounded lengthPositive widthHalf widthLength) :=
  annularFiniteSmoothGraph_denseRange parameters lower length positive bounded lengthPositive widthHalf widthLength

end Consumer
end Grad.AnnularRegularity

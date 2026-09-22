import AAW11FiniteDataSupport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace

section Actual
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem annularSolution_modes_zero (data : AnnularForcing lower × AnnularBoundary)
    (keep : Set HighAnnularMode) (fixed : annularDataCut lower keep data = data)
    (mode : HighAnnularMode) (outside : mode ∉ keep) :
    annularEnergyValue lower length positive
        (annularVariationalInverse parameters lower length positive bounded lengthPositive widthHalf widthLength data) mode = 0 ∧
    (annularSolvedFlux parameters lower length positive bounded lengthPositive widthHalf widthLength data).val.1 mode = 0 := by
  classical
  constructor
  · have diagonal := (annularVariationalInverse_diagonal parameters lower length positive bounded lengthPositive widthHalf widthLength
      (fourierMask keep) 1 (by norm_num) (fourierMask_bound keep) data).trans
        (congrArg (annularVariationalInverse parameters lower length positive bounded lengthPositive widthHalf widthLength) fixed)
    have atMode := congrArg (fun field : annularEnergySpace lower length positive => annularEnergyValue lower length positive field mode) diagonal
    have commute := congrArg (fun field : AnnularBulk lower => field mode)
      (annularEnergyValue_diagonal lower length positive (fourierMask keep) 1 (by norm_num) (fourierMask_bound keep)
        (annularVariationalInverse parameters lower length positive bounded lengthPositive widthHalf widthLength data))
    have equality := commute.symm.trans atMode
    rw [realLpDiagonal_apply] at equality
    simp only [fourierMask, if_neg outside, Complex.ofReal_zero, zero_smul] at equality
    exact equality.symm
  · have diagonal := (annularSolvedFlux_diagonal parameters lower length positive bounded lengthPositive widthHalf widthLength
      (fourierMask keep) 1 (by norm_num) (fourierMask_bound keep) data).trans
        (congrArg (annularSolvedFlux parameters lower length positive bounded lengthPositive widthHalf widthLength) fixed)
    have atMode := congrArg (fun graph : annularFluxWeakGraph lower positive => graph.val.1 mode) diagonal
    change ((fourierMask keep mode : ℝ) : ℂ) •
      (annularSolvedFlux parameters lower length positive bounded lengthPositive widthHalf widthLength data).val.1 mode = _ at atMode
    simp only [fourierMask, if_neg outside, Complex.ofReal_zero, zero_smul] at atMode
    exact atMode.symm

/-- Finite data produce a finite-mode actual solution, including its
canonical physical representatives and their true endpoint values. -/
theorem annularSolution_curves_zero (data : AnnularForcing lower × AnnularBoundary)
    (keep : Set HighAnnularMode) (fixed : annularDataCut lower keep data = data)
    (mode : HighAnnularMode) (outside : mode ∉ keep) :
    annularSolutionXiCurve parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2 mode = 0 ∧
    annularSolutionQCurve parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2 mode = 0 ∧
    annularSolutionPCurve parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2 mode = 0 := by
  let field := annularVariationalInverse parameters lower length positive bounded lengthPositive widthHalf widthLength data
  have modes := annularSolution_modes_zero parameters lower length positive bounded lengthPositive widthHalf widthLength data keep fixed mode outside
  have xiSection : annularPhysicalValueSection parameters lower length positive bounded mode field = 0 := by
    apply radialSectionL2_injective lower positive bounded
    rw [map_zero, annularPhysicalValueSection_bulk, annularPhysicalValue_eq_decode,
      modes.1, map_zero]
  have qSection : annularPhysicalQSection parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2 mode = 0 := by
    apply radialSectionL2_injective lower positive bounded
    rw [map_zero, annularPhysicalQSection_bulk]
    change annularDecodeMode parameters lower positive mode
      ((annularSolvedFlux parameters lower length positive bounded lengthPositive widthHalf widthLength data).val.1 mode) = 0
    rw [modes.2, map_zero]
  have xiZero : annularSolutionXiCurve parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2 mode = 0 := by
    change radialSectionExtension 1 lower bounded.le
      (annularPhysicalValueSection parameters lower length positive bounded mode field) = 0
    rw [xiSection]
    rfl
  have qZero : annularSolutionQCurve parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2 mode = 0 := by
    unfold annularSolutionQCurve
    rw [qSection]
    rfl
  refine ⟨xiZero, qZero, ?_⟩
  rw [annularSolutionPCurve_eq, qZero]
  apply ContinuousMap.ext
  intro radius
  change (-(annularDSymbol mode)⁻¹) • (0 : ComplexEuclidean 1) = 0
  exact smul_zero _

end Actual
end Grad.AnnularRegularity

import AAQ13ExactSolutionConormalTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularFluxTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The stored derivative is forced by the value, by the actual weak graph. -/
theorem annularFluxWeakGraph_value_injective (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    Function.Injective (fun data : annularFluxWeakGraph lower positive => data.val.1) := by
  intro first second same
  change first.val.1 = second.val.1 at same
  apply Subtype.ext
  apply Prod.ext same
  apply lp.ext
  funext mode
  have graphSame : annularFluxRadialGraph lower positive bounded first mode =
      annularFluxRadialGraph lower positive bounded second mode := by
    apply weightedRadial_value_injective 1 lower positive bounded.le
    exact (annularFluxRadialGraph_value lower positive bounded first mode).trans
      ((congrArg (fun value : AnnularBulk lower => value mode) same).trans
        (annularFluxRadialGraph_value lower positive bounded second mode).symm)
  have slopeSame := congrArg (weightedRadialCoordinate 1 lower 1) graphSame
  rw [annularFluxRadialGraph_slope, annularFluxRadialGraph_slope] at slopeSame
  exact (smul_right_injective (RadialL2 1 lower) (annularFrequency_pos mode).ne') slopeSame

section Diagonal
variable (lower : ℝ) (positive : 0 < lower)
    (coefficient : HighAnnularMode → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (coefficientBound : ∀ mode, |coefficient mode| ≤ constant)

def annularFluxAmbientDiagonal : AnnularFluxGraphAmbient lower →L[ℂ] AnnularFluxGraphAmbient lower :=
  (realLpDiagonal coefficient constant nonnegative coefficientBound).prodMap
    (realLpDiagonal coefficient constant nonnegative coefficientBound)

theorem annularFluxAmbientDiagonal_mem (data : annularFluxWeakGraph lower positive) :
    annularFluxAmbientDiagonal lower coefficient constant nonnegative coefficientBound data.val ∈
      annularFluxWeakGraph lower positive := by
  intro mode
  change CollarWeakDerivative lower
    (radialOrdinary 1 lower positive ((coefficient mode : ℂ) • data.val.1 mode))
    ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 : ℝ) •
      radialOrdinary 1 lower positive ((coefficient mode : ℂ) • data.val.2 mode))
  rw [map_smul, map_smul, smul_comm]
  exact collarWeakDerivative_complex_smul lower (coefficient mode : ℂ) _ _ (data.property mode)

def annularFluxGraphDiagonal : annularFluxWeakGraph lower positive →L[ℂ] annularFluxWeakGraph lower positive :=
  ((annularFluxAmbientDiagonal lower coefficient constant nonnegative coefficientBound).comp
    (annularFluxWeakGraph lower positive).subtypeL).codRestrict
      (annularFluxWeakGraph lower positive)
      (annularFluxAmbientDiagonal_mem lower positive coefficient constant nonnegative coefficientBound)

theorem annularFluxSection_diagonal (bounded : lower < 1)
    (data : annularFluxWeakGraph lower positive) (mode : HighAnnularMode) :
    annularFluxSection lower positive bounded
      (annularFluxGraphDiagonal lower positive coefficient constant nonnegative coefficientBound data) mode =
      (coefficient mode : ℂ) • annularFluxSection lower positive bounded data mode := by
  apply radialSectionL2_injective lower positive bounded
  rw [radialSectionL2_complex_smul, annularFluxSection_bulk, annularFluxSection_bulk]
  change radialOrdinary 1 lower positive ((coefficient mode : ℂ) • data.val.1 mode) = _
  exact map_smul (radialOrdinary 1 lower positive) (coefficient mode : ℂ) (data.val.1 mode)

theorem annularFluxTrace_diagonal (bounded : lower < 1) (endpoint : Fin 2)
    (data : annularFluxWeakGraph lower positive) :
    annularFluxTrace lower positive bounded endpoint
      (annularFluxGraphDiagonal lower positive coefficient constant nonnegative coefficientBound data) =
      realLpDiagonal coefficient constant nonnegative coefficientBound (annularFluxTrace lower positive bounded endpoint data) := by
  apply lp.ext
  funext mode
  change annularFluxTrace lower positive bounded endpoint
    (annularFluxGraphDiagonal lower positive coefficient constant nonnegative coefficientBound data) mode =
      (coefficient mode : ℂ) • annularFluxTrace lower positive bounded endpoint data mode
  rw [annularFluxTrace_apply, annularFluxTrace_apply, annularFluxSection_diagonal]
  exact smul_comm (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2))⁻¹ (coefficient mode : ℂ)
    (annularFluxSection lower positive bounded data mode
      ⟨radialEndpointRadius lower endpoint, radialEndpointRadius_mem lower bounded.le endpoint⟩)

end Diagonal
end Grad.AnnularFluxTrace

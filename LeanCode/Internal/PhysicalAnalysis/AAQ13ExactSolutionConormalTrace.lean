import AAQ12NaturalPhysicalFluxTraces

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularFluxTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

section Actual
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem annularSolvedFlux_physicalQSection (data : AnnularForcing lower × AnnularBoundary) (mode : HighAnnularMode) :
    annularFluxPhysicalQSection parameters lower positive bounded
      (annularSolvedFlux parameters lower length positive bounded lengthPositive widthHalf widthLength data) mode =
      annularPhysicalQSection parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2 mode := by
  apply radialSectionL2_injective lower positive bounded
  rw [annularFluxPhysicalQSection_bulk, annularPhysicalQSection_bulk]
  rfl

theorem annularSolvedFlux_physicalPSection (data : AnnularForcing lower × AnnularBoundary) (mode : HighAnnularMode) :
    annularFluxPhysicalPSection parameters lower positive bounded
      (annularSolvedFlux parameters lower length positive bounded lengthPositive widthHalf widthLength data) mode =
      annularPhysicalPSection parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2 mode := by
  unfold annularFluxPhysicalPSection annularPhysicalPSection
  rw [annularSolvedFlux_physicalQSection]

def annularSolutionNaturalPTrace (endpoint : Fin 2) : (AnnularForcing lower × AnnularBoundary) →L[ℂ] AnnularBoundary :=
  (annularFluxNaturalPTrace lower positive bounded endpoint).comp
    (annularSolvedFlux parameters lower length positive bounded lengthPositive widthHalf widthLength)

theorem annularSolutionNaturalPTrace_physical (endpoint : Fin 2)
    (data : AnnularForcing lower × AnnularBoundary) (mode : HighAnnularMode) :
    annularSolutionNaturalPTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data mode =
      annularPhysicalNegativeTraceWeight parameters lower endpoint mode •
        (annularDSymbol mode • annularPhysicalPSection parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2 mode
          ⟨radialEndpointRadius lower endpoint, radialEndpointRadius_mem lower bounded.le endpoint⟩) := by
  change annularFluxNaturalPTrace lower positive bounded endpoint
    (annularSolvedFlux parameters lower length positive bounded lengthPositive widthHalf widthLength data) mode = _
  rw [annularFluxNaturalPTrace_apply, annularSolvedFlux_physicalPSection]

theorem annularSolutionNaturalPTrace_norm (endpoint : Fin 2) (data : AnnularForcing lower × AnnularBoundary) :
    ‖annularSolutionNaturalPTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data‖ =
      ‖annularSolutionFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data‖ :=
  annularFluxNaturalPTrace_norm lower positive bounded endpoint _

theorem annularSolutionNaturalPTrace_physical_bound (endpoint : Fin 2) (data : AnnularForcing lower × AnnularBoundary) :
    ‖annularSolutionNaturalPTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data‖ ≤
      annularFluxPhysicalTraceConstant lower length *
        (‖annularVariationalInverse parameters lower length positive bounded lengthPositive widthHalf widthLength data‖ +
          ‖data.1.1‖ + ‖data.1.2.1‖ + ‖data.1.2.2.1‖) := by
  rw [annularSolutionNaturalPTrace_norm]
  exact annularSolutionFluxTrace_physical_bound parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data

end Actual
end Grad.AnnularFluxTrace

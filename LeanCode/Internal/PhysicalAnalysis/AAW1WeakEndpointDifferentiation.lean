import AAQ8CanonicalFluxSections
import ANR29RadialPrimitiveDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Any actual continuous representative of a weak solution has the proved
closed-interval derivative whenever its actual weak slope is continuous. -/
theorem annularSection_derivative_of_weak (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (value derivative : CollarL2 (ComplexEuclidean 1) lower)
    (weak : CollarWeakDerivative lower value derivative)
    (representative : RadialContinuousSection 1 lower)
    (bulk : radialSectionL2 1 lower positive bounded.le representative = value)
    (continuousDerivative : C(ℝ, ComplexEuclidean 1))
    (same : derivative =ᵐ[volume.restrict (Icc lower 1)] continuousDerivative)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (radialSectionExtension 1 lower bounded.le representative)
      (continuousDerivative radius) (Icc lower 1) radius := by
  let compact := collarWeak_isCompact 1 lower value derivative weak
  let graph := compactWeakRadialGraph lower positive bounded value derivative compact
  have canonical : representative = weightedRadialSection 1 lower positive bounded graph := by
    apply radialSectionL2_injective lower positive bounded
    exact bulk.trans ((weightedRadialSection_bulk 1 lower positive bounded graph).trans
      (compactWeakRadialGraph_value lower positive bounded value derivative compact)).symm
  have primitive (point : Icc lower (1 : ℝ)) :
      representative point = representative ⟨lower, le_rfl, bounded.le⟩ +
        ∫ r in lower..point.val, derivative r := by
    rw [canonical, weightedRadialSection_primitive,
      compactWeakRadialGraph_slope lower positive bounded value derivative compact]
    congr 1
    exact (weightedRadialSection_endpoint 1 lower positive bounded 0 graph).symm
  exact radialSection_hasDerivWithinAt 1 lower bounded.le representative derivative
    continuousDerivative same primitive radius inside

end Grad.AnnularRegularity

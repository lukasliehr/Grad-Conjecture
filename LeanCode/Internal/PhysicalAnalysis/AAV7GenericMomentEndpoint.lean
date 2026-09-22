import AAV6FluxGraphMomentConverse
import AAQ18DataGraphRadialRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularConverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.GaugeCoefficients.Physical.WeightedTrace

section Converse
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

def annularCandidateMomentGraph (field : annularEnergySpace lower length positive)
    (source : AnnularForcing lower) (mode : HighAnnularMode)
    (weak : CollarWeakDerivative lower
      (radialOrdinary 1 lower positive
        (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode))
      (annularNormalizedQSlope parameters lower length positive lengthPositive widthHalf widthLength bounded.le field source mode)) :
    WeightedRadialH1 1 lower :=
  compactWeakRadialGraph lower positive bounded _ _
    (annularFluxGraph_uncorrected_weak parameters lower length positive bounded lengthPositive widthHalf widthLength field source mode weak)

/-- The radius-weighted conormal moment has the same actual outer endpoint
as Q; this is forced by equality of continuous representatives in L2. -/
theorem annularCandidateMomentGraph_outer (field : annularEnergySpace lower length positive)
    (source : AnnularForcing lower) (mode : HighAnnularMode)
    (weak : CollarWeakDerivative lower
      (radialOrdinary 1 lower positive
        (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode))
      (annularNormalizedQSlope parameters lower length positive lengthPositive widthHalf widthLength bounded.le field source mode))
    (qGraph : WeightedRadialH1 1 lower)
    (qValue : collarH1Coordinate (ComplexEuclidean 1) lower 0
      (weightedToOrdinary 1 lower positive bounded.le qGraph) =
      radialOrdinary 1 lower positive
        (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode)) :
    weightedRadialTrace 1 lower positive bounded 1
      (annularCandidateMomentGraph parameters lower length positive bounded lengthPositive widthHalf widthLength field source mode weak) +
      (2 : ℝ) • weightedRadialTrace 1 lower positive bounded 1
        (annularModeRadialH1 lower length positive mode field) =
      weightedRadialTrace 1 lower positive bounded 1 qGraph := by
  let moment := annularCandidateMomentGraph parameters lower length positive bounded lengthPositive widthHalf widthLength field source mode weak +
    (2 : ℝ) • annularModeRadialH1 lower length positive mode field
  have value : collarH1Coordinate (ComplexEuclidean 1) lower 0
      (weightedToOrdinary 1 lower positive bounded.le moment) =
      annularRadialMoment lower positive
        (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode) := by
    dsimp only [moment, annularCandidateMomentGraph]
    rw [map_add, map_smul, map_add, map_smul, compactWeakRadialGraph_value,
      annularRecoveredQ_moment parameters lower length positive lengthPositive widthHalf widthLength bounded.le]
    rfl
  have sections : weightedRadialSection 1 lower positive bounded moment =
      radialSectionScalar lower annularRadiusCurve
        (weightedRadialSection 1 lower positive bounded qGraph) := by
    apply radialSectionL2_injective lower positive bounded
    rw [weightedRadialSection_bulk, value, radialSectionL2_scalar,
      weightedRadialSection_bulk, qValue]
    rfl
  have endpoint := congrArg (fun representative : RadialContinuousSection 1 lower =>
    representative ⟨radialEndpointRadius lower 1, radialEndpointRadius_mem lower bounded.le 1⟩) sections
  rw [weightedRadialSection_endpoint] at endpoint
  change weightedRadialTrace 1 lower positive bounded 1 moment =
    (1 : ℝ) • weightedRadialSection 1 lower positive bounded qGraph
      ⟨radialEndpointRadius lower 1, radialEndpointRadius_mem lower bounded.le 1⟩ at endpoint
  rw [one_smul, weightedRadialSection_endpoint] at endpoint
  simpa only [moment, map_add, map_smul] using endpoint

end Converse
end Grad.AnnularConverse

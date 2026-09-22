import AAR15ActualFluxMomentWeak
import ASG30CompactWeakGraphConverse
import ANR48RadialEndpointIntegration

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Realization in the already accepted genuine smooth radial graph closure. -/
def compactWeakRadialGraph (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (value derivative : CollarL2 (ComplexEuclidean 1) lower)
    (weak : CompactWeakDerivative 1 lower value derivative) : WeightedRadialH1 1 lower :=
  (compactWeakPair_in_weightedCompletion 1 lower positive bounded value derivative weak).choose

theorem compactWeakRadialGraph_value (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (value derivative : CollarL2 (ComplexEuclidean 1) lower)
    (weak : CompactWeakDerivative 1 lower value derivative) :
    collarH1Coordinate (ComplexEuclidean 1) lower 0
      (weightedToOrdinary 1 lower positive bounded.le (compactWeakRadialGraph lower positive bounded value derivative weak)) = value :=
  (compactWeakPair_in_weightedCompletion 1 lower positive bounded value derivative weak).choose_spec.1

theorem compactWeakRadialGraph_slope (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (value derivative : CollarL2 (ComplexEuclidean 1) lower)
    (weak : CompactWeakDerivative 1 lower value derivative) :
    collarH1Coordinate (ComplexEuclidean 1) lower 1
      (weightedToOrdinary 1 lower positive bounded.le (compactWeakRadialGraph lower positive bounded value derivative weak)) = derivative :=
  (compactWeakPair_in_weightedCompletion 1 lower positive bounded value derivative weak).choose_spec.2

section MomentGraph
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

def annularUncorrectedMomentGraph (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (mode : HighAnnularMode) : WeightedRadialH1 1 lower :=
  compactWeakRadialGraph lower positive bounded _ _
    (annularUncorrectedFluxMoment_weak parameters lower length positive lengthPositive widthHalf widthLength bounded source innerValue mode)

def annularQMomentGraph (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (mode : HighAnnularMode) : WeightedRadialH1 1 lower :=
  annularUncorrectedMomentGraph parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode +
    (2 : ℝ) • annularModeRadialH1 lower length positive mode
      (annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue)

theorem annularQMomentGraph_value (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (mode : HighAnnularMode) :
    collarH1Coordinate (ComplexEuclidean 1) lower 0
      (weightedToOrdinary 1 lower positive bounded.le
        (annularQMomentGraph parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode)) =
      annularRadialMoment lower positive
        (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength
          (annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue)
          source.1 mode) := by
  unfold annularQMomentGraph annularUncorrectedMomentGraph
  rw [map_add, map_smul, map_add, map_smul, compactWeakRadialGraph_value,
    annularRecoveredQ_moment parameters lower length positive lengthPositive widthHalf widthLength bounded.le]
  rfl

theorem annularQMomentGraph_slope (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (mode : HighAnnularMode) :
    collarH1Coordinate (ComplexEuclidean 1) lower 1
      (weightedToOrdinary 1 lower positive bounded.le
        (annularQMomentGraph parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode)) =
      annularFluxMomentRHS parameters lower length positive lengthPositive widthHalf widthLength bounded.le
        (annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue)
        source mode := by
  unfold annularQMomentGraph annularUncorrectedMomentGraph
  rw [map_add, map_smul, map_add, map_smul, compactWeakRadialGraph_slope]
  rfl

/-- Free outer tests retain the entire natural boundary term of the actual
variational solution. This is an identity of genuine weak radial moments. -/
theorem annularUncorrectedMoment_boundary_test (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (mode : HighAnnularMode) (profile : ℝ → ℝ) (smooth : ContDiff ℝ ∞ profile)
    (innerZero : profile lower = 0) (vector : ComplexEuclidean 1) :
    let field := annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
    collarPairing lower ⟨deriv profile, (contDiff_infty_iff_deriv.mp smooth).2.continuous⟩ vector
      (annularUncorrectedFluxMoment parameters lower length positive lengthPositive widthHalf widthLength field source mode) +
    collarPairing lower ⟨profile, smooth.continuous⟩ vector
      (annularUncorrectedFluxMomentRHS parameters lower length positive lengthPositive widthHalf widthLength field source mode) +
    inner ℂ ((Real.sqrt 2 : ℂ) • (profile 1 • vector)) (annularEnergyOuter lower length positive field mode) =
      -inner ℂ ((Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) •
        (profile 1 • vector)) (source.2.2.2 mode) := by
  dsimp only
  have law := annularVariationalSolution_scalar_test parameters lower length positive bounded lengthPositive widthHalf widthLength
    source innerValue mode profile smooth innerZero vector
  rw [annularForm_scalar_moment, annularFunctional_scalar_moment] at law
  dsimp only at law
  simp only [annularUncorrectedFluxMomentRHS, annularUncorrectedFluxMoment, map_add, map_sub] at law ⊢
  linear_combination law

end MomentGraph
end Grad.AnnularReconstruction

import AAZJ1OriginalPhaseDomination

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularJointRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace









open Grad.AnnularRadialJets Grad.AnnularRegularity


section JetSections
variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (jet : ℕ → AnnularRawFamily lower)
    (weak : ∀ order, AnnularPhysicalWeakDerivative parameters lower positive (jet order) (jet (order + 1)))

def annularPhysicalJetGraph (order : ℕ) (mode : HighAnnularMode) : WeightedRadialH1 1 lower :=
  compactWeakRadialGraph lower positive bounded
    (annularDecodeMode parameters lower positive mode (jet order mode))
    (annularDecodeMode parameters lower positive mode (jet (order + 1) mode)) (weak order mode)

def annularPhysicalJetSection (order : ℕ) (mode : HighAnnularMode) : RadialContinuousSection 1 lower :=
  weightedRadialSection 1 lower positive bounded (annularPhysicalJetGraph parameters lower positive bounded jet weak order mode)

theorem annularPhysicalJetSection_bulk (order : ℕ) (mode : HighAnnularMode) :
    radialSectionL2 1 lower positive bounded.le (annularPhysicalJetSection parameters lower positive bounded jet weak order mode) =
      annularDecodeMode parameters lower positive mode (jet order mode) :=
  (weightedRadialSection_bulk 1 lower positive bounded
    (annularPhysicalJetGraph parameters lower positive bounded jet weak order mode)).trans
      (compactWeakRadialGraph_value lower positive bounded _ _ (weak order mode))

/-- The same canonical physical sections differentiate to each other at
both original one-sided endpoints, as well as throughout the annulus. -/
theorem annularPhysicalJetSection_derivative (order : ℕ) (mode : HighAnnularMode)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt
      (radialSectionExtension 1 lower bounded.le (annularPhysicalJetSection parameters lower positive bounded jet weak order mode))
      (annularPhysicalJetSection parameters lower positive bounded jet weak (order + 1) mode ⟨radius, inside⟩)
      (Icc lower 1) radius :=
  annularSection_derivative lower positive bounded _ _
    ((compactWeak_iff_collarWeak 1 lower positive bounded _ _).mp (weak order mode)) _ _
    (annularPhysicalJetSection_bulk parameters lower positive bounded jet weak order mode)
    (annularPhysicalJetSection_bulk parameters lower positive bounded jet weak (order + 1) mode) radius inside

/-- Actual per-mode closed-collar smoothness follows from the proved
physical jet chain. No smooth solution representative is a premise. -/
theorem annularPhysicalJetSection_smooth (order : ℕ) (mode : HighAnnularMode) :
    ContDiffOn ℝ ∞
      (radialSectionExtension 1 lower bounded.le (annularPhysicalJetSection parameters lower positive bounded jet weak order mode))
      (Icc lower 1) := by
  have finite (rank order : ℕ) : ContDiffOn ℝ rank
      (radialSectionExtension 1 lower bounded.le (annularPhysicalJetSection parameters lower positive bounded jet weak order mode))
      (Icc lower 1) := by
    induction rank generalizing order with
    | zero => exact contDiffOn_zero.mpr (ContinuousMap.continuous _).continuousOn
    | succ rank previous =>
      apply annular_closedCollar_succ lower bounded rank _
        (radialSectionExtension 1 lower bounded.le (annularPhysicalJetSection parameters lower positive bounded jet weak (order + 1) mode))
      · intro radius inside
        have law := annularPhysicalJetSection_derivative parameters lower positive bounded jet weak order mode radius inside
        rw [annularSectionExtension_eval lower bounded.le _ radius inside]
        exact law
      · exact previous (order + 1)
  exact contDiffOn_infty.mpr (fun rank => finite rank order)

end JetSections
end Grad.AnnularJointRegularity

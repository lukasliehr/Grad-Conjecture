import AKP11FullFamilyNativeCompatibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology
namespace Grad.ActualAnnularExhaustion
open Grad.AnnularStrongOrbit
open Grad.CartesianState Grad.AnnularFullGraph Grad.AnnularForwardDatum Grad.AnnularForwardTraces
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularRestriction
open Grad.AnnularWeakExhaustion Grad.AnnularIncomingIntegrability Grad.AnnularHighGenerators
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  traceCoupledRealNormed traceCoupledRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule weakWeightedRetainedRealInner

/-- Actual full original compatible fields have one common sequence of
vanishing original incoming traces, using the SAME inserted grade one. -/
theorem fullOriginalFamily_common_vanishing_radii
    (parameters : PhaseParameters)
    (upper length : ℝ) (upperPositive : 0 < upper) (upperBounded : upper < 1) (lengthPositive : 0 < length)
    (collars : ℕ → ℝ) (positive : ∀ index, 0 < collars index) (bounded : ∀ index, collars index < 1)
    (decreasing : Antitone collars) (cofinal : Tendsto collars atTop (𝓝 0))
    (original : ∀ index, OriginalFiveBlockAmbient parameters (collars index) length (positive index))
    (compatible : ∀ k l (included : collars k ≤ collars l),
      originalFiveBlockRestriction parameters (collars k) (collars l) length (positive k) (positive l)
        (bounded l) lengthPositive included (original k) = original l) :
    let fields := fun index => originalWeightedRetainedObservation parameters (collars index) length (positive index)
      (bounded index).le lengthPositive (original index)
    ∀ (weighted : ∀ index, CoupledSpace (collars index) length (positive index) lengthPositive)
    (_inserted : ∀ index, CoupledInsertedGrade (collars index) length (positive index) lengthPositive 1 (fields index) (weighted index))
    (retainedBound insertedBound : ℝ)
    (_retained : ∀ index, ‖fields index‖ ≤ retainedBound)
    (_insertedNorm : ∀ index, ‖weighted index‖ ≤ insertedBound)
    (exceptional : Set ℝ) (_null : volume exceptional = 0),
    ∃ (radii : ℕ → ℝ) (inside : ∀ index, radii index ∈ Ioc 0 upper),
      (∀ index, radii index ∉ exceptional) ∧
      (∀ index, radii (index + 1) < radii index / 2) ∧
      StrictAnti radii ∧
      (∀ index, actualFamilyIncomingNorm upper length lengthPositive collars positive bounded fields (radii index) < 1 / ((index : ℝ) + 1)) ∧
      Tendsto radii atTop (𝓝 0) ∧
      Tendsto (actualFamilyIncomingNorm upper length lengthPositive collars positive bounded fields ∘ radii) atTop (𝓝 0) ∧
      (∀ (stage index : ℕ) (included : collars index ≤ radii stage),
        ‖coupledIncomingTrace (radii stage) length ((positive index).trans_le included)
          ((inside stage).2.trans_lt upperBounded)
          lengthPositive
          (coupledEndpointRestriction (collars index) (radii stage) length (positive index) ((positive index).trans_le included)
            ((inside stage).2.trans_lt upperBounded) lengthPositive included (fields index))‖ < 1 / ((stage : ℝ) + 1)) := by
  dsimp only
  intro weighted inserted retainedBound insertedBound retained insertedNorm exceptional null
  exact actualCompatibleFamily_common_vanishing_radii upper length upperPositive upperBounded lengthPositive
    collars positive bounded decreasing cofinal _ weighted
    (fullOriginalFamily_nativeCompatible parameters length lengthPositive collars positive bounded decreasing original compatible)
    inserted retainedBound insertedBound retained insertedNorm exceptional null

end Grad.ActualAnnularExhaustion

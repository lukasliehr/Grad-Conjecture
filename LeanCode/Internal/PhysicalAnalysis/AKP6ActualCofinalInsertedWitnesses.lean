import AKP5ActualOriginalAnnularWeakLimit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
namespace Grad.ActualAnnularExhaustion
open Grad.CartesianState Grad.AnnularFullGraph Grad.AnnularForwardDatum Grad.AnnularStrongOrbit
open Grad.AnnularForwardTraces Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularCoupledInverse Grad.AnnularRestriction Grad.AnnularHighGenerators
open Grad.AnnularExhaustionEstimate Grad.AnnularWeakExhaustion
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  traceCoupledRealNormed traceCoupledRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule

variable (length : ℝ) (lengthPositive : 0 < length)
    (lower : ℕ → ℝ) (positive : ∀ n, 0 < lower n) (lowerHalf : ∀ n, lower n ≤ 1 / 2)
    (weighted : ∀ n, CoupledSpace (lower n) length (positive n) lengthPositive)

/-- Restrict the actual SAME-field inserted witness; no new inverse is taken. -/
def cofinalInsertedSequence (collar stage : ℕ) : CoupledSpace (lower collar) length (positive collar) lengthPositive :=
  if included : lower stage ≤ lower collar then
    coupledEndpointRestriction (lower stage) (lower collar) length (positive stage) (positive collar)
      ((lowerHalf collar).trans_lt (by norm_num)) lengthPositive included (weighted stage)
  else 0

theorem cofinalInsertedSequence_bound (constant : ℝ) (nonnegative : 0 ≤ constant)
    (uniform : ∀ n, ‖weighted n‖ ≤ constant) (collar stage : ℕ) :
    ‖cofinalInsertedSequence length lengthPositive lower positive lowerHalf weighted collar stage‖ ≤ constant := by
  by_cases included : lower stage ≤ lower collar
  · simp only [cofinalInsertedSequence, dif_pos included]
    exact (coupledEndpointRestriction_bound (lower stage) (lower collar) length (positive stage) (positive collar)
      ((lowerHalf collar).trans_lt (by norm_num)) lengthPositive included (weighted stage)).trans (uniform stage)
  · simpa only [cofinalInsertedSequence, dif_neg included,norm_zero] using nonnegative

/-- The actual BF inserted-grade relation holds eventually on each fixed
collar, in every stored energy, flux and low derivative coordinate. -/
theorem cofinalInsertedSequence_actual (parameters : PhaseParameters) (grade : ℕ)
    (field : ∀ n, OriginalFiveBlockAmbient parameters (lower n) length (positive n))
    (same : ∀ n, CoupledInsertedGrade (lower n) length (positive n) lengthPositive grade
      (originalWeightedRetainedObservation parameters (lower n) length (positive n) ((lowerHalf n).trans (by norm_num)) lengthPositive (field n))
      (weighted n))
    (cofinal : ∀ k, ∀ᶠ n in atTop, lower n ≤ lower k) (collar : ℕ) :
    ∀ᶠ n in atTop, CoupledInsertedGrade (lower collar) length (positive collar) lengthPositive grade
      (originalWeightedRetainedObservation parameters (lower collar) length (positive collar) ((lowerHalf collar).trans (by norm_num)) lengthPositive
        (cofinalRestrictionSequence parameters length lengthPositive lower positive lowerHalf field collar n))
      (cofinalInsertedSequence length lengthPositive lower positive lowerHalf weighted collar n) := by
  filter_upwards [cofinal collar] with n included
  rw [cofinalRestrictionSequence_of_included parameters length lengthPositive lower positive lowerHalf field collar n included]
  simp only [cofinalInsertedSequence,dif_pos included]
  change CoupledInsertedGrade (lower collar) length (positive collar) lengthPositive grade
    (originalCoupledEquivalence parameters (lower collar) length (positive collar) ((lowerHalf collar).trans (by norm_num)) lengthPositive
      (originalRetainedRestriction parameters (lower n) (lower collar) length (positive n) (positive collar)
        ((lowerHalf collar).trans_lt (by norm_num)) lengthPositive included (field n).ofLp.1)) _
  rw [originalRetainedRestriction_weighted]
  exact coupledEndpointRestriction_inserted (lower n) (lower collar) length (positive n) (positive collar)
    ((lowerHalf collar).trans_lt (by norm_num)) lengthPositive included grade _ _ (same n)

end Grad.ActualAnnularExhaustion

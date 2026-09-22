import AKP2SameFixedStateExhaustionSolves

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.ActualAnnularExhaustion
open Grad.CartesianState Grad.AnnularFullGraph Grad.AnnularForwardDatum Grad.AnnularStrongOrbit
open Grad.AnnularForwardTraces Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularRestriction
open Grad.AnnularExhaustionEstimate Grad.AnnularWeakExhaustion
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  traceCoupledRealNormed traceCoupledRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule

variable (parameters : PhaseParameters) (length : ℝ) (lengthPositive : 0 < length)
    (lower : ℕ → ℝ) (positive : ∀ n, 0 < lower n) (lowerHalf : ∀ n, lower n ≤ 1 / 2)
    (field : ∀ n, OriginalFiveBlockAmbient parameters (lower n) length (positive n))

/-- A genuine existing solution is restricted as soon as its annulus
contains this fixed collar. The finite unused prefix is filled by zero. -/
def cofinalRestrictionSequence (collar stage : ℕ) :
    OriginalFiveBlockAmbient parameters (lower collar) length (positive collar) :=
  if included : lower stage ≤ lower collar then
    originalFiveBlockRestriction parameters (lower stage) (lower collar) length (positive stage) (positive collar)
      ((lowerHalf collar).trans_lt (by norm_num)) lengthPositive included (field stage)
  else 0

theorem cofinalRestrictionSequence_of_included (collar stage : ℕ) (included : lower stage ≤ lower collar) :
    cofinalRestrictionSequence parameters length lengthPositive lower positive lowerHalf field collar stage =
      originalFiveBlockRestriction parameters (lower stage) (lower collar) length (positive stage) (positive collar)
        ((lowerHalf collar).trans_lt (by norm_num)) lengthPositive included (field stage) := by
  simp only [cofinalRestrictionSequence, dif_pos included]

theorem cofinalRestrictionSequence_compatible
    (cofinal : ∀ k, ∀ᶠ n in atTop, lower n ≤ lower k)
    (first second : ℕ) (included : lower first ≤ lower second) :
    ∀ᶠ n in atTop,
      originalFiveBlockRestriction parameters (lower first) (lower second) length (positive first) (positive second)
        ((lowerHalf second).trans_lt (by norm_num)) lengthPositive included
        (cofinalRestrictionSequence parameters length lengthPositive lower positive lowerHalf field first n) =
      cofinalRestrictionSequence parameters length lengthPositive lower positive lowerHalf field second n := by
  filter_upwards [cofinal first] with n contains
  rw [cofinalRestrictionSequence_of_included parameters length lengthPositive lower positive lowerHalf field first n contains,
    cofinalRestrictionSequence_of_included parameters length lengthPositive lower positive lowerHalf field second n (contains.trans included)]
  exact originalFiveBlockRestriction_comp parameters (lower n) (lower first) (lower second) length
    (positive n) (positive first) (positive second) ((lowerHalf second).trans_lt (by norm_num)) lengthPositive contains included (field n)

/-- Native retained bounds are uniform for the WHOLE local sequence,
including its unused prefix. The restriction is a genuine graph contraction. -/
theorem cofinalRestrictionSequence_retainedBound
    (constant : ℝ) (nonnegative : 0 ≤ constant)
    (estimate : ∀ n, originalWeightedRetainedNorm parameters (lower n) length (positive n)
      ((lowerHalf n).trans (by norm_num)) lengthPositive (field n).ofLp.1 ≤ constant)
    (collar stage : ℕ) :
    originalWeightedRetainedNorm parameters (lower collar) length (positive collar)
      ((lowerHalf collar).trans (by norm_num)) lengthPositive
      (cofinalRestrictionSequence parameters length lengthPositive lower positive lowerHalf field collar stage).ofLp.1 ≤ constant := by
  by_cases included : lower stage ≤ lower collar
  · rw [cofinalRestrictionSequence_of_included parameters length lengthPositive lower positive lowerHalf field collar stage included]
    exact (originalRestriction_weightedRetainedNorm parameters (lower stage) (lower collar) length (positive stage) (positive collar)
      ((lowerHalf collar).trans_lt (by norm_num)) lengthPositive included (field stage)).trans (estimate stage)
  · simp only [cofinalRestrictionSequence, dif_neg included]
    change ‖originalCoupledEquivalence parameters (lower collar) length (positive collar)
      ((lowerHalf collar).trans (by norm_num)) lengthPositive 0‖ ≤ constant
    simpa only [map_zero,norm_zero] using nonnegative

/-- Every original copied source and full residual is fixed on this collar
once the actual source family is restricted there. -/
theorem cofinalRestrictionSequence_sources
    (cofinal : ∀ k, ∀ᶠ n in atTop, lower n ≤ lower k)
    (sources : ∀ k, OriginalFullSourceBlocks parameters (lower k))
    (same : ∀ n k (included : lower n ≤ lower k),
      originalFullSourceRestriction parameters (lower n) (lower k) included (field n).ofLp.2 = sources k)
    (collar : ℕ) :
    ∀ᶠ n in atTop,
      (cofinalRestrictionSequence parameters length lengthPositive lower positive lowerHalf field collar n).ofLp.2 = sources collar := by
  filter_upwards [cofinal collar] with n included
  rw [cofinalRestrictionSequence_of_included parameters length lengthPositive lower positive lowerHalf field collar n included]
  exact same n collar included

end Grad.ActualAnnularExhaustion

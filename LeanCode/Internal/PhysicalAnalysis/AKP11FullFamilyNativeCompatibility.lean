import AKP8SameCofinalAllGradeLimits
import AKO15ActualCompatibleFamilyVanishingTraces

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.ActualAnnularExhaustion
open Grad.AnnularStrongOrbit
open Grad.CartesianState Grad.AnnularFullGraph Grad.AnnularForwardDatum Grad.AnnularForwardTraces
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularRestriction
open Grad.AnnularWeakExhaustion Grad.AnnularIncomingIntegrability Grad.AnnularHighGenerators
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  traceCoupledRealNormed traceCoupledRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule weakWeightedRetainedRealInner

variable (parameters : PhaseParameters) (length : ℝ) (lengthPositive : 0 < length)
    (lower : ℕ → ℝ) (positive : ∀ n, 0 < lower n) (bounded : ∀ n, lower n < 1)
    (decreasing : Antitone lower)
    (field : ∀ n, OriginalFiveBlockAmbient parameters (lower n) length (positive n))
    (compatible : ∀ k l (included : lower k ≤ lower l),
      originalFiveBlockRestriction parameters (lower k) (lower l) length (positive k) (positive l)
        (bounded l) lengthPositive included (field k) = field l)

include compatible

/-- Actual full original compatibility implies compatibility in the native
retained graphs used by the incoming-trace theorem. -/
theorem fullOriginalFamily_nativeCompatible :
    ActualRetainedFamilyCompatible length lengthPositive lower positive bounded decreasing
      (fun n => originalWeightedRetainedObservation parameters (lower n) length (positive n) (bounded n).le lengthPositive (field n)) := by
  intro first second order
  have same := congrArg (fun value : OriginalFiveBlockAmbient parameters (lower first) length (positive first) => value.ofLp.1)
    (compatible second first (decreasing order))
  change originalRetainedRestriction parameters (lower second) (lower first) length (positive second) (positive first)
    (bounded first) lengthPositive (decreasing order) (field second).ofLp.1 = (field first).ofLp.1 at same
  exact (originalRetainedRestriction_weighted parameters (lower second) (lower first) length (positive second) (positive first)
    (bounded first) lengthPositive (decreasing order) (field second).ofLp.1).symm.trans
      (congrArg (originalCoupledEquivalence parameters (lower first) length (positive first) (bounded first).le lengthPositive) same)

/-- Every grade of that same family also restricts as the actual native
retained graph; its equation is never changed by Fourier insertion. -/
theorem fullOriginalFamily_insertedCompatible
    (grade : ℕ) (weighted : ∀ n, CoupledSpace (lower n) length (positive n) lengthPositive)
    (actual : ∀ n, CoupledInsertedGrade (lower n) length (positive n) lengthPositive grade
      (originalWeightedRetainedObservation parameters (lower n) length (positive n) (bounded n).le lengthPositive (field n)) (weighted n)) :
    ActualRetainedFamilyCompatible length lengthPositive lower positive bounded decreasing weighted := by
  intro first second order
  have same := congrArg (fun value : OriginalFiveBlockAmbient parameters (lower first) length (positive first) => value.ofLp.1)
    (compatible second first (decreasing order))
  exact originalInsertedLimits_restriction_compatible parameters (lower second) (lower first) length
    (positive second) (positive first) (bounded first) lengthPositive (decreasing order) grade
    (field second).ofLp.1 (field first).ofLp.1 same (weighted second) (weighted first) (actual second) (actual first)

end Grad.ActualAnnularExhaustion

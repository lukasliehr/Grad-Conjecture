import AKCV8SegmentTaylorEstimate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
open Set
open scoped BigOperators ContDiff
namespace Grad.NashMoser.OriginalLimit
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.QuotientProjection Grad.ConstrainedGrades
open Grad.Q24Realization Grad.PhysicalCoordinates Grad.NonlinearQuotientBounds

/-- Exact two equal directions in the already accepted mixed one-high
estimate. Only one direction carries the high grade. -/
theorem originalMixedSecond_oneHigh
    (parameters : PhaseParameters) (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (grade : ℕ)
    (base direction : RealMixedAmbient parameters reference insideR (grade+6) (realHighLarge grade)) :
    realMixedCompletedOneHigh parameters reference insideR grade 2 base (fun _ => direction) =
      (1+‖base.ofLp.2.ofLp.2‖) *
        ‖realMixedLowering parameters reference insideR realLowLarge (realLowLeHigh grade) direction‖^2 +
      2*‖direction‖*‖realMixedLowering parameters reference insideR realLowLarge (realLowLeHigh grade) direction‖ := by
  have erase0 : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have erase1 : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
  simp only [realMixedCompletedOneHigh,Fin.prod_univ_two,Fin.sum_univ_two,
    erase0,erase1,Finset.prod_singleton]
  ring

/-- Actual Q24 second derivative with its explicit high-low allocation,
uniform on the same compact seed patch and low-state ball. The high-state
coefficient remains visible and is never multiplied by a high direction. -/
theorem originalMixedSecond_bound
    (parameters : PhaseParameters) (cellLength : ℝ) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 4 ≤ grade)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (patchInside : seedPatch ⊆ Seed.parameterDomain) (curvatureBound lowStateBound : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base direction : RealMixedAmbient parameters reference insideR (grade+6) (realHighLarge grade)),
      realMixedSeed parameters reference insideR (grade+6) (realHighLarge grade) base ∈ seedPatch →
      ‖base.ofLp.2.ofLp.1‖ ≤ curvatureBound →
      base ∈ realMixedDomain parameters reference insideR (grade+6) (realHighLarge grade) →
      ‖stateLowering parameters reference insideR realLowLarge (realLowLeHigh grade) base.ofLp.2.ofLp.2‖ ≤ lowStateBound →
      ‖iteratedFDeriv ℝ 2 (completedRealPhysicalMixedSlice parameters cellLength reference insideR grade (by omega))
        base (fun _ => direction)‖ ≤
        constant * ((1+‖base.ofLp.2.ofLp.2‖) *
          ‖realMixedLowering parameters reference insideR realLowLarge (realLowLeHigh grade) direction‖^2 +
          2*‖direction‖*‖realMixedLowering parameters reference insideR realLowLarge (realLowLeHigh grade) direction‖) := by
  obtain ⟨constant,nonnegative,estimate⟩ := physicalMixedDerivativeEstimate parameters cellLength reference insideR
    grade large 2 seedPatch compact patchInside curvatureBound lowStateBound
  refine ⟨constant,nonnegative,fun base direction seedInside curvature inside low => ?_⟩
  simpa only [originalMixedSecond_oneHigh] using estimate base (fun _ => direction) seedInside curvature inside low

end Grad.NashMoser.OriginalLimit

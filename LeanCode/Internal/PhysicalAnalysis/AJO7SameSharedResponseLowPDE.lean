import AJO6ActualRawLowEquations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularLowClassical
open Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularRegularity
open Grad.AnnularFluxTrace Grad.CircularHighRegularity Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.AnnularReconstruction Grad.AnnularCurrentLow Grad.PhaseAlgebra

open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularFullSource Grad.AnnularCurrentSource
open Grad.AnnularCrossMaps Grad.AnnularCoupledInverse Grad.AnnularKnownLow
open Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)

def sharedStrongLowRawSlope (index : LowAnnularIndex) : ℝ → ComplexEuclidean 1 :=
  let solution := sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  let input := fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data solution
  let known := strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data
  let g := (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2
  lowPhysicalRawSlope parameters lower length positive (lowerHalf.trans_lt (by norm_num)) solution.ofLp.2
    (lowPhysicalRowAction parameters length compact lower positive (lowerHalf.trans (by norm_num)) state 0 input + highSourceF lower known)
    (lowPhysicalRowAction parameters length compact lower positive (lowerHalf.trans (by norm_num)) state 1 input)
    (lowPhysicalRowAction parameters length compact lower positive (lowerHalf.trans (by norm_num)) state 2 input - radialRadiusRow lower positive g) index

/-- The SAME full shared-source response satisfies the original low raw
coordinate PDE on the closed collar. The only representative premise states
that a continuous candidate equals the explicit full original RHS a.e. -/
theorem sharedStrongResponse_lowPhysicalSection_derivative (index : LowAnnularIndex)
    (rhs : C(ℝ, ComplexEuclidean 1))
    (actual : rhs =ᵐ[volume.restrict (Icc lower 1)]
      sharedStrongLowRawSlope parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data index)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    let solution := sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
    HasDerivWithinAt (radialSectionExtension 1 lower (lowerHalf.trans (by norm_num))
      (lowPhysicalSection parameters lower length positive (lowerHalf.trans_lt (by norm_num)) solution.ofLp.2 index))
      (rhs radius) (Icc lower 1) radius := by
  let solution := sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  let input := fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data solution
  let first := lowPhysicalRowAction parameters length compact lower positive (lowerHalf.trans (by norm_num)) state 0 input +
    highSourceF lower (strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data)
  let cell := lowPhysicalRowAction parameters length compact lower positive (lowerHalf.trans (by norm_num)) state 1 input
  let angular := lowPhysicalRowAction parameters length compact lower positive (lowerHalf.trans (by norm_num)) state 2 input -
    radialRadiusRow lower positive (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2
  have equation : solution.ofLp.2.val 1 = lowFullRowRHS parameters lower length positive lengthPositive
      (solution.ofLp.2.val 0) first cell angular :=
    sharedStrongResponse_fullLowRow parameters length compact lower positive lengthPositive state lowerHalf widthHalf widthLength small data
  exact lowPhysicalSection_fullRows_derivative parameters lower length positive (lowerHalf.trans_lt (by norm_num))
    lengthPositive solution.ofLp.2 first cell angular equation index rhs actual radius inside

end Grad.AnnularLowClassical

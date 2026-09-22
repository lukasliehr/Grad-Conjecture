import AKS6ActualOriginalEquationDifference

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology
namespace Grad.AnnularWeightedUniqueness
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularReconstruction
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularForwardDatum Grad.AnnularForwardTraces Grad.AnnularStrongOrbit
open Grad.AnnularCoupledInverse Grad.AnnularRestriction Grad.AnnularExhaustionEstimate
open Grad.AnnularIncomingIntegrability Grad.SourceCollarDivision Grad.AnnularSourceGraph
open Grad.AnnularCurrentSource Grad.AnnularVariational Grad.AnnularLowEnergy Grad.AnnularTiltedReference
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule
  traceCoupledRealNormed traceCoupledRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule
  Grad.AnnularStrongOrbit.knownAmbientNormed Grad.AnnularStrongOrbit.knownAmbientSeminormed
  Grad.AnnularStrongOrbit.knownAmbientRealNormed Grad.AnnularStrongOrbit.knownAmbientRealModule
  Grad.AnnularStrongOrbit.strongCarrierNormed Grad.AnnularStrongOrbit.strongCarrierSeminormed
  Grad.AnnularStrongOrbit.strongCarrierRealNormed Grad.AnnularStrongOrbit.strongCarrierRealModule

open Grad.AnnularFullGraph Grad.AnnularWeakExhaustion

open Grad.ActualAnnularExhaustion

open Grad.AnnularHighGenerators

private theorem linear_sub_norm_bound {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (linear : E →L[ℝ] F) (first second : E) (a b : ℝ)
    (firstBound : ‖linear first‖ ≤ a) (secondBound : ‖linear second‖ ≤ b) :
    ‖linear (first - second)‖ ≤ a + b := by
  rw [linear.map_sub]
  exact (norm_sub_le _ _).trans (add_le_add firstBound secondBound)

/-- Two actual compatible weighted original equation families with the same
full source4 and physical outer data are identical. Only their native base
and SAME inserted grade-one bounds enter; no Cartesian regularity is assumed. -/
theorem actualWeightedFamilies_unique
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters length compact)
    (collars : ℕ → ℝ) (positive : ∀ index, 0 < collars index) (lowerHalf : ∀ index, collars index ≤ 1 / 2)
    (decreasing : Antitone collars) (cofinal : Tendsto collars atTop (𝓝 0))
    (first second : ∀ index, OriginalFiveBlockAmbient parameters (collars index) length (positive index))
    (firstCompatible : ∀ k l (included : collars k ≤ collars l),
      originalFiveBlockRestriction parameters (collars k) (collars l) length (positive k) (positive l)
        ((lowerHalf l).trans_lt (by norm_num)) lengthPositive included (first k) = first l)
    (secondCompatible : ∀ k l (included : collars k ≤ collars l),
      originalFiveBlockRestriction parameters (collars k) (collars l) length (positive k) (positive l)
        ((lowerHalf l).trans_lt (by norm_num)) lengthPositive included (second k) = second l)
    (firstEquation : ∀ index, first index ∈ OriginalObservedEquationGraph parameters length compact (collars index) (positive index)
      (lowerHalf index) lengthPositive widthHalf widthLength state)
    (secondEquation : ∀ index, second index ∈ OriginalObservedEquationGraph parameters length compact (collars index) (positive index)
      (lowerHalf index) lengthPositive widthHalf widthLength state)
    (sources : ∀ index, (first index).ofLp.2 = (second index).ofLp.2)
    (outer : ∀ index, originalOuterBoundaryTrace parameters length compact (collars index) (positive index) (lowerHalf index)
      lengthPositive state ((first index).ofLp.1,(first index).ofLp.2.ofLp.1) =
      originalOuterBoundaryTrace parameters length compact (collars index) (positive index) (lowerHalf index)
        lengthPositive state ((second index).ofLp.1,(second index).ofLp.2.ofLp.1)) :
    let native := fun index => originalWeightedRetainedObservation parameters (collars index) length (positive index)
      ((lowerHalf index).trans (by norm_num)) lengthPositive
    ∀ (firstWeighted secondWeighted : ∀ index, CoupledSpace (collars index) length (positive index) lengthPositive)
      (_firstInserted : ∀ index, CoupledInsertedGrade (collars index) length (positive index) lengthPositive 1
        (native index (first index)) (firstWeighted index))
      (_secondInserted : ∀ index, CoupledInsertedGrade (collars index) length (positive index) lengthPositive 1
        (native index (second index)) (secondWeighted index))
      (firstBound secondBound firstGradeBound secondGradeBound : ℝ)
      (_firstNorm : ∀ index, ‖native index (first index)‖ ≤ firstBound)
      (_secondNorm : ∀ index, ‖native index (second index)‖ ≤ secondBound)
      (_firstGradeNorm : ∀ index, ‖firstWeighted index‖ ≤ firstGradeBound)
      (_secondGradeNorm : ∀ index, ‖secondWeighted index‖ ≤ secondGradeBound),
      ∀ index, first index = second index := by
  dsimp only
  intro firstWeighted secondWeighted firstInserted secondInserted firstBound secondBound firstGradeBound secondGradeBound
    firstNorm secondNorm firstGradeNorm secondGradeNorm
  let difference := fun index => first index - second index
  have compatible : ∀ k l (included : collars k ≤ collars l),
      originalFiveBlockRestriction parameters (collars k) (collars l) length (positive k) (positive l)
        ((lowerHalf l).trans_lt (by norm_num)) lengthPositive included (difference k) = difference l := by
    intro k l included
    change originalFiveBlockRestriction parameters (collars k) (collars l) length (positive k) (positive l)
      ((lowerHalf l).trans_lt (by norm_num)) lengthPositive included (first k - second k) = first l - second l
    rw [(originalFiveBlockRestriction parameters (collars k) (collars l) length (positive k) (positive l)
      ((lowerHalf l).trans_lt (by norm_num)) lengthPositive included).map_sub,
      firstCompatible, secondCompatible]
  have equation : ∀ index, difference index ∈ OriginalObservedEquationGraph parameters length compact (collars index) (positive index)
      (lowerHalf index) lengthPositive widthHalf widthLength state := fun index =>
    originalObservedEquationGraph_sub parameters length compact (collars index) (positive index) (lowerHalf index) lengthPositive
      widthHalf widthLength state small (first index) (second index) (firstEquation index) (secondEquation index)
  have sourceZero : ∀ index, (difference index).ofLp.2 = 0 := by
    intro index
    change (first index).ofLp.2 - (second index).ofLp.2 = 0
    exact sub_eq_zero.mpr (sources index)
  have outerZero : ∀ index, originalOuterBoundaryTrace parameters length compact (collars index) (positive index) (lowerHalf index)
      lengthPositive state ((difference index).ofLp.1,(difference index).ofLp.2.ofLp.1) = 0 := by
    intro index
    exact (originalFullOuter_sub parameters length compact (collars index) (positive index) (lowerHalf index) lengthPositive state
      (first index) (second index)).trans (sub_eq_zero.mpr (outer index))
  have result := actualHomogeneousFamily_eq_zero parameters length compact lengthPositive widthHalf widthLength state small
    collars positive lowerHalf decreasing cofinal difference compatible equation sourceZero outerZero
    (fun index => firstWeighted index - secondWeighted index)
    (by
      intro index
      change CoupledInsertedGrade _ _ _ _ 1
        (originalWeightedRetainedObservation parameters (collars index) length (positive index)
          ((lowerHalf index).trans (by norm_num)) lengthPositive (first index - second index)) _
      rw [(originalWeightedRetainedObservation parameters (collars index) length (positive index)
        ((lowerHalf index).trans (by norm_num)) lengthPositive).map_sub]
      exact coupledInserted_sub _ _ _ _ 1 _ _ _ _ (firstInserted index) (secondInserted index))
    (firstBound + secondBound) (firstGradeBound + secondGradeBound)
    (by
      intro index
      exact linear_sub_norm_bound
        (originalWeightedRetainedObservation parameters (collars index) length (positive index)
          ((lowerHalf index).trans (by norm_num)) lengthPositive)
        (first index) (second index) firstBound secondBound (firstNorm index) (secondNorm index))
    (fun index => (norm_sub_le _ _).trans (add_le_add (firstGradeNorm index) (secondGradeNorm index)))
  intro index
  exact sub_eq_zero.mp (result index)

end Grad.AnnularWeightedUniqueness

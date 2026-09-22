import AKS4OwnIncomingRestrictionEstimate

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

private theorem zero_of_reciprocal_bound (value constant : ℝ) (nonnegative : 0 ≤ value)
    (estimate : ∀ᶠ index : ℕ in atTop, value ≤ constant * (1 / ((index : ℝ) + 1))) : value = 0 := by
  have convergence : Tendsto (fun index : ℕ => value - constant * (1 / ((index : ℝ) + 1))) atTop (𝓝 value) := by
    simpa only [mul_zero, sub_zero] using
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))))
  exact le_antisymm (le_of_tendsto convergence (estimate.mono (fun _ bound => sub_nonpos.mpr bound))) nonnegative

/-- Weighted homogeneous uniqueness for actual full original equation
families. Uniform grade zero and SAME inserted grade one suffice. The new
incoming boundary values are always the solution's own traces. -/
theorem actualHomogeneousFamily_eq_zero
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters length compact)
    (collars : ℕ → ℝ) (positive : ∀ index, 0 < collars index) (lowerHalf : ∀ index, collars index ≤ 1 / 2)
    (decreasing : Antitone collars) (cofinal : Tendsto collars atTop (𝓝 0))
    (original : ∀ index, OriginalFiveBlockAmbient parameters (collars index) length (positive index))
    (compatible : ∀ first second (included : collars first ≤ collars second),
      originalFiveBlockRestriction parameters (collars first) (collars second) length (positive first) (positive second)
        ((lowerHalf second).trans_lt (by norm_num)) lengthPositive included (original first) = original second)
    (equation : ∀ index, original index ∈ OriginalObservedEquationGraph parameters length compact (collars index) (positive index)
      (lowerHalf index) lengthPositive widthHalf widthLength state)
    (sources : ∀ index, (original index).ofLp.2 = 0)
    (outer : ∀ index, originalOuterBoundaryTrace parameters length compact (collars index) (positive index) (lowerHalf index)
      lengthPositive state ((original index).ofLp.1,(original index).ofLp.2.ofLp.1) = 0) :
    let fields := fun index => originalWeightedRetainedObservation parameters (collars index) length (positive index)
      ((lowerHalf index).trans (by norm_num)) lengthPositive (original index)
    ∀ (weighted : ∀ index, CoupledSpace (collars index) length (positive index) lengthPositive)
      (_inserted : ∀ index, Grad.AnnularHighGenerators.CoupledInsertedGrade (collars index) length (positive index) lengthPositive 1
        (fields index) (weighted index))
      (retainedBound insertedBound : ℝ)
      (_retained : ∀ index, ‖fields index‖ ≤ retainedBound)
      (_insertedNorm : ∀ index, ‖weighted index‖ ≤ insertedBound),
      ∀ index, original index = 0 := by
  dsimp only
  intro weighted inserted retainedBound insertedBound retained insertedNorm
  let bounded : ∀ index, collars index < 1 := fun index => (lowerHalf index).trans_lt (by norm_num)
  let selected := fullOriginalFamily_common_vanishing_radii parameters (1 / 2) length (by norm_num) (by norm_num)
    lengthPositive collars positive bounded decreasing cofinal original compatible weighted inserted retainedBound insertedBound retained insertedNorm
    ∅ (by simp)
  obtain ⟨radii,inside,_avoids,_geometric,_strict,_incoming,toAxis,_toZero,traces⟩ := selected
  have coefficientNonnegative : 0 ≤ 2 * Grad.AnnularFullSource.independentCoupledDataConstant parameters length compact :=
    mul_nonneg (by norm_num) (Grad.AnnularFullSource.independentCoupledDataConstant_nonnegative parameters length compact)
  intro fixed
  have smallRadius : ∀ᶠ stage in atTop, radii stage < collars fixed := (tendsto_order.1 toAxis).2 _ (positive fixed)
  have estimate : ∀ᶠ stage : ℕ in atTop,
      originalWeightedRetainedNorm parameters (collars fixed) length (positive fixed)
        ((lowerHalf fixed).trans (by norm_num)) lengthPositive (original fixed).ofLp.1 ≤
        (2 * Grad.AnnularFullSource.independentCoupledDataConstant parameters length compact) * (1 / ((stage : ℝ) + 1)) := by
    filter_upwards [smallRadius] with stage smallRadius
    obtain ⟨index,below⟩ := ((tendsto_order.1 cofinal).2 (radii stage) (inside stage).1).exists
    let context := fixedExhaustionContext parameters length compact lengthPositive widthHalf widthLength state small
      (radii stage) (inside stage).1 (inside stage).2
    have bound := homogeneousRestriction_bound parameters length compact (collars index) (collars fixed) context
      (positive index) (positive fixed) (lowerHalf fixed) below.le smallRadius.le
      (original index) (equation index) (sources index) (outer index)
    have same := congrArg (fun item : OriginalFiveBlockAmbient parameters (collars fixed) length (positive fixed) =>
      originalWeightedRetainedNorm parameters (collars fixed) length (positive fixed)
        ((lowerHalf fixed).trans (by norm_num)) lengthPositive item.ofLp.1)
      (compatible index fixed (below.le.trans smallRadius.le))
    exact same.symm.trans_le (bound.trans (mul_le_mul_of_nonneg_left (traces stage index below.le).le coefficientNonnegative))
  have normZero := zero_of_reciprocal_bound _ _ (norm_nonneg _) estimate
  have weightedZero := norm_eq_zero.mp normZero
  have retainedZero : (original fixed).ofLp.1 = 0 :=
    (originalCoupledEquivalence parameters (collars fixed) length (positive fixed)
      ((lowerHalf fixed).trans (by norm_num)) lengthPositive).injective (weightedZero.trans (map_zero _).symm)
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
  exact Prod.ext retainedZero (sources fixed)

end Grad.AnnularWeightedUniqueness

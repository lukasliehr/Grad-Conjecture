import AJM2SameSharedSolvedGraphDensity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
open Set Filter
open scoped Topology
namespace Grad.AnnularSolvedGraphDensity
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongOrbit Grad.AnnularStrongSolution
open Grad.AnnularCoupledInverse Grad.AnnularReconstruction Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)

/-- Closure in the unchanged original source and AK/AJ solution graph norms.
The original datum retains copied F0/F2, every forcing and every boundary datum. -/
theorem originalSolvedGraph_closure :
    closure (range (fun core : OriginalSmoothSourceCore parameters =>
      let data := originalSmoothStrongData parameters lower positive (lowerHalf.trans (by norm_num)) core
      (data,originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data))) =
    range (fun data : OriginalStrongCarrier parameters lower 0 0 =>
      (data,originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)) :=
  continuousFullGraph_closure_eq
    (originalSmoothStrongDenseMap parameters lower positive (lowerHalf.trans (by norm_num))).mapping
    (originalSmoothStrongDenseMap parameters lower positive (lowerHalf.trans (by norm_num))).dense
    (originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (originalSharedResponse_continuous parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)

/-- Exactly the same dense source solve is transported by the accepted BF6 map. -/
theorem originalSmoothSolve_same (core : OriginalSmoothSourceCore parameters) :
    originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      (originalSmoothStrongData parameters lower positive (lowerHalf.trans (by norm_num)) core) =
    (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive).symm
      (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
        ((strongSmoothDenseMap parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive).mapping core)) := rfl

/-- A later proved smooth-solution/core provider can discharge closed membership
without discarding the source or either weak solution graph coordinate. -/
theorem originalSolvedGraph_closed_transfer {Z : Type*} [TopologicalSpace Z]
    (observation : OriginalStrongCarrier parameters lower 0 0 × OriginalCoupledSpace lower length positive → Z)
    (continuousObservation : Continuous observation) (closedSet : Set Z) (closed : IsClosed closedSet)
    (smoothCoreMember : ∀ core : OriginalSmoothSourceCore parameters,
      observation
        (originalSmoothStrongData parameters lower positive (lowerHalf.trans (by norm_num)) core,
          originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
            (originalSmoothStrongData parameters lower positive (lowerHalf.trans (by norm_num)) core)) ∈ closedSet)
    (data : OriginalStrongCarrier parameters lower 0 0) :
    observation (data,originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) ∈ closedSet :=
  continuousFullGraph_closed_transfer
    (originalSmoothStrongDenseMap parameters lower positive (lowerHalf.trans (by norm_num))).mapping
    (originalSmoothStrongDenseMap parameters lower positive (lowerHalf.trans (by norm_num))).dense
    (originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (originalSharedResponse_continuous parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    observation continuousObservation closedSet closed smoothCoreMember data

end Grad.AnnularSolvedGraphDensity

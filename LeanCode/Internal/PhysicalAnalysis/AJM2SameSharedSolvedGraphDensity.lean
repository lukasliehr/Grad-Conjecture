import AJM1ContinuousFullGraphDensity
import AJF48SameSharedResponseContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
open Set Filter
open scoped Topology
namespace Grad.AnnularSolvedGraphDensity
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongOrbit Grad.AnnularStrongSolution
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularReconstruction
open Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)

/-- Joint convergence retains ALL original shared source coordinates and
BOTH actual high/low weak solution graphs, before any observation. -/
theorem sharedSolvedGraph_closure :
    closure (range (fun core : OriginalSmoothSourceCore parameters =>
      let data := (strongSmoothDenseMap parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive).mapping core
      (data,sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data))) =
    range (fun data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 =>
      (data,sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)) :=
  continuousFullGraph_closure_eq
    (strongSmoothDenseMap parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive).mapping
    (strongSmoothDenseMap parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive).dense
    (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (sharedStrongResponse_continuous parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)

theorem sharedSolvedGraph_mem_closure
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0) :
    (data,sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) ∈
      closure (range (fun core : OriginalSmoothSourceCore parameters =>
        let smoothData := (strongSmoothDenseMap parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive).mapping core
        (smoothData,sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small smoothData))) :=
  continuousFullGraph_mem_closure
    (strongSmoothDenseMap parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive).mapping
    (strongSmoothDenseMap parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive).dense
    (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (sharedStrongResponse_continuous parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) data

/-- The original BF5/BF6 maps transport continuity of the SAME response. -/
theorem originalSharedResponse_continuous :
    Continuous (originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) :=
  (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive).symm.continuous.comp
    ((sharedStrongResponse_continuous parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small).comp
      (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0).continuous)

end Grad.AnnularSolvedGraphDensity

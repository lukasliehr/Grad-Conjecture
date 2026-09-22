import AJM3OriginalSourceAndSolutionClosure

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
open Set Filter
open scoped Topology
namespace Grad.AnnularSolvedGraphDensity
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongOrbit Grad.AnnularStrongSolution
open Grad.AnnularCoupledInverse Grad.AnnularReconstruction Grad.GaugeCoefficients.Physical.Allocation

private theorem fullGraph_normApproximation {Core X Y : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    (approximation : Core → X) (response : X → Y) (data : X)
    (joint : (data,response data) ∈ closure (range (fun core => (approximation core,response (approximation core)))))
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ core, ‖approximation core - data‖ < epsilon ∧ ‖response (approximation core) - response data‖ < epsilon := by
  obtain ⟨point,⟨core,rfl⟩,close⟩ := Metric.mem_closure_iff.mp joint epsilon positive
  change max (dist data (approximation core)) (dist (response data) (response (approximation core))) < epsilon at close
  have bounds := max_lt_iff.mp close
  refine ⟨core,?_,?_⟩
  · calc
      _ = ‖data - approximation core‖ := norm_sub_rev _ _
      _ = dist data (approximation core) := (dist_eq_norm _ _).symm
      _ < epsilon := bounds.1
  · calc
      _ = ‖response data - response (approximation core)‖ := norm_sub_rev _ _
      _ = dist (response data) (response (approximation core)) := (dist_eq_norm _ _).symm
      _ < epsilon := bounds.2

private theorem fullEquationGraph {X Y : Type*} (response : X → Y) (equation : X → Y → Prop)
    (solves : ∀ data, equation data (response data))
    (unique : ∀ data candidate, equation data candidate → candidate = response data) :
    range (fun data => (data,response data)) = {point : X × Y | equation point.1 point.2} := by
  ext point
  constructor
  · rintro ⟨data,rfl⟩
    exact solves data
  · intro actual
    exact ⟨point.1,Prod.ext rfl (unique point.1 point.2 actual).symm⟩

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)

/-- Simultaneous approximation in the TWO unchanged original graph norms. -/
theorem originalSolvedGraph_normApproximation (data : OriginalStrongCarrier parameters lower 0 0)
    (epsilon : ℝ) (epsilonPositive : 0 < epsilon) :
    ∃ core : OriginalSmoothSourceCore parameters,
      ‖originalSmoothStrongData parameters lower positive (lowerHalf.trans (by norm_num)) core - data‖ < epsilon ∧
      ‖originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
          (originalSmoothStrongData parameters lower positive (lowerHalf.trans (by norm_num)) core) -
        originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data‖ < epsilon := by
  have joint := continuousFullGraph_mem_closure
    (originalSmoothStrongDenseMap parameters lower positive (lowerHalf.trans (by norm_num))).mapping
    (originalSmoothStrongDenseMap parameters lower positive (lowerHalf.trans (by norm_num))).dense
    (originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (originalSharedResponse_continuous parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) data
  exact fullGraph_normApproximation
    (originalSmoothStrongDenseMap parameters lower positive (lowerHalf.trans (by norm_num))).mapping
    (originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    data joint epsilon epsilonPositive

/-- Exact full solved graph equality, using the actual accepted inverse laws.
No radial smoothness assertion about these solutions is inserted. -/
theorem originalSolvedEquationGraph_closure :
    closure (range (fun core : OriginalSmoothSourceCore parameters =>
      let data := originalSmoothStrongData parameters lower positive (lowerHalf.trans (by norm_num)) core
      (data,originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data))) =
    {point : OriginalStrongCarrier parameters lower 0 0 × OriginalCoupledSpace lower length positive |
      OriginalStrongCoupledEquation parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state point.1 point.2} :=
  (originalSolvedGraph_closure parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small).trans
    (fullEquationGraph
      (originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
      (OriginalStrongCoupledEquation parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state)
      (originalSharedResponse_equation parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
      (originalSharedResponse_unique parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small))

end Grad.AnnularSolvedGraphDensity

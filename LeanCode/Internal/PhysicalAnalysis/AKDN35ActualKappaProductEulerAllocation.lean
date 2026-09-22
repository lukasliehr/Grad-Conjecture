import AKDN34ActualKappaEulerAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.AnnularWeightedSmoothness Grad.AnnularCurrentLow
open Grad.AnnularGeneralSourceRegularity
open Grad.GaugeCoefficients.Physical.Allocation

/-- The actual kappa product in G3 is differentiated before estimating.
Its coefficient derivative remains inside the joint allocation; the input
is the same primitive source at the complementary original frequency grade. -/
theorem actualSourceKappaCurve_EulerAllocation (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (component : Fin 3) (grade rank : ℕ) :
    ∃ first second : ℕ → ℝ, (∀ order, 0 ≤ first order) ∧ (∀ order, 0 ≤ second order) ∧
    ∀ state : RetainedInverseState parameters length compact,
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 ≤ 1 →
    ∀ input : ℕ → ℝ → CellL2 1,
    (∀ power, ContDiffOn ℝ ∞ (input power) (Icc lower 1)) →
    (∀ power reserve radius, radius ∈ Icc lower 1 → ∀ mode,
      input (power+reserve) radius mode=(annularFrequency mode.1 mode.2 : ℂ)^reserve • input power radius mode) →
    ∀ radius : RadialPoint, radius.val ∈ Icc lower 1 →
    ‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank
      (fun point => radialConjugatedAction parameters lower positive bounded.le
        (actualSourceKappaKernel parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low component) grade 0 point (input grade point)) radius.val‖ ≤
      eulerAllocationSum (fun order inputRank => 2^grade *
        (first order*(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+order))*
          ‖vectorEulerWithinIteratedDerivative (Icc lower 1) inputRank (input grade) radius.val‖+
         second order*(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+(order+grade)))*
          ‖vectorEulerWithinIteratedDerivative (Icc lower 1) inputRank (input 0) radius.val‖)) (eulerLeibnizTerms rank) := by
  choose first second first0 second0 bounds using
    fun order => actualSourceKappaEulerAction_complementary parameters length compact component order grade
  refine ⟨first,second,first0,second0,?_⟩
  intro state small input inputSmooth inputSame radius inside
  obtain ⟨reserve,operatorSmooth,operatorSame⟩ := actualSourceKappaOperator_finiteEuler parameters length compact lower positive bounded state component grade rank
  let operator := radialConjugatedAction parameters lower positive bounded.le
    (actualSourceKappaKernel parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low component) grade reserve
  have same : EqOn
      (fun point => radialConjugatedAction parameters lower positive bounded.le
        (actualSourceKappaKernel parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low component) grade 0 point (input grade point))
      (fun point => complexOperatorApply 1 1 (operator point) (input (grade+reserve) point)) (Icc lower 1) := by
    intro point member
    dsimp only
    rw [radialConjugatedAction_zero_apply]
    exact (conjugatedKernelAction_same parameters grade reserve (collarRadius lower positive bounded.le point)
      (actualSourceKappaKernel parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low component (collarRadius lower positive bounded.le point))
      (input (grade+reserve) point) (input grade point) (inputSame grade reserve point member)).symm
  rw [vectorEulerWithin_congr (Icc lower 1) rank _ _ same inside,
    vectorEulerWithin_bilinear (complexOperatorApply 1 1) (Icc lower 1) (uniqueDiffOn_Icc bounded)
      (fun point member => (positive.trans_le member.1).ne') operator (input (grade+reserve)) rank
      operatorSmooth (contDiffOn_infty.mp (inputSmooth _) rank) inside]
  apply (bilinearEulerPolynomial_norm (complexOperatorApply 1 1) _ _ _ radius.val).trans
  apply eulerAllocationSum_mono
  intro term member
  have allocated := eulerLeibnizTerms_rank rank term member
  change ‖vectorEulerWithinIteratedDerivative (Icc lower 1) term.1 operator radius.val
    (vectorEulerWithinIteratedDerivative (Icc lower 1) term.2 (input (grade+reserve)) radius.val)‖ ≤ _
  rw [operatorSame term.1 (by omega) radius inside,
    conjugatedKernelAction_same parameters grade reserve radius _
      (vectorEulerWithinIteratedDerivative (Icc lower 1) term.2 (input (grade+reserve)) radius.val)
      (vectorEulerWithinIteratedDerivative (Icc lower 1) term.2 (input grade) radius.val)
      (cellCurveEuler_shift lower bounded input inputSmooth inputSame grade reserve term.2 radius.val inside)]
  apply bounds term.1 state small radius
  intro mode
  simpa only [Nat.zero_add] using cellCurveEuler_shift lower bounded input inputSmooth inputSame 0 grade term.2 radius.val inside mode

end Grad.OriginalCartesianTameEstimate

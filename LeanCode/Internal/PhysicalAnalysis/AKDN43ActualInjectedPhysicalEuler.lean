import AKDN42ActualKappaPrimitiveEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.AnnularWeightedSmoothness Grad.AnnularCurrentLow
open Grad.AnnularGeneralSourceRegularity Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularSmoothCore Grad.BoundaryLift
open Grad.GaugeCoefficients.Physical.Ledger

/-- Each actual prescribed seven-slot input is a fixed injection of one
original scalar primitive. Its Euler derivatives cost no coefficient rank. -/
theorem actualInjectedPhysicalCurve_EulerAllocation (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (row : Fin 3) (slot : Fin 7) (grade rank : ℕ) :
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
        (lowPhysicalRowKernel parameters length compact state row) grade 0 point
        (hilbertSlotInjection parameters slot (input grade point))) radius.val‖ ≤
      eulerAllocationSum (fun order inputRank => 2^grade *
        (first order*(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+order))*
          ‖vectorEulerWithinIteratedDerivative (Icc lower 1) inputRank (input grade) radius.val‖+
         second order*(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+(order+grade)))*
          ‖vectorEulerWithinIteratedDerivative (Icc lower 1) inputRank (input 0) radius.val‖)) (eulerLeibnizTerms rank) := by
  obtain ⟨first,second,first0,second0,estimate⟩ := samePhysicalRowCurve_EulerAllocation parameters length compact lower
    positive bounded row grade rank
  let inject := hilbertSlotInjection parameters slot
  refine ⟨(fun order => first order*‖inject‖),(fun order => second order*‖inject‖),
    (fun order => mul_nonneg (first0 order) (norm_nonneg _)),
    (fun order => mul_nonneg (second0 order) (norm_nonneg _)),?_⟩
  intro state unit input smooth same radius inside
  let lifted := fun power point => inject (input power point)
  have liftedSmooth (power : ℕ) : ContDiffOn ℝ ∞ (lifted power) (Icc lower 1) :=
    (inject.restrictScalars ℝ).contDiff.comp_contDiffOn (smooth power)
  have liftedSame (power reserve : ℕ) (point : ℝ) (member : point ∈ Icc lower 1) (mode : ℤ × ℤ) :
      lifted (power+reserve) point mode=(annularFrequency mode.1 mode.2 : ℂ)^reserve • lifted power point mode := by
    change (hilbertSlotInjection parameters slot (input (power+reserve) point)) mode = _
    change matrixUnit slot (0 : Fin 1) (input (power+reserve) point mode) = _
    rw [same power reserve point member mode,map_smul]
    rfl
  have actual := estimate state unit lifted liftedSmooth liftedSame radius inside
  apply actual.trans
  apply eulerAllocationSum_mono
  intro term _
  have observed (power : ℕ) :
      ‖vectorEulerWithinIteratedDerivative (Icc lower 1) term.2 (lifted power) radius.val‖ ≤
        ‖inject‖*‖vectorEulerWithinIteratedDerivative (Icc lower 1) term.2 (input power) radius.val‖ := by
    have equality := vectorEulerWithin_observation (Icc lower 1) (uniqueDiffOn_Icc bounded) (input power)
      (inject.restrictScalars ℝ) term.2 (contDiffOn_infty.mp (smooth power) term.2) inside
    change vectorEulerWithinIteratedDerivative (Icc lower 1) term.2 (lifted power) radius.val =
      inject (vectorEulerWithinIteratedDerivative (Icc lower 1) term.2 (input power) radius.val) at equality
    rw [equality]
    exact inject.le_opNorm _
  have budget0 (order : ℕ) : 0 ≤ 1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+order) :=
    add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)
  have comparison := mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left (observed grade) (mul_nonneg (first0 term.1) (budget0 term.1)))
    (mul_le_mul_of_nonneg_left (observed 0) (mul_nonneg (second0 term.1) (budget0 (term.1+grade)))))
    (by positivity : 0 ≤ (2:ℝ)^grade)
  exact comparison.trans_eq (by ring)

end Grad.OriginalCartesianTameEstimate

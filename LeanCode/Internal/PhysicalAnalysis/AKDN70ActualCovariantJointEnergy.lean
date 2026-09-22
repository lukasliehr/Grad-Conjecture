import AKDN69ActualWeightedCovariantEuler
import AKDN45ActualPhysicalPrimitiveEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularReconstruction Grad.AnnularGeneralSourceRegularity
open Grad.AnnularWeightedSmoothness Grad.AnnularSmoothCore Grad.AnnularKernelL2
open Grad.GaugeCoefficients.Physical.Allocation Grad.BoundaryKernelAction

/-- Actual reconstructed Euler action on jointly allocated inputs.
Coefficient weights are already part of the input energy, so no second
high state factor is introduced by this integration. -/
theorem actualEulerFamily_jointEnergy {source target : ℕ}
    (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (kernel : (state : AnnularReconstructionState parameters length compact) →
      (radius : RadialPoint) → RadialKernel parameters radius source target)
    (family : ActualEulerFamily parameters length compact kernel)
    (smooth : ∀ state, SmoothConjugatedFamily parameters lower positive bounded.le (kernel state))
    (total extra power rank : ℕ) (paid : extra+power+rank≤total) :
    ∃ constant : ℝ, 0≤constant ∧
    ∀ state : RetainedInverseState parameters length compact,
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10≤1 →
    ∀ input : ℕ → ℝ → CellL2 source,
    (∀ grade, ContDiffOn ℝ ∞ (input grade) (Icc lower 1)) →
    (∀ grade reserve radius, radius∈Icc lower 1 → ∀ mode,
      input (grade+reserve) radius mode=(annularFrequency mode.1 mode.2 : ℂ)^reserve • input grade radius mode) →
    ∀ payment : ℝ, 0≤payment →
    (∀ extra grade order : ℕ, extra+grade+order≤total →
      (∫⁻ radius in Icc lower 1, ENNReal.ofReal
        (‖(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+extra)) •
          vectorEulerWithinIteratedDerivative (Icc lower 1) order (input grade) radius‖^2)) ≤ ENNReal.ofReal (payment^2)) →
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+extra)) •
        vectorEulerWithinIteratedDerivative (Icc lower 1) rank
          (fun point => radialConjugatedAction parameters lower positive bounded.le (kernel state.val) power 0 point (input power point)) radius‖^2)) ≤
      ENNReal.ofReal ((constant*payment)^2) := by
  obtain ⟨actionConstant,action0,actionBound⟩ := actualEulerFamily_weightedEuler parameters length compact lower
    positive bounded kernel family smooth total extra power rank paid
  refine ⟨actionConstant*(4:ℝ)^(eulerLeibnizTerms rank).length*4,by positivity,?_⟩
  intro state unit input inputSmooth inputSame payment payment0 inputEnergy
  let budget := fun order => 1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+order)
  let values := fun order inputRank radius =>
    ‖budget (extra+order) • vectorEulerWithinIteratedDerivative (Icc lower 1) inputRank (input power) radius‖+
    ‖budget (extra+order+power) • vectorEulerWithinIteratedDerivative (Icc lower 1) inputRank (input 0) radius‖
  have continuous (grade order : ℕ) : ContinuousOn
      (vectorEulerWithinIteratedDerivative (Icc lower 1) order (input grade)) (Icc lower 1) :=
    (vectorEulerWithin_smooth (Icc lower 1) (uniqueDiffOn_Icc bounded) (input grade) order 0
      (by simpa only [Nat.zero_add] using contDiffOn_infty.mp (inputSmooth grade) order)).continuousOn
  have measurable (order inputRank : ℕ) : AEStronglyMeasurable (values order inputRank) (volume.restrict (Icc lower 1)) := by
    have high := ((continuous power inputRank).const_smul (budget (extra+order))).aestronglyMeasurable (μ:=volume) measurableSet_Icc
    have low := ((continuous 0 inputRank).const_smul (budget (extra+order+power))).aestronglyMeasurable (μ:=volume) measurableSet_Icc
    exact (high.norm.add low.norm).congr (Filter.Eventually.of_forall (fun _ => rfl))
  have terminalEnergy (order inputRank : ℕ) (allocated : order+inputRank=rank) :
      (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖values order inputRank radius‖^2)) ≤ ENNReal.ofReal ((4*payment)^2) := by
    have high := inputEnergy (extra+order) power inputRank (by omega)
    have low := inputEnergy (extra+order+power) 0 inputRank (by omega)
    have actual := twoInput_squareEnergy (volume.restrict (Icc lower 1)) (values order inputRank)
      (fun radius => budget (extra+order) • vectorEulerWithinIteratedDerivative (Icc lower 1) inputRank (input power) radius)
      (fun radius => budget (extra+order+power) • vectorEulerWithinIteratedDerivative (Icc lower 1) inputRank (input 0) radius)
      (((continuous power inputRank).const_smul (budget (extra+order))).aestronglyMeasurable (μ:=volume) measurableSet_Icc)
      (((continuous 0 inputRank).const_smul (budget (extra+order+power))).aestronglyMeasurable (μ:=volume) measurableSet_Icc)
      1 1 payment payment (by norm_num) (by norm_num) payment0 payment0
      (by
        apply Filter.Eventually.of_forall
        intro radius
        change ‖‖_‖+‖_‖‖≤_
        rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
        simp only [one_mul]
        exact le_refl _) high low
    exact actual.trans_eq (by congr 1; ring)
  have summed := eulerAllocationSum_squareEnergy (volume.restrict (Icc lower 1)) values
    (4*payment) (by positivity) (eulerLeibnizTerms rank)
    (fun term _ => measurable term.1 term.2)
    (fun term member => terminalEnergy term.1 term.2 (eulerLeibnizTerms_rank rank term member))
  have energy : (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      ((eulerAllocationSum (fun a b => values a b radius) (eulerLeibnizTerms rank))^2)) ≤
      ENNReal.ofReal (((4:ℝ)^(eulerLeibnizTerms rank).length*(4*payment))^2) := by
    simpa only [Real.norm_eq_abs,sq_abs] using summed
  have actual := dominated_squareEnergy (volume.restrict (Icc lower 1))
    (fun radius => budget extra • vectorEulerWithinIteratedDerivative (Icc lower 1) rank
      (fun point => radialConjugatedAction parameters lower positive bounded.le (kernel state.val) power 0 point (input power point)) radius)
    (fun radius => eulerAllocationSum (fun a b => values a b radius) (eulerLeibnizTerms rank))
    actionConstant ((4:ℝ)^(eulerLeibnizTerms rank).length*(4*payment)) action0
    (Filter.Eventually.of_forall (fun _ => eulerAllocationSum_nonnegative _
      (fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) _)) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
      exact actionBound state unit input inputSmooth inputSame ⟨radius,⟨positive.le.trans inside.1,inside.2⟩⟩ inside) energy
  exact actual.trans_eq (by congr 1; ring)

end Grad.OriginalCartesianTameEstimate

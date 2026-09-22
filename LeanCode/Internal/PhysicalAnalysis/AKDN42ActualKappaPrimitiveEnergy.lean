import AKDN41ActualPrimitiveEulerTermEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularReconstruction Grad.AnnularGeneralSourceRegularity
open Grad.FlatSourceProjection Grad.QuotientProjection Grad.AnnularWeightedSmoothness Grad.AnnularSmoothCore
open Grad.AnnularKernelL2 Grad.GaugeCoefficients.Physical.Allocation

/-- The actual kappa/primitive term in G3 has the full joint source energy
at original width and independent F4. No coefficient-derivative or source
energy premise remains in this actual consumer. -/
theorem actualKappaPrimitive_jointEnergy (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (total extra power rank : ℕ)
    (paid : extra+power+rank ≤ total) (component : Fin 3) (slot : Fin 4) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ state : RetainedInverseState parameters length compact,
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 ≤ 1 →
    ∀ source : SmoothQuotient parameters,
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+extra)) •
        vectorEulerWithinIteratedDerivative (Icc lower 1) rank
          (fun point => radialConjugatedAction parameters lower positive bounded.le
            (actualSourceKappaKernel parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low component)
            power 0 point (actualCartesianPrimitiveCurve parameters length lower positive bounded source slot power point)) radius‖^2)) ≤
      ENNReal.ofReal ((constant*(‖quotientEta parameters (4+total) source‖+
        (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+total))*
          ‖quotientEta parameters 4 source‖))^2) := by
  obtain ⟨actionConstant,action0,actionBound⟩ := actualKappaPrimitive_weightedEuler parameters length compact lower
    positive bounded total extra power rank paid component slot
  obtain ⟨terminalConstant,terminal0,terminalEnergy⟩ := actualPrimitiveEulerTerm_pairEnergy parameters length lower
    positive bounded total extra power rank paid slot
  refine ⟨actionConstant*(4:ℝ)^(eulerLeibnizTerms rank).length*terminalConstant,
    mul_nonneg (mul_nonneg action0 (by positivity)) terminal0,?_⟩
  intro state unit source
  let budget := fun order => 1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+order)
  let primitive := actualCartesianPrimitiveCurve parameters length lower positive bounded source slot
  let payment := ‖quotientEta parameters (4+total) source‖+
    budget total*‖quotientEta parameters 4 source‖
  have budget0 (order : ℕ) : 0 ≤ budget order := add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)
  have payment0 : 0 ≤ payment := add_nonneg (norm_nonneg _) (mul_nonneg (budget0 _) (norm_nonneg _))
  let values := fun order inputRank radius =>
    ‖budget (extra+order) • vectorEulerWithinIteratedDerivative (Icc lower 1) inputRank (primitive power) radius‖+
    ‖budget (extra+order+power) • vectorEulerWithinIteratedDerivative (Icc lower 1) inputRank (primitive 0) radius‖
  have measurable (order inputRank : ℕ) : AEStronglyMeasurable (values order inputRank) (volume.restrict (Icc lower 1)) := by
    have high := ((actualPrimitiveEuler_continuous parameters length lower positive bounded source slot power inputRank).const_smul
      (budget (extra+order))).aestronglyMeasurable (μ := volume) measurableSet_Icc
    have low := ((actualPrimitiveEuler_continuous parameters length lower positive bounded source slot 0 inputRank).const_smul
      (budget (extra+order+power))).aestronglyMeasurable (μ := volume) measurableSet_Icc
    apply (high.norm.add low.norm).congr
    exact Filter.Eventually.of_forall (fun _ => rfl)
  have summed := eulerAllocationSum_squareEnergy (volume.restrict (Icc lower 1)) values
    (terminalConstant*payment) (mul_nonneg terminal0 payment0) (eulerLeibnizTerms rank)
    (fun term _ => measurable term.1 term.2) (by
      intro term member
      exact terminalEnergy state.val.val.field state.val.val.rho state.val.val.epsilon unit source term.1 term.2
        (eulerLeibnizTerms_rank rank term member))
  have energy : (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      ((eulerAllocationSum (fun a b => values a b radius) (eulerLeibnizTerms rank))^2)) ≤
      ENNReal.ofReal (((4:ℝ)^(eulerLeibnizTerms rank).length*(terminalConstant*payment))^2) := by
    simpa only [Real.norm_eq_abs,sq_abs] using summed
  have actual := dominated_squareEnergy (volume.restrict (Icc lower 1))
    (fun radius => budget extra • vectorEulerWithinIteratedDerivative (Icc lower 1) rank
      (fun point => radialConjugatedAction parameters lower positive bounded.le
        (actualSourceKappaKernel parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low component)
        power 0 point (primitive power point)) radius)
    (fun radius => eulerAllocationSum (fun a b => values a b radius) (eulerLeibnizTerms rank))
    actionConstant ((4:ℝ)^(eulerLeibnizTerms rank).length*(terminalConstant*payment)) action0
    (Filter.Eventually.of_forall (fun _ => eulerAllocationSum_nonnegative _
      (fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) _)) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
      exact actionBound state unit source ⟨radius,⟨positive.le.trans inside.1,inside.2⟩⟩ inside) energy
  exact actual.trans_eq (by congr 1; ring)

end Grad.OriginalCartesianTameEstimate

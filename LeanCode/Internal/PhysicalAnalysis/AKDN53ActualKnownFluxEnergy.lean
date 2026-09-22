import AKDN50ActualKnownRowEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularReconstruction Grad.AnnularGeneralSourceRegularity
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothness Grad.AnnularCurrentLow Grad.QuotientProjection
open Grad.GaugeCoefficients.Physical.Allocation

def actualKnownSourceRowCurve (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (state : RetainedInverseState parameters length compact)
    (source : SmoothQuotient parameters) (power : ℕ) (row : Fin 3) (radius : ℝ) : CellL2 1 :=
  radialConjugatedAction parameters lower positive bounded.le
    (lowPhysicalRowKernel parameters length compact state row) power 0 radius
    (actualCartesianKnownSevenCurve parameters length lower positive bounded source power radius)

theorem actualKnownSourceRowCurve_smooth (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (state : RetainedInverseState parameters length compact)
    (source : SmoothQuotient parameters) (power : ℕ) (row : Fin 3) :
    ContDiffOn ℝ ∞ (actualKnownSourceRowCurve parameters length compact lower positive bounded state source power row) (Icc lower 1) := by
  have smooth := actualPhysicalPrimitiveCurve_smooth parameters length compact lower positive bounded state source row
  apply (((smooth 4 0 power).add (smooth 5 1 power)).add (smooth 6 2 power)).congr
  intro point _
  dsimp only [actualKnownSourceRowCurve,actualCartesianKnownSevenCurve]
  rw [map_add,map_add]
  rfl

/-- The literal known j/c/rV flux assembly loses no rank beyond its
actual input grade. All finite lower Euler ranks share one source payment. -/
theorem actualKnownFlux_jointEulerEnergy (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (total extra power rank : ℕ)
    (paid : extra+power+rank ≤ total) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ state : RetainedInverseState parameters length compact,
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 ≤ 1 →
    ∀ source : SmoothQuotient parameters,
    let rows := actualKnownSourceRowCurve parameters length compact lower positive bounded state source power
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+extra)) •
        vectorEulerWithinIteratedDerivative (Icc lower 1) rank
          (fun point => balancedFluxOutput parameters length point (rows 0 point,(rows 1 point,rows 2 point))) radius‖^2)) ≤
      ENNReal.ofReal ((constant*(‖quotientEta parameters (4+total) source‖+
        (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+total))*
          ‖quotientEta parameters 4 source‖))^2) := by
  choose constants constants0 rowEnergy using (fun index : Fin 3 × Fin (rank+1) =>
    actualKnownRow_jointEnergy parameters length compact lower positive bounded total extra power index.2.val (by omega) index.1)
  obtain ⟨terminal,terminalOne,uniform⟩ := finiteUniformMajorant constants
  have terminal0 : 0 ≤ terminal := zero_le_one.trans terminalOne
  obtain ⟨flux,flux0,fluxBound⟩ := balancedFluxCurve_EulerNormRows parameters length
  let finiteFactor : ℝ := 4^(Finset.univ : Finset (Fin 3)).card
  have finite0 : 0 ≤ finiteFactor := by positivity
  refine ⟨flux*4^(eulerLeibnizTerms rank).length*(finiteFactor*terminal),by positivity,?_⟩
  intro state unit source
  dsimp only
  let rows := actualKnownSourceRowCurve parameters length compact lower positive bounded state source power
  let weight := 1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+extra)
  let payment := ‖quotientEta parameters (4+total) source‖+
    (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+total))*‖quotientEta parameters 4 source‖
  have weight0 : 0 ≤ weight := add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)
  have payment0 : 0 ≤ payment := add_nonneg (norm_nonneg _)
    (mul_nonneg (add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)) (norm_nonneg _))
  have smooth (row : Fin 3) (order : ℕ) : ContDiffOn ℝ order (rows row) (Icc lower 1) :=
    contDiffOn_infty.mp (actualKnownSourceRowCurve_smooth parameters length compact lower positive bounded state source power row) order
  let values := fun (_left right : ℕ) radius =>
    ∑ row : Fin 3, ‖weight • vectorEulerWithinIteratedDerivative (Icc lower 1) right (rows row) radius‖
  have componentMeasurable (row : Fin 3) (order : ℕ) :=
    ((weightedEuler_continuous lower bounded (rows row) order (smooth row order) weight).aestronglyMeasurable
      (μ := volume) measurableSet_Icc).norm
  have measurable (left right : ℕ) : AEStronglyMeasurable (values left right) (volume.restrict (Icc lower 1)) := by
    apply (((componentMeasurable 0 right).add (componentMeasurable 1 right)).add (componentMeasurable 2 right)).congr
    apply Filter.Eventually.of_forall
    intro radius
    dsimp only [values]
    rw [Fin.sum_univ_three]
    rfl
  have termEnergy (term : ℕ × ℕ) (member : term ∈ eulerLeibnizTerms rank) :
      (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖values term.1 term.2 radius‖^2)) ≤
      ENNReal.ofReal (((finiteFactor*terminal)*payment)^2) := by
    have allocated := eulerLeibnizTerms_rank rank term member
    have componentEnergy (row : Fin 3) :
        (∫⁻ radius in Icc lower 1, ENNReal.ofReal
          (‖‖weight • vectorEulerWithinIteratedDerivative (Icc lower 1) term.2 (rows row) radius‖‖^2)) ≤
        ENNReal.ofReal ((terminal*payment)^2) := by
      let index : Fin 3 × Fin (rank+1) := (row,⟨term.2,by omega⟩)
      simp only [norm_norm]
      apply (rowEnergy index state unit source).trans
      apply ENNReal.ofReal_le_ofReal
      apply (sq_le_sq₀ (mul_nonneg (constants0 index) payment0) (mul_nonneg terminal0 payment0)).mpr
      exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (uniform index)) payment0
    have sumEnergy := finiteSum_squareEnergy (volume.restrict (Icc lower 1))
      (fun (row : Fin 3) radius => ‖weight • vectorEulerWithinIteratedDerivative (Icc lower 1) term.2 (rows row) radius‖)
      (fun row => componentMeasurable row term.2) (terminal*payment) (mul_nonneg terminal0 payment0) componentEnergy Finset.univ
    exact sumEnergy.trans_eq (by congr 1; dsimp only [finiteFactor]; ring)
  have summed := eulerAllocationSum_squareEnergy (volume.restrict (Icc lower 1)) values
    ((finiteFactor*terminal)*payment) (by positivity) (eulerLeibnizTerms rank)
    (fun term _ => measurable term.1 term.2) termEnergy
  have energy : (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      ((eulerAllocationSum (fun a b => values a b radius) (eulerLeibnizTerms rank))^2)) ≤
      ENNReal.ofReal (((4:ℝ)^(eulerLeibnizTerms rank).length*((finiteFactor*terminal)*payment))^2) := by
    simpa only [Real.norm_eq_abs,sq_abs] using summed
  have actual := dominated_squareEnergy (volume.restrict (Icc lower 1))
    (fun radius => weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank
      (fun point => balancedFluxOutput parameters length point (rows 0 point,(rows 1 point,rows 2 point))) radius)
    (fun radius => eulerAllocationSum (fun a b => values a b radius) (eulerLeibnizTerms rank))
    flux ((4:ℝ)^(eulerLeibnizTerms rank).length*((finiteFactor*terminal)*payment)) flux0
    (Filter.Eventually.of_forall (fun _ => eulerAllocationSum_nonnegative _
      (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) _)) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
      have pointBound := mul_le_mul_of_nonneg_left (fluxBound lower positive bounded (rows 0) (rows 1) (rows 2) rank
        (smooth 0 rank) (smooth 1 rank) (smooth 2 rank) ⟨radius,⟨positive.le.trans inside.1,inside.2⟩⟩ inside) weight0
      simp only [norm_smul,Real.norm_of_nonneg weight0]
      dsimp only [values]
      simp only [Fin.sum_univ_three,norm_smul,Real.norm_of_nonneg weight0]
      have distribute : (fun (_left right : ℕ) =>
          weight*‖vectorEulerWithinIteratedDerivative (Icc lower 1) right (rows 0) radius‖+
          weight*‖vectorEulerWithinIteratedDerivative (Icc lower 1) right (rows 1) radius‖+
          weight*‖vectorEulerWithinIteratedDerivative (Icc lower 1) right (rows 2) radius‖) =
          (fun _left right => weight*(‖vectorEulerWithinIteratedDerivative (Icc lower 1) right (rows 0) radius‖+
            ‖vectorEulerWithinIteratedDerivative (Icc lower 1) right (rows 1) radius‖+
            ‖vectorEulerWithinIteratedDerivative (Icc lower 1) right (rows 2) radius‖)) := by funext a b; ring
      rw [distribute,←eulerAllocationSum_mul_left]
      nlinarith only [pointBound]) energy
  exact actual.trans_eq (by congr 1; ring)

end Grad.OriginalCartesianTameEstimate

import AKDN46FixedRadiusEulerNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.AnnularGeneralSourceRegularity Grad.QuotientProjection
open Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Allocation Grad.OriginalTerminalAllocation

theorem actualScalarEuler_continuous (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (source : ACore parameters 1) (power rank : ℕ) :
    ContinuousOn (vectorEulerWithinIteratedDerivative (Icc lower 1) rank
      (cartesianWeightedRadialCurve parameters lower positive bounded source power 0)) (Icc lower 1) := by
  exact (vectorEulerWithin_smooth (Icc lower 1) (uniqueDiffOn_Icc bounded)
    (cartesianWeightedRadialCurve parameters lower positive bounded source power 0) rank 0
    (by simpa only [Nat.zero_add] using (contDiffOn_infty.mp
      (cartesianWeightedRadialCurve_smooth parameters lower positive bounded source power 0) rank))).continuousOn

/-- The literal radius times source-2 contribution to rG3, and every fixed
real linear observation of it, retains the original joint source payment. -/
theorem actualRadiusSource_jointEnergy (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (total extra power rank : ℕ)
    (paid : extra+power+rank ≤ total) (mapping : CellL2 1 →L[ℝ] CellL2 1) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (field : ACore parameters 3) (rho epsilon : ℝ), physicalBudget parameters field rho epsilon 10 ≤ 1 →
    ∀ (source : SmoothQuotient parameters) (row : Fin 4),
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖(1+physicalBudget parameters field rho epsilon (10+extra)) •
        vectorEulerWithinIteratedDerivative (Icc lower 1) rank
          (fun point => point • mapping
            (cartesianWeightedRadialCurve parameters lower positive bounded (source row) power 0 point)) radius‖^2)) ≤
      ENNReal.ofReal ((constant*(‖quotientEta parameters (4+total) source‖+
        (1+physicalBudget parameters field rho epsilon (10+total))*‖quotientEta parameters 4 source‖))^2) := by
  choose constants constants0 terminalEnergy using
    (fun order : Fin (rank+1) => actualScalarSource_jointTerminalEnergy parameters lower positive bounded
      total extra power order.val (by omega))
  obtain ⟨terminalConstant,terminalOne,uniform⟩ := finiteUniformMajorant constants
  have terminal0 : 0 ≤ terminalConstant := zero_le_one.trans terminalOne
  refine ⟨‖mapping‖*(4:ℝ)^(eulerLeibnizTerms rank).length*terminalConstant,
    mul_nonneg (mul_nonneg (norm_nonneg _) (by positivity)) terminal0,?_⟩
  intro field rho epsilon unit source row
  let weight := 1+physicalBudget parameters field rho epsilon (10+extra)
  let curve := cartesianWeightedRadialCurve parameters lower positive bounded (source row) power 0
  let payment := ‖quotientEta parameters (4+total) source‖+
    (1+physicalBudget parameters field rho epsilon (10+total))*‖quotientEta parameters 4 source‖
  have weight0 : 0 ≤ weight := add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)
  have payment0 : 0 ≤ payment := add_nonneg (norm_nonneg _)
    (mul_nonneg (add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)) (norm_nonneg _))
  let values := fun (_order inputRank : ℕ) radius =>
    ‖weight • vectorEulerWithinIteratedDerivative (Icc lower 1) inputRank curve radius‖
  have measurable (order inputRank : ℕ) : AEStronglyMeasurable (values order inputRank) (volume.restrict (Icc lower 1)) :=
    (((actualScalarEuler_continuous parameters lower positive bounded (source row) power inputRank).const_smul
      weight).aestronglyMeasurable measurableSet_Icc).norm
  have termEnergy (term : ℕ × ℕ) (member : term ∈ eulerLeibnizTerms rank) :
      (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖values term.1 term.2 radius‖^2)) ≤
      ENNReal.ofReal ((terminalConstant*payment)^2) := by
    have allocated := eulerLeibnizTerms_rank rank term member
    let index : Fin (rank+1) := ⟨term.2,by omega⟩
    have actual := terminalEnergy index field rho epsilon unit source row
    simp only [values,norm_norm]
    apply actual.trans
    apply ENNReal.ofReal_le_ofReal
    apply (sq_le_sq₀ (mul_nonneg (constants0 index) payment0) (mul_nonneg terminal0 payment0)).mpr
    exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (uniform index)) payment0
  have summed := eulerAllocationSum_squareEnergy (volume.restrict (Icc lower 1)) values
    (terminalConstant*payment) (mul_nonneg terminal0 payment0) (eulerLeibnizTerms rank)
    (fun term _ => measurable term.1 term.2) termEnergy
  have energy : (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      ((eulerAllocationSum (fun a b => values a b radius) (eulerLeibnizTerms rank))^2)) ≤
      ENNReal.ofReal (((4:ℝ)^(eulerLeibnizTerms rank).length*(terminalConstant*payment))^2) := by
    simpa only [Real.norm_eq_abs,sq_abs] using summed
  have smooth : ContDiffOn ℝ rank curve (Icc lower 1) := contDiffOn_infty.mp
    (cartesianWeightedRadialCurve_smooth parameters lower positive bounded (source row) power 0) rank
  have actual := dominated_squareEnergy (volume.restrict (Icc lower 1))
    (fun radius => weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank
      (fun point => point • mapping (curve point)) radius)
    (fun radius => eulerAllocationSum (fun a b => values a b radius) (eulerLeibnizTerms rank))
    ‖mapping‖ ((4:ℝ)^(eulerLeibnizTerms rank).length*(terminalConstant*payment)) (norm_nonneg _)
    (Filter.Eventually.of_forall (fun _ => eulerAllocationSum_nonnegative _ (fun _ _ => norm_nonneg _) _)) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
      exact radiusMapping_weightedEulerBound mapping lower positive bounded curve rank smooth weight weight0 radius inside) energy
  exact actual.trans_eq (by congr 1; ring)

end Grad.OriginalCartesianTameEstimate

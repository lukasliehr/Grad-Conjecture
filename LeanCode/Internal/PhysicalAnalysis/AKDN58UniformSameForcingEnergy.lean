import AKDN57SameIncomingForcingEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory
open scoped ENNReal
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularReconstruction Grad.AnnularGeneralSourceRegularity
open Grad.AnnularStrongData Grad.AnnularStrongOrbit Grad.AnnularStrongSolution Grad.AnnularKernelL2
open Grad.QuotientProjection Grad.GaugeCoefficients.Physical.Allocation Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation

/-- The full forcing estimate depends only on the actual four source
blocks. The incoming data of the SAME native solution are preserved. -/
theorem sameIncomingBalancedSource_uniformEulerEnergy (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (total : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ state : RetainedInverseState parameters length compact,
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 ≤ 1 →
    ∀ (source : SmoothQuotient parameters) (flat : IsFlat source)
      (original : OriginalStrongCarrier parameters lower 0 0)
      (sameSources : original.val.ofLp.1 =
        (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
          lower positive bounded 0 source flat).val.ofLp.1),
    ∀ (extra grade rank : ℕ), extra+grade+rank+1 ≤ total →
    let data := originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 original
    let curves := actualCartesianSourceCurves_of_sourceBlocks parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
      state.val.val.low lower positive bounded lengthPositive source flat original sameSources
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+extra)) •
        vectorEulerWithinIteratedDerivative (Icc lower 1) rank
          (fun point => balancedActualSource parameters length compact lower positive bounded state data curves grade
            (collarRadius lower positive bounded.le point)) radius‖^2)) ≤
      ENNReal.ofReal ((constant*(‖quotientEta parameters (4+total) source‖+
        (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+total))*
          ‖quotientEta parameters 4 source‖))^2) := by
  classical
  let Index := {index : Fin (total+1) × Fin (total+1) × Fin (total+1) //
    index.1.val+index.2.1.val+index.2.2.val+1≤total}
  let results := fun index : Index =>
    sameIncomingBalancedSource_jointEulerEnergy parameters length compact lower positive bounded lengthPositive
      total index.val.1.val index.val.2.1.val index.val.2.2.val index.property
  let constants := fun index => (results index).choose
  have constants0 := fun index => (results index).choose_spec.1
  have energy := fun index => (results index).choose_spec.2
  let majorant := finiteUniformMajorant constants
  let constant := majorant.choose
  have constantOne := majorant.choose_spec.1
  have uniform := majorant.choose_spec.2
  have constant0 : 0 ≤ constant := zero_le_one.trans constantOne
  refine ⟨constant,constant0,?_⟩
  intro state unit source flat original sameSources extra grade rank paid
  dsimp only
  let index : Index := ⟨(⟨extra,by omega⟩,⟨grade,by omega⟩,⟨rank,by omega⟩),paid⟩
  have actual := energy index state unit source flat original sameSources
  apply actual.trans
  apply ENNReal.ofReal_le_ofReal
  have payment0 : 0 ≤ ‖quotientEta parameters (4+total) source‖+
      (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+total))*
        ‖quotientEta parameters 4 source‖ := add_nonneg (norm_nonneg _)
    (mul_nonneg (add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)) (norm_nonneg _))
  apply (sq_le_sq₀ (mul_nonneg (constants0 index) payment0) (mul_nonneg constant0 payment0)).mpr
  exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (uniform index)) payment0

end Grad.OriginalCartesianTameEstimate

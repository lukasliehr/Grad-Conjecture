import AKDN54ActualBalancedForcingEnergy
import AKDN56PureBalancedPairEnergy

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
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothness Grad.AnnularCurrentLow

theorem balancedActualSource_same_curves (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (state : RetainedInverseState parameters length compact)
    (firstData secondData : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (first : ActualSourceRadialCurves parameters lower positive bounded firstData)
    (second : ActualSourceRadialCurves parameters lower positive bounded secondData)
    (seven : first.seven=second.seven) (force : first.force=second.force) (third : first.third=second.third)
    (grade : ℕ) (radius : RadialPoint) :
    balancedActualSource parameters length compact lower positive bounded state firstData first grade radius =
      balancedActualSource parameters length compact lower positive bounded state secondData second grade radius := by
  dsimp only [balancedActualSource]
  rw [seven,force,third]

/-- The full forcing estimate depends only on the actual four source
blocks. The incoming data of the SAME native solution are preserved. -/
theorem sameIncomingBalancedSource_jointEulerEnergy (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (total extra grade rank : ℕ) (paid : extra+grade+rank+1 ≤ total) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ state : RetainedInverseState parameters length compact,
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 ≤ 1 →
    ∀ (source : SmoothQuotient parameters) (flat : IsFlat source)
      (original : OriginalStrongCarrier parameters lower 0 0)
      (sameSources : original.val.ofLp.1 =
        (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
          lower positive bounded 0 source flat).val.ofLp.1),
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
  let result := actualBalancedSource_jointEulerEnergy parameters length compact lower
    positive bounded lengthPositive total extra grade rank paid
  let constant := result.choose
  have constant0 : 0 ≤ constant := result.choose_spec.1
  have energy := result.choose_spec.2
  refine ⟨constant,constant0,?_⟩
  intro state unit source flat original sameSources
  dsimp only
  let firstData := originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 original
  let firstCurves := actualCartesianSourceCurves_of_sourceBlocks parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
    state.val.val.low lower positive bounded lengthPositive source flat original sameSources
  let secondData := actualCartesianWeightedDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
    state.val.val.low lower positive bounded lengthPositive source flat
  let secondCurves := actualCartesianSourceRadialCurves parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
    state.val.val.low lower positive bounded lengthPositive source flat
  have same := eulerCurve_squareEnergy_congr lower
    (fun point => balancedActualSource parameters length compact lower positive bounded state firstData firstCurves grade
      (collarRadius lower positive bounded.le point))
    (fun point => balancedActualSource parameters length compact lower positive bounded state secondData secondCurves grade
      (collarRadius lower positive bounded.le point)) (by
        intro point _
        exact balancedActualSource_same_curves parameters length compact lower positive bounded state firstData secondData
          firstCurves secondCurves rfl rfl rfl grade (collarRadius lower positive bounded.le point)) rank
    (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+extra))
  exact same.le.trans (energy state unit source flat)

end Grad.OriginalCartesianTameEstimate

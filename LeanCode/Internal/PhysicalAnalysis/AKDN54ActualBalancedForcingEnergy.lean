import AKDN52ActualThirdSourceEulerEnergy
import AKDN53ActualKnownFluxEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularReconstruction Grad.AnnularGeneralSourceRegularity
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothness Grad.AnnularCurrentLow Grad.QuotientProjection
open Grad.GaugeCoefficients.Physical.Allocation Grad.OriginalTerminalAllocation Grad.FlatSourceProjection
open Grad.AnnularKernelL2

/-- The SAME actual balanced forcing has every jointly weighted Euler
energy required by the native recurrence. The original phase, closed collar,
all prescribed slots and literal rG3 are retained; no source estimate is assumed. -/
theorem actualBalancedSource_jointEulerEnergy (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (total extra grade rank : ℕ) (paid : extra+grade+rank+1 ≤ total) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ state : RetainedInverseState parameters length compact,
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 ≤ 1 →
    ∀ (source : SmoothQuotient parameters) (flat : IsFlat source),
    let data := actualCartesianWeightedDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
      state.val.val.low lower positive bounded lengthPositive source flat
    let curves := actualCartesianSourceRadialCurves parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
      state.val.val.low lower positive bounded lengthPositive source flat
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+extra)) •
        vectorEulerWithinIteratedDerivative (Icc lower 1) rank
          (fun point => balancedActualSource parameters length compact lower positive bounded state data curves grade
            (collarRadius lower positive bounded.le point)) radius‖^2)) ≤
      ENNReal.ofReal ((constant*(‖quotientEta parameters (4+total) source‖+
        (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+total))*
          ‖quotientEta parameters 4 source‖))^2) := by
  let forceMap : CellL2 1 →L[ℝ] PhysicalHilbertPair :=
    (ContinuousLinearMap.inl ℝ (CellL2 1) (CellL2 1)).comp ((hilbertMeanFree parameters).restrictScalars ℝ)
  let thirdMap : CellL2 1 →L[ℝ] PhysicalHilbertPair :=
    (ContinuousLinearMap.inr ℝ (CellL2 1) (CellL2 1)).comp
      ((hilbertFrequencyOperator parameters 1 (some false)).restrictScalars ℝ)
  obtain ⟨flux,flux0,fluxEnergy⟩ := actualKnownFlux_jointEulerEnergy parameters length compact lower positive bounded
    total extra (grade+1) rank (by omega)
  obtain ⟨force,force0,forceEnergy⟩ := actualPrimitive_jointTerminalEnergy parameters length lower positive bounded
    total extra (grade+1) rank (by omega)
  obtain ⟨third,third0,thirdEnergy⟩ := actualThirdSource_jointEulerEnergy parameters length compact lower positive bounded
    total extra grade rank (by omega)
  let directConstant := 2*(‖forceMap‖*force 3+‖thirdMap‖*third)
  have direct0 : 0 ≤ directConstant := by
    have forcePositive := force0 3
    dsimp only [directConstant]
    positivity
  refine ⟨2*(flux+directConstant),by positivity,?_⟩
  intro state unit source flat
  dsimp only
  let data := actualCartesianWeightedDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
    state.val.val.low lower positive bounded lengthPositive source flat
  let curves := actualCartesianSourceRadialCurves parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
    state.val.val.low lower positive bounded lengthPositive source flat
  let weight := 1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+extra)
  let payment := ‖quotientEta parameters (4+total) source‖+
    (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+total))*‖quotientEta parameters 4 source‖
  have payment0 : 0 ≤ payment := add_nonneg (norm_nonneg _)
    (mul_nonneg (add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)) (norm_nonneg _))
  let rows := actualKnownSourceRowCurve parameters length compact lower positive bounded state source (grade+1)
  let fluxCurve := fun point => balancedFluxOutput parameters length point (rows 0 point,(rows 1 point,rows 2 point))
  let forceCurve := actualCartesianPrimitiveCurve parameters length lower positive bounded source 3 (grade+1)
  let thirdCurve := actualCartesianThirdCurve parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
    state.val.val.low lower positive bounded source flat (grade+1)
  have rowsSmooth (row : Fin 3) : ContDiffOn ℝ ∞ (rows row) (Icc lower 1) :=
    actualKnownSourceRowCurve_smooth parameters length compact lower positive bounded state source (grade+1) row
  have fluxSmooth : ContDiffOn ℝ rank fluxCurve (Icc lower 1) := contDiffOn_infty.mp
    (balancedFluxCurve_smooth parameters length (Icc lower 1) _
      ((rowsSmooth 0).prodMk ((rowsSmooth 1).prodMk (rowsSmooth 2)))) rank
  have forceSmooth : ContDiffOn ℝ rank forceCurve (Icc lower 1) := contDiffOn_infty.mp
    ((actualCartesianPrimitiveRadialCurves parameters length lower positive bounded source 3).smooth (grade+1)) rank
  have thirdSmooth : ContDiffOn ℝ rank thirdCurve (Icc lower 1) := contDiffOn_infty.mp
    (actualCartesianThirdCurve_smooth parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
      state.val.val.low lower positive bounded source flat (grade+1)) rank
  have firstObservation := eulerCurve_squareEnergy_observation lower bounded forceCurve rank forceSmooth forceMap weight
    (force 3*payment) (forceEnergy state.val.val.field state.val.val.rho state.val.val.epsilon unit source 3)
  have secondObservation := eulerCurve_squareEnergy_observation lower bounded thirdCurve rank thirdSmooth thirdMap weight
    (third*payment) (thirdEnergy state unit source flat)
  have direct := eulerCurve_squareEnergy_add lower bounded (fun point => forceMap (forceCurve point))
    (fun point => thirdMap (thirdCurve point)) rank (forceMap.contDiff.comp_contDiffOn forceSmooth)
    (thirdMap.contDiff.comp_contDiffOn thirdSmooth) weight (‖forceMap‖*(force 3*payment)) (‖thirdMap‖*(third*payment))
    (mul_nonneg (norm_nonneg _) (mul_nonneg (force0 3) payment0)) (by positivity) firstObservation secondObservation
  have directEnergy : (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank
        (fun point => forceMap (forceCurve point)+thirdMap (thirdCurve point)) radius‖^2)) ≤
      ENNReal.ofReal ((directConstant*payment)^2) :=
    direct.trans_eq (by dsimp only [directConstant]; congr 1; ring)
  have full := eulerCurve_squareEnergy_add lower bounded fluxCurve
    (fun point => forceMap (forceCurve point)+thirdMap (thirdCurve point)) rank fluxSmooth
    ((forceMap.contDiff.comp_contDiffOn forceSmooth).add (thirdMap.contDiff.comp_contDiffOn thirdSmooth)) weight
    (flux*payment) (directConstant*payment) (mul_nonneg flux0 payment0) (mul_nonneg direct0 payment0)
    (fluxEnergy state unit source) directEnergy
  have same := eulerCurve_squareEnergy_congr lower
    (fun point => balancedActualSource parameters length compact lower positive bounded state data curves grade
      (collarRadius lower positive bounded.le point))
    (fun point => fluxCurve point+(forceMap (forceCurve point)+thirdMap (thirdCurve point))) (by
      intro point inside
      dsimp only
      rw [balancedActualSource_sameKnownCurves parameters length compact lower positive bounded state data curves grade point inside]
      apply congrArg₂ (fun left right : PhysicalHilbertPair => left+right)
      · rfl
      · change (hilbertMeanFree parameters (forceCurve point),hilbertFrequencyOperator parameters 1 (some false) (thirdCurve point)) =
          (hilbertMeanFree parameters (forceCurve point)+0,0+hilbertFrequencyOperator parameters 1 (some false) (thirdCurve point))
        rw [add_zero,zero_add]) rank weight
  exact same.le.trans (full.trans_eq (by congr 1; ring))

end Grad.OriginalCartesianTameEstimate

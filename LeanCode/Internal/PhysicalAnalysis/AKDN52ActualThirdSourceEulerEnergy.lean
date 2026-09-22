import AKDN50ActualKnownRowEnergy
import AKDN51SignedEulerEnergyAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularReconstruction Grad.AnnularGeneralSourceRegularity
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothness Grad.AnnularCurrentLow Grad.QuotientProjection
open Grad.GaugeCoefficients.Physical.Allocation Grad.OriginalTerminalAllocation Grad.FlatSourceProjection

/-- Genuine Euler energy of the SAME actual rG3 source, with its literal
signed kappa expansion and one joint original-source payment. -/
theorem actualThirdSource_jointEulerEnergy (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (total extra grade rank : ℕ)
    (paid : extra+(grade+1)+rank ≤ total) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ state : RetainedInverseState parameters length compact,
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 ≤ 1 →
    ∀ (source : SmoothQuotient parameters) (flat : IsFlat source),
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+extra)) •
        vectorEulerWithinIteratedDerivative (Icc lower 1) rank
          (actualCartesianThirdCurve parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
            state.val.val.low lower positive bounded source flat (grade+1)) radius‖^2)) ≤
      ENNReal.ofReal ((constant*(‖quotientEta parameters (4+total) source‖+
        (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+total))*
          ‖quotientEta parameters 4 source‖))^2) := by
  let mapping : CellL2 1 →L[ℝ] CellL2 1 :=
    (((length : ℂ)⁻¹) • ContinuousLinearMap.id ℂ (CellL2 1)).restrictScalars ℝ
  let project := (hilbertMeanFree parameters).restrictScalars ℝ
  obtain ⟨radial,radial0,radialEnergy⟩ := actualRadiusSource_jointEnergy parameters lower positive bounded
    total extra (grade+1) rank paid mapping
  obtain ⟨first,first0,firstEnergy⟩ := actualKappaPrimitive_jointEnergy parameters length compact lower
    positive bounded total extra (grade+1) rank paid 0 3
  obtain ⟨second,second0,secondEnergy⟩ := actualKappaPrimitive_jointEnergy parameters length compact lower
    positive bounded total extra (grade+1) rank paid 1 0
  obtain ⟨third,third0,thirdEnergy⟩ := actualKappaPrimitive_jointEnergy parameters length compact lower
    positive bounded total extra (grade+1) rank paid 2 2
  obtain ⟨primitiveConstant,primitive0,primitiveEnergy⟩ := actualPrimitive_jointTerminalEnergy parameters length lower
    positive bounded total extra (grade+1) rank paid
  let innerConstant := 2*(2*(2*(first+second)+third)+primitiveConstant 0)
  have inner0 : 0 ≤ innerConstant := by
    have last0 := primitive0 0
    dsimp only [innerConstant]
    positivity
  refine ⟨2*(radial+‖project‖*innerConstant),by positivity,?_⟩
  intro state unit source flat
  let weight := 1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+extra)
  let payment := ‖quotientEta parameters (4+total) source‖+
    (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+total))*
      ‖quotientEta parameters 4 source‖
  have payment0 : 0 ≤ payment := add_nonneg (norm_nonneg _)
    (mul_nonneg (add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)) (norm_nonneg _))
  let curves := actualKappaPrimitiveCurve parameters length compact lower positive bounded state source
  let last := actualCartesianPrimitiveCurve parameters length lower positive bounded source 0 (grade+1)
  let inner := fun point => ((curves 0 3 (grade+1) point+curves 1 0 (grade+1) point)-curves 2 2 (grade+1) point)-last point
  let radiusCurve := fun point => point • mapping
    (cartesianWeightedRadialCurve parameters lower positive bounded (source 2) (grade+1) 0 point)
  have smooth (component : Fin 3) (slot : Fin 4) : ContDiffOn ℝ rank (curves component slot (grade+1)) (Icc lower 1) :=
    contDiffOn_infty.mp (actualKappaPrimitiveCurve_smooth parameters length compact lower positive bounded state source component slot (grade+1)) rank
  have lastSmooth : ContDiffOn ℝ rank last (Icc lower 1) := contDiffOn_infty.mp
    ((actualCartesianPrimitiveRadialCurves parameters length lower positive bounded source 0).smooth (grade+1)) rank
  have innerSmooth : ContDiffOn ℝ rank inner (Icc lower 1) :=
    (((smooth 0 3).add (smooth 1 0)).sub (smooth 2 2)).sub lastSmooth
  have radiusSmooth : ContDiffOn ℝ rank radiusCurve (Icc lower 1) :=
    contDiffOn_id.smul (mapping.contDiff.comp_contDiffOn (contDiffOn_infty.mp
      (cartesianWeightedRadialCurve_smooth parameters lower positive bounded (source 2) (grade+1) 0) rank))
  have firstTwo := eulerCurve_squareEnergy_add lower bounded (curves 0 3 (grade+1)) (curves 1 0 (grade+1))
    rank (smooth 0 3) (smooth 1 0) weight (first*payment) (second*payment)
    (mul_nonneg first0 payment0) (mul_nonneg second0 payment0) (firstEnergy state unit source) (secondEnergy state unit source)
  have firstThree := eulerCurve_squareEnergy_sub lower bounded
    (fun point => curves 0 3 (grade+1) point+curves 1 0 (grade+1) point) (curves 2 2 (grade+1))
    rank ((smooth 0 3).add (smooth 1 0)) (smooth 2 2) weight (2*(first*payment+second*payment)) (third*payment)
    (by positivity) (mul_nonneg third0 payment0) firstTwo (thirdEnergy state unit source)
  have allFour := eulerCurve_squareEnergy_sub lower bounded
    (fun point => (curves 0 3 (grade+1) point+curves 1 0 (grade+1) point)-curves 2 2 (grade+1) point) last
    rank (((smooth 0 3).add (smooth 1 0)).sub (smooth 2 2)) lastSmooth weight
    (2*(2*(first*payment+second*payment)+third*payment)) (primitiveConstant 0*payment)
    (by positivity) (mul_nonneg (primitive0 0) payment0) firstThree
    (primitiveEnergy state.val.val.field state.val.val.rho state.val.val.epsilon unit source 0)
  have innerEnergy : (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank inner radius‖^2)) ≤
      ENNReal.ofReal ((innerConstant*payment)^2) :=
    allFour.trans_eq (by dsimp only [innerConstant]; congr 1; ring)
  have projected := eulerCurve_squareEnergy_observation lower bounded inner rank innerSmooth project weight
    (innerConstant*payment) innerEnergy
  have full := eulerCurve_squareEnergy_add lower bounded radiusCurve (fun point => project (inner point))
    rank radiusSmooth (project.contDiff.comp_contDiffOn innerSmooth) weight (radial*payment) (‖project‖*(innerConstant*payment))
    (mul_nonneg radial0 payment0) (by positivity)
    (radialEnergy state.val.val.field state.val.val.rho state.val.val.epsilon unit source 2) projected
  have same := eulerCurve_squareEnergy_congr lower
    (actualCartesianThirdCurve parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
      lower positive bounded source flat (grade+1))
    (fun point => radiusCurve point+project (inner point)) (by
      intro point inside
      rw [actualThirdCurve_expanded parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
        lower positive bounded grade source flat point inside]
      rfl) rank weight
  exact same.le.trans (full.trans_eq (by congr 1; ring))

end Grad.OriginalCartesianTameEstimate

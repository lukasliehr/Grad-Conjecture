import AKDN72BalancedSevenAssemblyEnergy
import AKDN66ActualNativeBalancedSourceEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.AnnularSmoothCore
open Grad.AnnularReconstruction Grad.AnnularGeneralSourceRegularity Grad.OriginalTerminalAllocation
open Grad.QuotientProjection Grad.GaugeCoefficients.Physical.Allocation Grad.ExhaustionSourceAllocation

/-- The complete literal known seven-slot packet, including its original
phase, has joint coefficient/Euler energy with the independent F4 base. -/
theorem actualKnownSeven_jointEulerEnergy (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0<lower) (bounded : lower<1) (total extra power rank : ℕ) (paid : extra+power+rank≤total) :
    ∃ constant : ℝ, 0≤constant ∧
    ∀ state : RetainedInverseState parameters length compact,
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10≤1 →
    ∀ source : SmoothQuotient parameters,
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+extra)) •
        vectorEulerWithinIteratedDerivative (Icc lower 1) rank
          (actualCartesianKnownSevenCurve parameters length lower positive bounded source power) radius‖^2)) ≤
      ENNReal.ofReal ((constant*(‖quotientEta parameters (4+total) source‖+
        (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+total))*‖quotientEta parameters 4 source‖))^2) := by
  obtain ⟨cost,cost0,bound⟩ := actualPrimitive_jointTerminalEnergy parameters length lower positive bounded total extra power rank paid
  let mapping := fun slot => (hilbertSlotInjection parameters slot).restrictScalars ℝ
  let price := fun (slot : Fin 7) (primitive : Fin 4) => ‖mapping slot‖*cost primitive
  have price0 (slot : Fin 7) (primitive : Fin 4) : 0≤price slot primitive := mul_nonneg (norm_nonneg _) (cost0 _)
  refine ⟨2*(2*(price 4 0+price 5 1)+price 6 2),
    mul_nonneg (by norm_num) (add_nonneg (mul_nonneg (by norm_num) (add_nonneg (price0 _ _) (price0 _ _))) (price0 _ _)),?_⟩
  intro state unit source
  let weight := 1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+extra)
  let payment := ‖quotientEta parameters (4+total) source‖+
    (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+total))*‖quotientEta parameters 4 source‖
  have payment0 : 0≤payment := add_nonneg (norm_nonneg _)
    (mul_nonneg (add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)) (norm_nonneg _))
  let primitive := fun slot => actualCartesianPrimitiveCurve parameters length lower positive bounded source slot power
  let injected := fun slot sourceSlot radius => mapping slot (primitive sourceSlot radius)
  have smooth (slot : Fin 4) : ContDiffOn ℝ rank (primitive slot) (Icc lower 1) :=
    contDiffOn_infty.mp ((actualCartesianPrimitiveRadialCurves parameters length lower positive bounded source slot).smooth power) rank
  have injectedSmooth (slot : Fin 7) (primitive : Fin 4) : ContDiffOn ℝ rank (injected slot primitive) (Icc lower 1) :=
    (mapping slot).contDiff.comp_contDiffOn (smooth primitive)
  have energy (slot : Fin 7) (primitiveSlot : Fin 4) :
      (∫⁻ radius in Icc lower 1, ENNReal.ofReal
        (‖weight • vectorEulerWithinIteratedDerivative (Icc lower 1) rank (injected slot primitiveSlot) radius‖^2)) ≤
        ENNReal.ofReal ((price slot primitiveSlot*payment)^2) := by
    have actual := eulerCurve_squareEnergy_observation lower bounded (primitive primitiveSlot) rank (smooth primitiveSlot)
      (mapping slot) weight (cost primitiveSlot*payment)
      (bound state.val.val.field state.val.val.rho state.val.val.epsilon unit source primitiveSlot)
    exact actual.trans_eq (by congr 1; ring)
  have first := eulerCurve_squareEnergy_add lower bounded (injected 4 0) (injected 5 1) rank
    (injectedSmooth 4 0) (injectedSmooth 5 1) weight (price 4 0*payment) (price 5 1*payment)
    (mul_nonneg (price0 _ _) payment0) (mul_nonneg (price0 _ _) payment0) (energy 4 0) (energy 5 1)
  have second := eulerCurve_squareEnergy_add lower bounded (fun point => injected 4 0 point+injected 5 1 point) (injected 6 2) rank
    ((injectedSmooth 4 0).add (injectedSmooth 5 1)) (injectedSmooth 6 2) weight
    (2*(price 4 0*payment+price 5 1*payment)) (price 6 2*payment)
    (mul_nonneg (by norm_num) (add_nonneg (mul_nonneg (price0 _ _) payment0) (mul_nonneg (price0 _ _) payment0)))
    (mul_nonneg (price0 _ _) payment0) first (energy 6 2)
  have same := eulerCurve_squareEnergy_congr lower
    (actualCartesianKnownSevenCurve parameters length lower positive bounded source power)
    (fun point => (injected 4 0 point+injected 5 1 point)+injected 6 2 point) (fun _ _ => rfl) rank weight
  exact same.le.trans (second.trans_eq (by congr 1; ring))

end Grad.OriginalCartesianTameEstimate

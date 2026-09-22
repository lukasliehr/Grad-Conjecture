import AKCK9BalancedSourceEnergyAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.SourceCollarFullSource Grad.AnnularGeneralSourceRegularity
open Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularStrongData Grad.AnnularSmoothCore
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation
open Grad.GaugeCoefficients.Physical.Allocation

/-- The literal balanced known source of the SAME original Cartesian datum,
at its original analytic width and over all cells, has high q+4 payment and
independent F4 payment. No high coefficient multiplies a high source norm. -/
theorem actualBalancedSource_fourEnergy (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (state : RetainedInverseState parameters length compact)
      (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 6 ≤
        originalCoefficientLowRadius parameters length),
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 ≤ 1 →
    ∀ (source : SmoothQuotient parameters) (flat : IsFlat source),
    let data := actualCartesianWeightedDatum parameters length state.val.val.rho state.val.val.epsilon
      state.val.val.field small lower positive bounded lengthPositive source flat
    let curves := actualCartesianSourceRadialCurves parameters length state.val.val.rho state.val.val.epsilon
      state.val.val.field small lower positive bounded lengthPositive source flat
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖balancedActualSource parameters length compact lower positive bounded state data curves grade
        (collarRadius lower positive bounded.le radius)‖^2)) ≤
      ENNReal.ofReal ((constant*(‖quotientEta parameters (grade+4) source‖+
        physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+11)*
          ‖quotientEta parameters 4 source‖))^2) := by
  obtain ⟨knownHigh,knownLow,knownHigh0,knownLow0,knownEnergy⟩ :=
    actualKnownSeven_fourEnergy parameters length lower positive bounded grade
  obtain ⟨primitive,primitive0,primitiveEnergy⟩ :=
    actualPrimitiveCurve_fourEnergy parameters length lower positive bounded grade
  obtain ⟨kernel,kernel0,kernelBound⟩ := balancedActualSource_oneOrder parameters length compact grade
  have gh0 := g3HighConstant_nonnegative parameters length grade
  have gl0 : 0 ≤ g3LowConstant parameters length grade := by
    have same := fullSourceLowConstant_nonnegative parameters length grade
    unfold fullSourceLowConstant at same
    linarith only [same]
  let thirdConstant := lower⁻¹*(g3HighConstant parameters length grade+g3LowConstant parameters length grade)
  have third0 : 0 ≤ thirdConstant := mul_nonneg (inv_nonneg.mpr positive.le) (add_nonneg gh0 gl0)
  have primitive30 := primitive0 3
  let total := knownHigh+knownLow+primitive 3+thirdConstant
  have total0 : 0 ≤ total := by dsimp only [total]; positivity
  refine ⟨4*kernel*total,by positivity,?_⟩
  intro state small unit source flat
  dsimp only
  let data := actualCartesianWeightedDatum parameters length state.val.val.rho state.val.val.epsilon
    state.val.val.field small lower positive bounded lengthPositive source flat
  let curves := actualCartesianSourceRadialCurves parameters length state.val.val.rho state.val.val.epsilon
    state.val.val.field small lower positive bounded lengthPositive source flat
  let B := physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+11)
  let A := ‖quotientEta parameters (grade+4) source‖
  let L := ‖quotientEta parameters 4 source‖
  let payment := A+B*L
  have B0 : 0 ≤ B := physicalBudget_nonnegative _ _ _ _ _
  have A0 : 0 ≤ A := norm_nonneg _
  have L0 : 0 ≤ L := norm_nonneg _
  have payment0 : 0 ≤ payment := add_nonneg A0 (mul_nonneg B0 L0)
  have actualThird := actualThirdCurve_fourEnergy parameters length state.val.val.rho state.val.val.epsilon
    state.val.val.field small lower positive bounded grade source flat
  have lowPay : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+6)*
      ‖quotientEta parameters 3 source‖ ≤ B*L :=
    mul_le_mul (physicalBudget_monotone _ _ _ _ (by omega))
      (originalSourceNorm_monotone parameters source (by omega : 3≤4)) (norm_nonneg _) B0
  have thirdPay : lower⁻¹*(g3HighConstant parameters length grade*A+
      g3LowConstant parameters length grade*
        physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+6)*
          ‖quotientEta parameters 3 source‖) ≤ thirdConstant*payment := by
    calc
      _ ≤ lower⁻¹*(g3HighConstant parameters length grade*A+
          g3LowConstant parameters length grade*(B*L)) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr positive.le)
        apply add_le_add le_rfl
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left lowPay gl0
      _ ≤ _ := by
        dsimp only [thirdConstant,payment]
        nlinarith only [mul_nonneg (mul_nonneg (inv_nonneg.mpr positive.le) gh0) (mul_nonneg B0 L0),
          mul_nonneg (mul_nonneg (inv_nonneg.mpr positive.le) gl0) A0]
  have thirdEnergy : (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖curves.third (grade+1) radius‖^2)) ≤
      ENNReal.ofReal ((thirdConstant*payment)^2) := by
    apply actualThird.trans
    apply ENNReal.ofReal_le_ofReal
    apply (sq_le_sq₀ ?_ (mul_nonneg third0 payment0)).mpr thirdPay
    exact mul_nonneg (inv_nonneg.mpr positive.le) (add_nonneg (mul_nonneg gh0 A0)
      (mul_nonneg (mul_nonneg gl0 (physicalBudget_nonnegative _ _ _ _ _)) (norm_nonneg _)))
  have pointwise : ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      ‖balancedActualSource parameters length compact lower positive bounded state data curves grade
        (collarRadius lower positive bounded.le radius)‖ ≤
      kernel*(‖curves.seven (grade+1) radius‖+B*‖curves.seven 0 radius‖+
        ‖curves.force (grade+1) radius‖+‖curves.third (grade+1) radius‖) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
    have literal := collarRadius_literal lower positive bounded.le radius inside
    have bound := kernelBound lower positive bounded state unit data curves
      (collarRadius lower positive bounded.le radius) (by rw [literal]; exact inside)
    simpa only [literal,B] using bound
  have assembled := fourInput_squareEnergy (volume.restrict (Icc lower 1))
    (fun radius => balancedActualSource parameters length compact lower positive bounded state data curves grade
      (collarRadius lower positive bounded.le radius))
    (curves.seven (grade+1)) (curves.seven 0) (curves.force (grade+1)) (curves.third (grade+1))
    ((curves.sevenSmooth _).continuousOn.aestronglyMeasurable measurableSet_Icc)
    ((curves.sevenSmooth _).continuousOn.aestronglyMeasurable measurableSet_Icc)
    ((curves.forceSmooth _).continuousOn.aestronglyMeasurable measurableSet_Icc)
    ((curves.thirdSmooth _).continuousOn.aestronglyMeasurable measurableSet_Icc)
    kernel B (knownHigh*A) (knownLow*L) (primitive 3*A) (thirdConstant*payment)
    kernel0 B0 (mul_nonneg knownHigh0 A0) (mul_nonneg knownLow0 L0)
    (mul_nonneg (primitive0 3) A0) (mul_nonneg third0 payment0) pointwise
    (knownEnergy source).1 (knownEnergy source).2 (primitiveEnergy source 3) thirdEnergy
  apply assembled.trans
  apply ENNReal.ofReal_le_ofReal
  apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
  have combined : knownHigh*A+B*(knownLow*L)+primitive 3*A+thirdConstant*payment ≤ total*payment := by
    dsimp only [total,payment]
    nlinarith only [mul_nonneg knownHigh0 (mul_nonneg B0 L0),mul_nonneg knownLow0 A0,
      mul_nonneg (primitive0 3) (mul_nonneg B0 L0)]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left combined (mul_nonneg (by norm_num : (0:ℝ)≤4) kernel0)

end Grad.OriginalCartesianTameEstimate

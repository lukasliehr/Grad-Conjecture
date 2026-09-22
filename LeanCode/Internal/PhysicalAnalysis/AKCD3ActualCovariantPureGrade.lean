import AKCD2SameNativeBalancedAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.AnnularKernelL2
open Grad.ActualSmoothPhysicalField Grad.ActualNativeCellMoments Grad.AnnularWeightedSmoothness
open Grad.GaugeCoefficients.Physical.Allocation

theorem smoothCurve_base_le_grade {dimension : ℕ} {parameters : PhaseParameters}
    {lower : ℝ} {positive : 0 < lower} {row : DivisionRow dimension lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower < 1)
    (grade : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    ‖curves.curve 0 radius‖ ≤ ‖curves.curve grade radius‖ := by
  have same : ∀ mode, curves.curve grade radius mode = (annularFrequency mode.1 mode.2 : ℂ)^grade • curves.curve 0 radius mode := by
    intro mode
    simpa only [Nat.zero_add] using curves.shift bounded 0 grade radius inside mode
  rw [← hilbertReserve_same parameters dimension grade _ _ same]
  exact ((hilbertReserve parameters dimension grade).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (hilbertReserve_norm_le parameters dimension grade) (norm_nonneg _)).trans_eq (one_mul _))

/-- The SAME actual normalized covariant reconstruction has complementary
native grades. The constant precedes the state, collar, curve and radius. -/
theorem actualCovariantCurve_oneHigh (parameters : PhaseParameters) (length compact : ℝ) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (state : AnnularReconstructionState parameters length compact),
    physicalBudget parameters state.val.field state.val.rho state.val.epsilon 12 ≤ 1 →
    ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
      (row : DivisionRow 7 lower) (curves : SmoothLowPhysicalRow parameters lower positive row)
      (radius : ℝ), radius ∈ Icc lower 1 →
      ‖(curves.covariant parameters length compact lower positive bounded state).cartesianCovariant.curve grade radius‖ ≤
        constant * (‖curves.curve grade radius‖ +
          physicalBudget parameters state.val.field state.val.rho state.val.epsilon (grade+12) * ‖curves.curve 0 radius‖) := by
  let first := normalizedCovariantConstant parameters length compact 0
  let second := normalizedCovariantConstant parameters length compact grade
  have firstNonnegative : 0 ≤ first := normalizedCovariantConstant_nonnegative parameters length compact 0
  have secondNonnegative : 0 ≤ second := normalizedCovariantConstant_nonnegative parameters length compact grade
  refine ⟨‖nativeCovariantRotation parameters grade‖ * (2^grade*(2*first+second)), by positivity, ?_⟩
  intro state small lower positive bounded row curves radius inside
  let point := collarRadius lower positive bounded.le radius
  let kernel := radialNormalizedCovariantKernel parameters length compact state.val point state.property
  have same : ∀ mode, curves.curve grade radius mode = (annularFrequency mode.1 mode.2 : ℂ)^grade • curves.curve 0 radius mode := by
    intro mode
    simpa only [Nat.zero_add] using curves.shift bounded 0 grade radius inside mode
  have actual := nativeBalancedAction_bound parameters grade point kernel (curves.curve grade radius) (curves.curve 0 radius) same
  have firstBound := (Classical.choose_spec (radialNormalizedCovariantKernel_physicalMoments parameters length compact 0)).2 state point
  have secondBound := (Classical.choose_spec (radialNormalizedCovariantKernel_physicalMoments parameters length compact grade)).2 state point
  change fullKernelMoment (radialKernelParameters parameters point) 0 kernel ≤ first *
    (1+physicalBudget parameters state.val.field state.val.rho state.val.epsilon 7) at firstBound
  change fullKernelMoment (radialKernelParameters parameters point) grade kernel ≤ second *
    (1+physicalBudget parameters state.val.field state.val.rho state.val.epsilon (grade+7)) at secondBound
  have lowBudget := (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon (by norm_num : 7≤12)).trans small
  have highBudget := physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon (by omega : grade+7≤grade+12)
  have low : fullKernelMoment (radialKernelParameters parameters point) 0 kernel ≤ 2*first :=
    firstBound.trans (by nlinarith only [lowBudget, firstNonnegative])
  have high : fullKernelMoment (radialKernelParameters parameters point) grade kernel ≤
      second * (1+physicalBudget parameters state.val.field state.val.rho state.val.epsilon (grade+12)) :=
    secondBound.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) highBudget) secondNonnegative)
  have baseLe := smoothCurve_base_le_grade curves bounded grade radius inside
  have highNonnegative := physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon (grade+12)
  have total : ‖bulkKernelAction parameters grade point kernel (curves.curve grade radius)‖ ≤
      (2^grade*(2*first+second)) * (‖curves.curve grade radius‖ +
        physicalBudget parameters state.val.field state.val.rho state.val.epsilon (grade+12) * ‖curves.curve 0 radius‖) := by
    apply actual.trans
    have one := add_le_add (mul_le_mul_of_nonneg_right low (norm_nonneg (curves.curve grade radius)))
      (mul_le_mul_of_nonneg_right high (norm_nonneg (curves.curve 0 radius)))
    apply (mul_le_mul_of_nonneg_left one (by positivity : 0≤(2:ℝ)^grade)).trans
    rw [mul_assoc ((2:ℝ)^grade) (2*first+second)]
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0≤(2:ℝ)^grade)
    have reserve := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) firstNonnegative) (mul_nonneg highNonnegative (norm_nonneg (curves.curve 0 radius)))
    nlinarith [mul_le_mul_of_nonneg_left baseLe secondNonnegative]
  rw [nativeCovariantRotation_same]
  apply ((nativeCovariantRotation parameters grade).le_opNorm _).trans
  have exactCurve : (curves.covariant parameters length compact lower positive bounded state).curve grade radius =
      bulkKernelAction parameters grade point kernel (curves.curve grade radius) := by
    change conjugatedKernelAction parameters grade 0 point kernel _ = _
    apply conjugatedKernelAction_same
    intro mode
    simp only [pow_zero,one_smul]
  rw [exactCurve]
  exact (mul_le_mul_of_nonneg_left total (norm_nonneg _)).trans_eq (by ring)

end Grad.OriginalCartesianTameEstimate

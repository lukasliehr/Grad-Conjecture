import AKCK7ActualBalancedKnownFlux

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.AnnularKernelL2
open Grad.AnnularSmoothCore Grad.AnnularWeightedSystem Grad.BoundaryLift Grad.AnnularCurrentLow
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularGeneralSourceRegularity
open Grad.AnnularStrongData Grad.AnnularWeightedSmoothness

/-- The literal known-source contribution to SR15 in its balanced order.
The input is the already realized original datum; RF0 is its stored angular
source, and the third curve is the same rG3, with the positive R sign. -/
def balancedActualSource (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (curves : ActualSourceRadialCurves parameters lower positive bounded data)
    (grade : ℕ) (radius : RadialPoint) : PhysicalHilbertPair :=
  let row := fun index : Fin 3 => bulkKernelAction parameters (grade+1) radius
    (lowPhysicalRowKernel parameters length compact state index radius) (curves.seven (grade+1) radius)
  balancedFluxOutput parameters length radius (row 0,(row 1,row 2)) +
    (hilbertMeanFree parameters (curves.force (grade+1) radius),
      hilbertFrequencyOperator parameters 1 (some false) (curves.third (grade+1) radius))

/-- Exact same-cell source signs and projections. The DΦ−1 term stays in
the separately checked homogeneous balanced operator CI6. -/
theorem balancedActualSource_coefficient (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (curves : ActualSourceRadialCurves parameters lower positive bounded data)
    (grade : ℕ) (radius : RadialPoint) (mode : ℤ × ℤ) :
    let row := fun index : Fin 3 => bulkKernelAction parameters (grade+1) radius
      (lowPhysicalRowKernel parameters length compact state index radius) (curves.seven (grade+1) radius)
    hilbertPairCoefficient mode (balancedActualSource parameters length compact lower positive bounded state data curves grade radius) =
      ((if mode.1=0 then (0 : ℂ) else 1) • (row 0 mode+curves.force (grade+1) radius mode),
        -((radius.val : ℂ)*(length : ℂ)⁻¹) • (frequencyRatioSymbol (some true) mode • row 1 mode) -
          frequencyRatioSymbol (some false) mode • row 2 mode +
          frequencyRatioSymbol (some false) mode • curves.third (grade+1) radius mode) := by
  dsimp only [balancedActualSource]
  rw [balancedFluxOutput_actual]
  apply Prod.ext
  · change (if mode.1=0 then (0 : ℂ) else 1) • (_ : ComplexEuclidean 1) +
      (if mode.1=0 then (0 : ℂ) else 1) • (_ : ComplexEuclidean 1) = _
    rw [smul_add]
    rfl
  · rfl

/-- Sharp actual known-source kernel estimate before inserting source norm
payments. Only the SAME grade-zero known packet multiplies high coefficients. -/
theorem balancedActualSource_oneOrder (parameters : PhaseParameters) (length compact : ℝ)
    (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
      (state : RetainedInverseState parameters length compact),
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 ≤ 1 →
    ∀ (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
      (curves : ActualSourceRadialCurves parameters lower positive bounded data)
      (radius : RadialPoint), radius.val ∈ Icc lower 1 →
    ‖balancedActualSource parameters length compact lower positive bounded state data curves grade radius‖ ≤
      constant * (‖curves.seven (grade+1) radius‖ +
        physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+11) * ‖curves.seven 0 radius‖ +
        ‖curves.force (grade+1) radius‖ + ‖curves.third (grade+1) radius‖) := by
  obtain ⟨kernelConstant,kernelNonnegative,kernelBound⟩ := actualBalancedKnownFlux_oneOrder parameters length compact grade
  let mean := hilbertMeanFree parameters
  let angular := hilbertFrequencyOperator parameters 1 (some false)
  refine ⟨kernelConstant+‖mean‖+‖angular‖,by positivity,?_⟩
  intro lower positive bounded state small data curves radius inside
  have same := actualWeightedCurve_shift lower bounded curves.seven
    (fun q => (curves.sevenSmooth q).continuousOn) _ curves.sevenSame 0 (grade+1) radius inside
  have flux := kernelBound state small radius (curves.seven (grade+1) radius) (curves.seven 0 radius)
    (by simpa only [Nat.zero_add] using same)
  have force := mean.le_opNorm (curves.force (grade+1) radius)
  have third := angular.le_opNorm (curves.third (grade+1) radius)
  have pairBound : ‖(mean (curves.force (grade+1) radius),angular (curves.third (grade+1) radius))‖ ≤
      ‖mean‖*‖curves.force (grade+1) radius‖+‖angular‖*‖curves.third (grade+1) radius‖ := by
    rw [Prod.norm_def]
    exact max_le (force.trans (le_add_of_nonneg_right (by positivity)))
      (third.trans (le_add_of_nonneg_left (by positivity)))
  apply ((norm_add_le _ _).trans (add_le_add flux pairBound)).trans
  have knownNonnegative : 0 ≤ ‖curves.seven (grade+1) radius‖ +
      physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+11)*‖curves.seven 0 radius‖ :=
    add_nonneg (norm_nonneg _) (mul_nonneg (physicalBudget_nonnegative _ _ _ _ _) (norm_nonneg _))
  nlinarith [mul_nonneg kernelNonnegative (norm_nonneg (curves.force (grade+1) radius)),
    mul_nonneg kernelNonnegative (norm_nonneg (curves.third (grade+1) radius)),
    mul_nonneg (norm_nonneg mean) knownNonnegative,
    mul_nonneg (norm_nonneg angular) knownNonnegative,
    mul_nonneg (norm_nonneg mean) (norm_nonneg (curves.third (grade+1) radius)),
    mul_nonneg (norm_nonneg angular) (norm_nonneg (curves.force (grade+1) radius))]

end Grad.OriginalCartesianTameEstimate

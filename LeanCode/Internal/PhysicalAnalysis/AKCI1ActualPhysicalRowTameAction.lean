import AKCD3ActualCovariantPureGrade
import AJD28ActualCoefficientCoordinateBounds

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

open Grad.AnnularCurrentLow Grad.AnnularCrossOrbit

/-- Exact original pre-projection physical rows, including the literal P in
rV. Distribute the output moment between the SAME high and base inputs before
using the actual reconstruction moment bounds. -/
theorem actualPhysicalRow_oneHigh (parameters : PhaseParameters) (length compact : ℝ)
    (row : Fin 3) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (state : RetainedInverseState parameters length compact),
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 ≤ 1 →
    ∀ (radius : RadialPoint) (high low : CellL2 7),
    (∀ mode, high mode = (annularFrequency mode.1 mode.2 : ℂ)^grade • low mode) →
    ‖bulkKernelAction parameters grade radius (lowPhysicalRowKernel parameters length compact state row radius) high‖ ≤
      constant * (‖high‖ +
        physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+10) * ‖low‖) := by
  obtain ⟨first,firstNonnegative,firstBound⟩ := lowPhysicalRowKernel_allMoments parameters length compact row 0
  obtain ⟨second,secondNonnegative,secondBound⟩ := lowPhysicalRowKernel_allMoments parameters length compact row grade
  refine ⟨2^grade*(2*first+second), by positivity, ?_⟩
  intro state small radius high low same
  let kernel := lowPhysicalRowKernel parameters length compact state row radius
  have actual := nativeBalancedAction_bound parameters grade radius kernel high low same
  have firstMoment := firstBound state radius
  have secondMoment := secondBound state radius
  change fullKernelMoment (radialKernelParameters parameters radius) 0 kernel ≤ first *
    (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 7) at firstMoment
  change fullKernelMoment (radialKernelParameters parameters radius) grade kernel ≤ second *
    (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+7)) at secondMoment
  have lowBudget := (physicalBudget_monotone parameters state.val.val.field state.val.val.rho state.val.val.epsilon (by norm_num : 7≤10)).trans small
  have highBudget := physicalBudget_monotone parameters state.val.val.field state.val.val.rho state.val.val.epsilon (by omega : grade+7≤grade+10)
  have lowMoment : fullKernelMoment (radialKernelParameters parameters radius) 0 kernel ≤ 2*first :=
    firstMoment.trans (by nlinarith only [lowBudget,firstNonnegative])
  have highMoment : fullKernelMoment (radialKernelParameters parameters radius) grade kernel ≤
      second * (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+10)) :=
    secondMoment.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) highBudget) secondNonnegative)
  have baseLe : ‖low‖ ≤ ‖high‖ := by
    rw [← hilbertReserve_same parameters 7 grade high low same]
    exact ((hilbertReserve parameters 7 grade).le_opNorm high).trans
      ((mul_le_mul_of_nonneg_right (hilbertReserve_norm_le parameters 7 grade) (norm_nonneg high)).trans_eq (one_mul _))
  have highNonnegative := physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+10)
  apply actual.trans
  have one := add_le_add (mul_le_mul_of_nonneg_right lowMoment (norm_nonneg high))
    (mul_le_mul_of_nonneg_right highMoment (norm_nonneg low))
  apply (mul_le_mul_of_nonneg_left one (by positivity : 0≤(2:ℝ)^grade)).trans
  rw [mul_assoc ((2:ℝ)^grade) (2*first+second)]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0≤(2:ℝ)^grade)
  have reserve := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) firstNonnegative)
    (mul_nonneg highNonnegative (norm_nonneg low))
  nlinarith [mul_le_mul_of_nonneg_left baseLe secondNonnegative]

end Grad.OriginalCartesianTameEstimate

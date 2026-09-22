import AKF10FullReservedWeightedSystem

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularWeightedSystem
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit
open Grad.AnnularSmoothCore Grad.PhaseAlgebra Grad.AnnularCurrentLow
open Grad.AnnularWeightedSmoothness Grad.AnnularWeightedSmoothCore Grad.AnnularSmoothSources
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact) (core : OriginalSmoothSourceCore parameters)

/-- The actual kernel's finite-order regularity discharges the saved finite
source consumer at every grade, with the original width and source unchanged. -/
theorem conjugatedSource_smooth_of_kernelOrders (grade : ℕ)
    (regularity : ∀ (index : Fin 3) (order : ℕ), ∃ reserve : ℕ,
      ContDiffOn ℝ order (radialConjugatedAction parameters lower positive (lowerHalf.trans (by norm_num))
        (lowPhysicalRowKernel parameters length compact state index) (grade + 1) reserve) (Icc lower 1)) :
    ContDiffOn ℝ ∞
      (conjugatedRadialSystemSource parameters length compact lower positive
        (lowerHalf.trans_lt (by norm_num)) lengthPositive state core grade) (Icc lower 1) := by
  apply conjugatedRadialSystemSource_smooth_of_rows
  intro index
  exact finiteConjugatedKernelCurve_smooth
    (smoothStrongSevenRow parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive core)
    parameters positive (lowerHalf.trans (by norm_num))
    (lowPhysicalRowKernel parameters length compact state index) (grade + 1) (regularity index)

theorem fullWeightedSystemSource_smooth_of_kernelOrders (grade : ℕ)
    (regularity : ∀ (index : Fin 3) (order : ℕ), ∃ reserve : ℕ,
      ContDiffOn ℝ order (radialConjugatedAction parameters lower positive (lowerHalf.trans (by norm_num))
        (lowPhysicalRowKernel parameters length compact state index) (grade + 1) reserve) (Icc lower 1)) :
    ContDiffOn ℝ ∞
      (fullWeightedSystemSource parameters length compact lower positive lowerHalf lengthPositive state core grade)
      (Icc lower 1) :=
  ((physicalPairMeanFree parameters).restrictScalars ℝ).contDiff.comp_contDiffOn
    (conjugatedSource_smooth_of_kernelOrders parameters length compact lower positive lowerHalf lengthPositive state core grade regularity)

variable (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)

/-- A single reserved continuous realization supplies continuity of the
SAME unreserved output field; equality is pointwise on the closed collar. -/
theorem conjugatedMeanFreeSystemRHS_continuous_of_reserve (grade reserve : ℕ)
    (rowsContinuous : ∀ index : Fin 3, ContDiffOn ℝ (0 : ℕ)
      (radialConjugatedAction parameters lower positive (lowerHalf.trans (by norm_num))
        (lowPhysicalRowKernel parameters length compact state index) (grade + 1) reserve) (Icc lower 1))
    (sourceContinuous : ContinuousOn
      (conjugatedRadialSystemSource parameters length compact lower positive
        (lowerHalf.trans_lt (by norm_num)) lengthPositive state core grade) (Icc lower 1)) :
    ContinuousOn (conjugatedMeanFreeSystemRHS parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core grade) (Icc lower 1) := by
  have homogeneous := (reservedConjugatedRadialSystemOperator_smooth parameters length compact lower state positive
    (lowerHalf.trans_lt (by norm_num)) grade reserve 0 rowsContinuous).continuousOn.clm_apply
      (conjugatedSmoothResponsePairCurve_continuous parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core (grade + 2 + reserve)).continuousOn
  have combined := (physicalPairMeanFree parameters).continuous.comp_continuousOn (homogeneous.add sourceContinuous)
  apply combined.congr
  intro radius inside
  change physicalPairMeanFree parameters _ = physicalPairMeanFree parameters _
  dsimp only [Pi.add_apply]
  rw [reservedConjugatedRadialSystemOperator_same,
    conjugatedSmoothResponsePairCurve_reserve parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core (grade + 2) reserve radius inside]

end Grad.AnnularWeightedSystem

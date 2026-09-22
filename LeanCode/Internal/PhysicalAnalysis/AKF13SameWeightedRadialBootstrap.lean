import AKF12CommonFiniteInputReserve

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularWeightedSystem
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.PhaseAlgebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularHighGenerators Grad.AnnularCurrentLow Grad.AnnularStrongSolution
open Grad.AnnularWeightedSmoothness Grad.AnnularKernelL2

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)

/-- All finite radial orders of the actual three kernel rows suffice for
full weighted radial C∞ of the SAME inverse at every original Fourier grade.
The kernel regularity provider is explicit until its actual theorem is applied. -/
theorem conjugatedSmoothResponse_smooth_of_kernelOrders
    (regularity : ∀ (index : Fin 3) (grade order : ℕ), ∃ reserve : ℕ,
      ContDiffOn ℝ order (radialConjugatedAction parameters lower positive (lowerHalf.trans (by norm_num))
        (lowPhysicalRowKernel parameters length compact state index) grade reserve) (Icc lower 1)) :
    ∀ grade, ContDiffOn ℝ ∞
      (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core grade) (Icc lower 1) := by
  classical
  have common (order grade : ℕ) := originalRows_commonReserve parameters length compact lower positive
    (lowerHalf.trans (by norm_num)) state (grade + 1) order (order + 3)
      (fun index => regularity index (grade + 1) order)
  choose reserve enough rowsSmooth using common
  have sourceSmooth (grade : ℕ) := fullWeightedSystemSource_smooth_of_kernelOrders parameters length compact lower
    positive lowerHalf lengthPositive state core grade (fun index order => regularity index (grade + 1) order)
  have rhsContinuous (grade : ℕ) : ContinuousOn
      (conjugatedMeanFreeSystemRHS parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core grade) (Icc lower 1) :=
    conjugatedMeanFreeSystemRHS_continuous_of_reserve parameters length compact lower positive lowerHalf lengthPositive
      state core widthHalf widthLength small grade (reserve 0 grade) (rowsSmooth 0 grade)
      (conjugatedSource_smooth_of_kernelOrders parameters length compact lower positive lowerHalf lengthPositive
        state core grade (fun index order => regularity index (grade + 1) order)).continuousOn
  apply finiteReservePairScale_smooth lower (lowerHalf.trans_lt (by norm_num))
    (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core)
    (fullWeightedSystemSource parameters length compact lower positive lowerHalf lengthPositive state core)
    (fun order grade => grade + 2 + reserve order grade)
    (fun order grade => fullReservedWeightedSystemOperator parameters length compact lower positive lowerHalf state
      grade (reserve order grade))
  · exact fun grade => (conjugatedSmoothResponsePairCurve_continuous parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core grade).continuousOn
  · exact sourceSmooth
  · intro order grade
    exact fullReservedWeightedSystemOperator_smooth parameters length compact lower positive lowerHalf state
      grade (reserve order grade) order (by have h := enough order grade; omega) (rowsSmooth order grade)
  · intro order grade mode radius inside
    have derivative := conjugatedCoordinateDerivative_of_continuousRHS parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core grade (rhsContinuous grade) mode radius inside
    rw [← fullReservedWeightedSystemOperator_same parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core grade (reserve order grade)
      (by have h := enough order grade; omega) radius inside mode] at derivative
    exact derivative.fst
  · intro order grade mode radius inside
    have derivative := conjugatedCoordinateDerivative_of_continuousRHS parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core grade (rhsContinuous grade) mode radius inside
    rw [← fullReservedWeightedSystemOperator_same parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core grade (reserve order grade)
      (by have h := enough order grade; omega) radius inside mode] at derivative
    exact derivative.snd

end Grad.AnnularWeightedSystem

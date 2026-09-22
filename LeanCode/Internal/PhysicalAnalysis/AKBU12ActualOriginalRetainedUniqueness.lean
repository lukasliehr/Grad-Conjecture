import AKBU11OriginalHomogeneousRetainedEstimate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Set Filter
open scoped Topology
namespace Grad.OriginalPhysicalKernelUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularIncomingIntegrability Grad.AnnularWeightedUniqueness
open Grad.OriginalKernelGraphRestriction Grad.OriginalKernelCovariantRecovery Grad.OriginalKernelOuterUniqueness
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.NonlinearQuotientBounds Grad.FinitePhysicalJetLift Grad.PhysicalCoordinates Grad.Constraints Grad.Cor18
open Grad.AnnularWeakExhaustion Grad.AnnularExhaustionEstimate Grad.ActualAnnularExhaustion Grad.AnnularRestriction

variable (parameters : PhaseParameters) (compact : ℝ) (lengthPositive : 0<parameters.length)
    (widthHalf : parameters.gamma≤1/2) (widthLength : parameters.gamma≤Real.sqrt 5/(6*parameters.length))
    (state : RetainedInverseState parameters parameters.length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8≤originalCoefficientLowRadius parameters parameters.length)
    (primitiveSmall : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8≤coupledPrimitiveRadius parameters parameters.length compact)
    (insideSeed : originalCoefficientSeed parameters compact state.val.val∈Seed.parameterDomain)
    (physicalState : QuotientState parameters)
    (sameBase : physicalState.2.1=planarReferenceCore parameters+state.val.val.field)
    (sameEpsilon : physicalState.1=(state.val.val.epsilon:ℂ))
    (vector : ACore parameters 3) (scalar : ACore parameters 1)
    (constrained : VectorConstraints parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed (toPhysicalCore parameters vector))
    (homogeneous : quotientRowsDerivative parameters parameters.length 1 physicalState ![(0,vector,scalar)]=0)

include widthHalf widthLength primitiveSmall insideSeed sameBase sameEpsilon constrained homogeneous

/-- The actual retained graph of every original constrained homogeneous
smooth Cartesian pair is zero on every admissible collar. -/
theorem originalPhysicalRetained_eq_zero (upper : ℝ) (positiveUpper : 0<upper)
    (domainUpper : upper≤min (1/2) parameters.length) :
    originalWeightedRetainedObservation parameters upper parameters.length positiveUpper
      ((domainUpper.trans (min_le_left _ _)).trans (by norm_num)) lengthPositive
      (originalPhysicalKernelGraphPoint parameters parameters.length compact upper positiveUpper domainUpper lengthPositive state small physicalState.2.1 vector scalar)=0 := by
  let field := originalWeightedRetainedObservation parameters upper parameters.length positiveUpper
    ((domainUpper.trans (min_le_left _ _)).trans (by norm_num)) lengthPositive
    (originalPhysicalKernelGraphPoint parameters parameters.length compact upper positiveUpper domainUpper lengthPositive state small physicalState.2.1 vector scalar)
  let coefficient := (2*Grad.AnnularFullSource.independentCoupledDataConstant parameters parameters.length compact)*
    (originalIncomingDecayConstant parameters parameters.length*‖GradeCore.ofCoreLinear (grade:=4) vector‖)
  let radii : ℕ→ℝ := fun index => upper*(1/((index:ℝ)+1))
  have positive (index : ℕ) : 0<radii index := mul_pos positiveUpper (by positivity)
  have included (index : ℕ) : radii index≤upper := by
    apply mul_le_of_le_one_right positiveUpper.le
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) index])
  have estimate (index : ℕ) : ‖field‖≤coefficient*(radii index)^(1/4:ℝ) := by
    have bound := originalPhysicalFixedRetained_bound parameters compact lengthPositive widthHalf widthLength state small primitiveSmall insideSeed
      physicalState sameBase sameEpsilon vector scalar constrained homogeneous upper positiveUpper domainUpper (radii index) (positive index) (included index)
    convert bound using 1
    dsimp only [coefficient]
    ring
  have toZero : Tendsto radii atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
  have powered : Tendsto (fun index => radii index^(1/4:ℝ)) atTop (𝓝 0) := by
    simpa only [Real.zero_rpow (by norm_num : (1/4:ℝ)≠0)] using toZero.rpow_const (Or.inr (by norm_num : (0:ℝ)≤1/4))
  have comparison : Tendsto (fun index => ‖field‖-coefficient*(radii index)^(1/4:ℝ)) atTop (𝓝 ‖field‖) := by
    simpa only [mul_zero,sub_zero] using tendsto_const_nhds.sub (tendsto_const_nhds.mul powered)
  have zero := le_of_tendsto comparison (Filter.Eventually.of_forall (fun index => sub_nonpos.mpr (estimate index)))
  exact norm_eq_zero.mp (le_antisymm zero (norm_nonneg field))

end Grad.OriginalPhysicalKernelUniqueness

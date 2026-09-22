import AKBU9OriginalFullIncomingNormPayment

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set
namespace Grad.OriginalPhysicalKernelUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.AnnularLowEnergy Grad.AnnularCoupledInverse
open Grad.AnnularVariational Grad.AnnularCrossMaps Grad.AnnularFluxTrace Grad.PhaseAlgebra
open Grad.OriginalKernelRetainedDecay Grad.AnnularCurrentLow Grad.AnnularIncomingIntegrability
open Grad.OriginalKernelGraphRestriction Grad.AnnularWeakExhaustion Grad.AnnularFullGraph Grad.AnnularOriginalCoreRealization
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.Constraints Grad.NonlinearQuotientBounds Grad.FinitePhysicalJetLift

def originalIncomingDecayConstant (parameters : PhaseParameters) (length : ℝ) : ℝ :=
  4*originalScalarDecayConstant parameters length+
  (lowBalanceConstant length parameters.gamma+2)*(1+length⁻¹)*originalScalarDecayConstant parameters length+
  originalFluxDecayConstant parameters length

/-- The incoming trace of the SAME original physical graph tends to zero
as r^(1/4), paid by the original A4 norm at unchanged analytic width. -/
theorem originalPhysicalIncoming_decay
    (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0<lower)
    (domain : lower≤min (1/2) length) (lengthPositive : 0<length)
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8≤originalCoefficientLowRadius parameters length)
    (physicalState : QuotientState parameters)
    (sameBase : physicalState.2.1=planarReferenceCore parameters+state.val.val.field)
    (vector : GradeCore parameters 3 4) (flat : ∀ cell,ZeroCartesianFirstJets (vector.toCore.val cell))
    (scalar : ACore parameters 1)
    (homogeneous : quotientRowsDerivative parameters length 1 physicalState ![(0,vector.toCore,scalar)]=0) :
    ‖coupledIncomingTrace lower length positive ((domain.trans (min_le_left _ _)).trans_lt (by norm_num)) lengthPositive
      (originalWeightedRetainedObservation parameters lower length positive ((domain.trans (min_le_left _ _)).trans (by norm_num)) lengthPositive
        (originalPhysicalKernelGraphPoint parameters length compact lower positive domain lengthPositive state small physicalState.2.1 vector.toCore scalar))‖≤
      originalIncomingDecayConstant parameters length*lower^(1/4:ℝ)*‖vector‖ := by
  let bounded : lower<1 := (domain.trans (min_le_left _ _)).trans_lt (by norm_num)
  let radius : RadialPoint := ⟨lower,positive.le,bounded.le⟩
  let xi := originalCoreCircleTrace parameters (originalKernelXi physicalState.2.1 vector.toCore scalar) radius
  let rotated := originalCoreCircleTrace parameters (rotationCore parameters (originalKernelXi physicalState.2.1 vector.toCore scalar)) radius
  let x := originalKernelPhysicalX parameters length state.val.val.rho state.val.val.epsilon state.val.val.field small radius physicalState.2.1 vector.toCore scalar
  have paid := originalFullIncoming_norm_bound parameters lower length positive bounded lengthPositive
    (originalWeightedRetainedObservation parameters lower length positive bounded.le lengthPositive
      (originalPhysicalKernelGraphPoint parameters length compact lower positive domain lengthPositive state small physicalState.2.1 vector.toCore scalar))
    xi rotated x
    (originalPhysicalKernelGraphPoint_Xi parameters length compact lower positive domain lengthPositive state small physicalState.2.1 vector.toCore scalar ⟨lower,le_rfl,bounded.le⟩)
    (originalPhysicalKernelGraphPoint_X parameters length compact lower positive domain lengthPositive state small physicalState.2.1 vector.toCore scalar ⟨lower,le_rfl,bounded.le⟩)
    (originalCoreCircleTrace_rotation parameters (originalKernelXi physicalState.2.1 vector.toCore scalar) radius)
  have scalars := originalKernelXi_scalar_decay parameters length state.val.val.rho state.val.val.epsilon state.val.val.field small
    physicalState sameBase vector flat scalar homogeneous radius
  have flux := originalKernelPhysicalX_decay parameters length state.val.val.rho state.val.val.epsilon state.val.val.field small
    physicalState sameBase vector flat scalar homogeneous radius positive
  have lowFactor : 0≤(lowBalanceConstant length parameters.gamma+2)*(1+length⁻¹)*lower^(-(9/4:ℝ)) := by
    unfold lowBalanceConstant
    positivity
  have estimate := paid.trans (add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add scalars.1 scalars.2) (by positivity : 0≤2*lower^(-(9/4:ℝ))))
    (add_le_add (mul_le_mul_of_nonneg_left scalars.1 lowFactor)
      (mul_le_mul_of_nonneg_left flux (Real.rpow_nonneg positive.le _))))
  have scalarPower : lower^(-(9/4:ℝ))*lower^(5/2:ℝ)=lower^(1/4:ℝ) := by rw [←Real.rpow_add positive]; norm_num
  have fluxPower : lower^(-(5/4:ℝ))*lower^(3/2:ℝ)=lower^(1/4:ℝ) := by rw [←Real.rpow_add positive]; norm_num
  apply estimate.trans_eq
  dsimp only [radius]
  unfold originalIncomingDecayConstant
  calc
    _ = (4*originalScalarDecayConstant parameters length+
        (lowBalanceConstant length parameters.gamma+2)*(1+length⁻¹)*originalScalarDecayConstant parameters length)*
        (lower^(-(9/4:ℝ))*lower^(5/2:ℝ))*‖vector‖+
        originalFluxDecayConstant parameters length*(lower^(-(5/4:ℝ))*lower^(3/2:ℝ))*‖vector‖ := by ring
    _ = _ := by rw [scalarPower,fluxPower]; ring

end Grad.OriginalPhysicalKernelUniqueness

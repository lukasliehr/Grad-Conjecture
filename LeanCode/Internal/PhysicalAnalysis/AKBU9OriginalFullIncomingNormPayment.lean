import AKBU5SameOriginalHighIncomingPayment
import AKBU8OriginalLowIncomingNormPayment

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.OriginalPhysicalKernelUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.AnnularLowEnergy Grad.AnnularCoupledInverse
open Grad.AnnularVariational Grad.AnnularCrossMaps Grad.AnnularFluxTrace Grad.PhaseAlgebra
open Grad.OriginalKernelRetainedDecay Grad.AnnularCurrentLow Grad.AnnularIncomingIntegrability Grad.AnnularHighTilt Grad.AnnularTiltedReference

/-- The genuine original BF incoming pair is controlled by SAME lambda-
weighted Xi, R Xi and x. The original high and low singular powers are
retained, so the A4 decay can be applied without any width loss. -/
theorem originalFullIncoming_norm_bound
    (parameters : PhaseParameters) (lower length : ℝ) (positive : 0<lower) (bounded : lower<1)
    (lengthPositive : 0<length) (field : CoupledSpace lower length positive lengthPositive)
    (xi rotatedXi x : CellL2 1)
    (representedXi : ∀ mode,sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field 0
      ⟨lower,le_rfl,bounded.le⟩ mode=lambdaCircleCoefficient parameters lower xi mode)
    (representedX : ∀ mode,sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field 0
      ⟨lower,le_rfl,bounded.le⟩ mode=lambdaCircleCoefficient parameters lower x mode)
    (rotation : OriginalCircleRotation xi rotatedXi) :
    ‖coupledIncomingTrace lower length positive bounded lengthPositive field‖≤
      (2*lower^(-(9/4:ℝ)))*(‖xi‖+‖rotatedXi‖)+
      ((((lowBalanceConstant length parameters.gamma+2)*(1+length⁻¹))*lower^(-(9/4:ℝ)))*‖xi‖+
      lower^(-(5/4:ℝ))*‖x‖) := by
  have pair : ‖coupledIncomingTrace lower length positive bounded lengthPositive field‖≤
      ‖annularEnergyTrace lower length positive bounded lengthPositive 0 (bEnergyDecode lower length positive field.ofLp.1.ofLp.1)‖+
      ‖lowIncomingTrace lower length positive bounded field.ofLp.2‖ := by
    have square := WithLp.prod_norm_sq_eq_of_L2 (coupledIncomingTrace lower length positive bounded lengthPositive field)
    change ‖coupledIncomingTrace lower length positive bounded lengthPositive field‖^2=
      ‖annularEnergyTrace lower length positive bounded lengthPositive 0 (bEnergyDecode lower length positive field.ofLp.1.ofLp.1)‖^2+
      ‖lowIncomingTrace lower length positive bounded field.ofLp.2‖^2 at square
    nlinarith [norm_nonneg (coupledIncomingTrace lower length positive bounded lengthPositive field),
      norm_nonneg (annularEnergyTrace lower length positive bounded lengthPositive 0 (bEnergyDecode lower length positive field.ofLp.1.ofLp.1)),
      norm_nonneg (lowIncomingTrace lower length positive bounded field.ofLp.2)]
  exact pair.trans (add_le_add (originalHighIncoming_norm_bound parameters lower length positive bounded lengthPositive field xi rotatedXi representedXi rotation)
    (originalLowIncoming_norm_bound parameters lower length positive bounded lengthPositive field xi x representedXi representedX))

end Grad.OriginalPhysicalKernelUniqueness

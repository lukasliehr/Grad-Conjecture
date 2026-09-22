import AKAR5ActualAxisCoefficientPrimitives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.SourceBoundaryTrace Grad.SourceCollarDivision
open Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.PhaseAlgebra Grad.BoundaryLift
open Grad.SourceCollarCoefficients Grad.ActualPhysicalField Grad.SourceCollar
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Envelope

variable {input output : ℕ}
def originalCircleFamilyAction (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (radius : RadialPoint) :=
  lambdaCircleAction parameters radius (originalMatrixRadialKernel parameters family coherent radius)
def originalCircleFamilyAngularAction (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (radius : RadialPoint) :=
  lambdaCircleAction parameters radius (angularCoefficientKernel (originalMatrixRadialKernel parameters family coherent radius))

def originalCircleFamilyConstant (parameters : PhaseParameters) (input output : ℕ)
    (profile : EstimateProfile) (angular : Bool) : ℝ :=
  let moment := if angular then 2 else 1
  2 * physicalMatrixKernelConstant parameters input output moment *
    (profile.fixed (moment+1) + profile.deviation (moment+1))

theorem originalCircleFamilyAction_norm (parameters : PhaseParameters) (rho epsilon : ℝ) (base : ACore parameters 3)
    (profile : EstimateProfile) (actual reference : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (estimate : FamilyEstimate parameters base rho epsilon 4 profile actual reference)
    (small : physicalBudget parameters base rho epsilon 8 ≤ 1) (radius : RadialPoint) :
    ‖originalCircleFamilyAction parameters actual estimate.actualCoherent radius‖ ≤
      originalCircleFamilyConstant parameters input output profile false := by
  apply (lambdaCircleAction_norm parameters radius _).trans
  have matrix := originalMatrixRadialKernel_bound parameters actual estimate.actualCoherent radius 1
  have family := familyEstimate_bounded_grade parameters rho epsilon base profile actual reference estimate small 2 (by omega)
  have bound := mul_le_mul_of_nonneg_left family (physicalMatrixKernelConstant_nonnegative parameters input output 1)
  change _ ≤ 2 * physicalMatrixKernelConstant parameters input output 1 * (profile.fixed 2+profile.deviation 2)
  nlinarith only [matrix,bound]

theorem originalCircleFamilyAngularAction_norm (parameters : PhaseParameters) (rho epsilon : ℝ) (base : ACore parameters 3)
    (profile : EstimateProfile) (actual reference : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (estimate : FamilyEstimate parameters base rho epsilon 4 profile actual reference)
    (small : physicalBudget parameters base rho epsilon 8 ≤ 1) (radius : RadialPoint) :
    ‖originalCircleFamilyAngularAction parameters actual estimate.actualCoherent radius‖ ≤
      originalCircleFamilyConstant parameters input output profile true := by
  apply (lambdaCircleAction_norm parameters radius _).trans
  have matrix := (angularCoefficientKernel_moment (originalMatrixRadialKernel parameters actual estimate.actualCoherent radius) 1).trans
    (originalMatrixRadialKernel_bound parameters actual estimate.actualCoherent radius 2)
  have family := familyEstimate_bounded_grade parameters rho epsilon base profile actual reference estimate small 3 (by omega)
  have bound := mul_le_mul_of_nonneg_left family (physicalMatrixKernelConstant_nonnegative parameters input output 2)
  change _ ≤ 2 * physicalMatrixKernelConstant parameters input output 2 * (profile.fixed 3+profile.deviation 3)
  nlinarith only [matrix,bound]

def originalTransposeFrameFamily (parameters : PhaseParameters) (length epsilon : ℝ) (base : ACore parameters 3) :=
  transposeFamily (unitDiskAdmissible parameters) (originalFullFrameFamily parameters length epsilon base)
def originalTransposeFrameProfile (parameters : PhaseParameters) (length : ℝ) :=
  transposeProfile 4 3 3 (originalFullFrameProfile parameters length)

theorem originalTransposeFrameFamily_estimate (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (base : ACore parameters 3) (small : physicalBudget parameters base rho epsilon 6 ≤ originalCoefficientLowRadius parameters length) :
    FamilyEstimate parameters base rho epsilon 4 (originalTransposeFrameProfile parameters length)
      (originalTransposeFrameFamily parameters length epsilon base)
      (transposeFamily (unitDiskAdmissible parameters)
        (constantFamily 1 parameters.sigma0 parameters.gamma 1 Grad.GaugeCoefficients.Physical.Frame.referenceFrame)) := by
  have margin := originalCoefficient_low_margin parameters length rho epsilon base small
  exact transposeFamily_estimate (unitDiskAdmissible parameters) margin.2.1
    (originalFullFrameFamily_estimate parameters length rho epsilon base margin.1)

end Grad.OriginalKernelRetainedDecay

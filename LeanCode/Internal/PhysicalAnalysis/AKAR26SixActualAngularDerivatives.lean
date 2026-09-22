import AKAR24PolarOperatorProductRules

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.BoundaryLift Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.AnnularGeneralSourceRegularity
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation

structure AxisCirclePrimitives.HasDerivatives (primitives : AxisCirclePrimitives) : Prop where
  frame : OriginalCircleOperatorDerivative primitives.frameTranspose primitives.rotationFrameTranspose
  covector : OriginalCircleOperatorDerivative primitives.covector primitives.rotationCovector
  cofactor : OriginalCircleOperatorDerivative primitives.cofactor primitives.rotationCofactor

theorem AxisCirclePrimitives.HasDerivatives.c {primitives : AxisCirclePrimitives}
    (derivatives : primitives.HasDerivatives) (parameters : PhaseParameters) :
    OriginalCircleOperatorDerivative (primitives.coefficients parameters).c (primitives.coefficients parameters).d := by
  have result := (originalCircleTangentialRow_derivative parameters).comp derivatives.frame
  convert result using 1
  · rfl
  · ext field
    simp only [AxisCirclePrimitives.coefficients,ContinuousLinearMap.comp_apply,add_apply,sub_apply,neg_apply]
    abel

theorem AxisCirclePrimitives.HasDerivatives.C {primitives : AxisCirclePrimitives}
    (derivatives : primitives.HasDerivatives) (parameters : PhaseParameters) :
    OriginalCircleOperatorDerivative (primitives.coefficients parameters).C (primitives.coefficients parameters).RC :=
  (originalCircleRadialRow_derivative parameters).comp derivatives.covector

theorem AxisCirclePrimitives.HasDerivatives.kappa {primitives : AxisCirclePrimitives}
    (derivatives : primitives.HasDerivatives) (parameters : PhaseParameters) :
    OriginalCircleOperatorDerivative (primitives.coefficients parameters).kappa (primitives.coefficients parameters).Rkappa := by
  have result := (originalCircleTangentialRow_derivative parameters).comp
    (derivatives.cofactor.comp (originalCircleRadialColumn_derivative parameters))
  convert result using 1
  · rfl
  · ext field
    simp only [AxisCirclePrimitives.coefficients,ContinuousLinearMap.comp_apply,add_apply,neg_apply,map_add]
    abel

theorem originalAxisCirclePrimitives_hasDerivatives (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 8 ≤ originalCoefficientLowRadius parameters length)
    (radius : RadialPoint) :
    (originalAxisCirclePrimitives parameters length rho epsilon base small radius).HasDerivatives := by
  exact ⟨originalCircleFamilyAction_derivative parameters _ _ radius,
    originalCircleFamilyAction_derivative parameters _ _ radius,
    originalCircleFamilyAction_derivative parameters _ _ radius⟩

end Grad.OriginalKernelRetainedDecay

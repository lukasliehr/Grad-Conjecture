import AKDP69ActualEndpointLowerGraphTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets Grad.SpatialDilation
namespace StartupAdjustableSpatialGraph
variable {State : Type*} {order : ℕ} {high low : State → ℝ}
    (parameters : PhaseParameters) (scale : Scale)

/-- The literal conjugated zeroth field is a finite sum of exactly the
second phase/tensor and first phase/flux terms from the native equation. -/
theorem phaseZerothFormula (fieldSecond : State → StartupL2 3)
    (tensorSecond : Fin 2 → Fin 2 → State → StartupL2 3) (fluxFirst : Fin 2 → State → StartupL2 3)
    (fieldEstimate : ∀ direction,StartupAdjustableSpatialGraph order (fun state => startupScaledPhaseSecondField
      parameters.sigma0 parameters.gamma scale.val parameters.gamma_pos.le scale.property.1.le scale.property.2 direction direction (fieldSecond state)) high low)
    (tensorEstimate : ∀ outer inner,StartupAdjustableSpatialGraph order (fun state => startupScaledPhaseSecondField
      parameters.sigma0 parameters.gamma scale.val parameters.gamma_pos.le scale.property.1.le scale.property.2 outer inner (tensorSecond outer inner state)) high low)
    (fluxEstimate : ∀ direction,StartupAdjustableSpatialGraph order (fun state => startupScaledPhaseFirstField
      parameters.sigma0 parameters.gamma scale.val parameters.gamma_pos.le scale.property.1.le scale.property.2 direction (fluxFirst direction state)) high low)
    (highNonnegative : ∀ state,0≤high state) :
    StartupAdjustableSpatialGraph order (fun state => startupPhaseEquationZeroth parameters.sigma0 parameters.gamma scale.val
      parameters.gamma_pos.le scale.property.1.le scale.property.2 0 (fieldSecond state)
      (fun outer inner => tensorSecond outer inner state) (fun direction => fluxFirst direction state)) high low := by
  have tensors := sum _ (fun outer => sum _ (tensorEstimate outer) highNonnegative) highNonnegative
  have fluxes := sum _ fluxEstimate highNonnegative
  have fields := sum _ fieldEstimate highNonnegative
  exact ((tensors.add fluxes).sub fields).congr (fun state => by simp only [startupPhaseEquationZeroth,zero_add])

theorem phaseFluxFormula (fieldFirst : State → StartupL2 3)
    (tensorFirst : Fin 2 → Fin 2 → State → StartupL2 3) (flux : Fin 2 → State → StartupL2 3)
    (fieldEstimate : ∀ direction,StartupAdjustableSpatialGraph order (fun state => startupScaledPhaseFirstField
      parameters.sigma0 parameters.gamma scale.val parameters.gamma_pos.le scale.property.1.le scale.property.2 direction (fieldFirst state)) high low)
    (tensorEstimate : ∀ outer inner direction,StartupAdjustableSpatialGraph order (fun state => startupScaledPhaseFirstField
      parameters.sigma0 parameters.gamma scale.val parameters.gamma_pos.le scale.property.1.le scale.property.2 direction (tensorFirst outer inner state)) high low)
    (fluxEstimate : ∀ direction,StartupAdjustableSpatialGraph order (flux direction) high low)
    (direction : Fin 2) (highNonnegative : ∀ state,0≤high state) :
    StartupAdjustableSpatialGraph order (fun state => startupPhaseEquationFlux parameters.sigma0 parameters.gamma scale.val
      parameters.gamma_pos.le scale.property.1.le scale.property.2 (fieldFirst state)
      (fun outer inner => tensorFirst outer inner state) (fun dir => flux dir state) direction) high low := by
  have first := sum _ (fun inner => tensorEstimate direction inner inner) highNonnegative
  have second := sum _ (fun outer => tensorEstimate outer direction outer) highNonnegative
  exact (((fluxEstimate direction).add first).add second).sub ((fieldEstimate direction).smul 2 highNonnegative)

end StartupAdjustableSpatialGraph
end Grad.CartesianStartup

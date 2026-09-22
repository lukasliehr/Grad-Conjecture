import AKDP67FiniteAdjustableGraphFormula

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets
namespace StartupAdjustableSpatialGraph
variable {State : Type*} {order : ℕ} {field : State → StartupL2 3} {high low : State → ℝ}
    (cutoff : Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff) (compact : HasCompactSupport cutoff)

theorem cutoffGraph (estimate : StartupAdjustableSpatialGraph order field high low) (highNonnegative : ∀ state,0≤high state) :
    StartupAdjustableSpatialGraph order (fun state => startupCutoffL2 cutoff smooth compact (field state)) high low :=
  estimate.map (startupCutoffSpatialGraph cutoff smooth compact order 0) (startupCutoffL2 cutoff smooth compact)
    (startupCutoffSpatialGraph_base cutoff smooth compact order 0) highNonnegative

theorem cutoffFirst (estimate : StartupAdjustableSpatialGraph order field high low)
    (direction : Fin 2) (highNonnegative : ∀ state,0≤high state) :
    StartupAdjustableSpatialGraph order (fun state => startupCutoffDerivative cutoff smooth compact direction (field state)) high low :=
  estimate.map (startupCutoffDerivativeGraph cutoff smooth compact direction) (startupCutoffDerivative cutoff smooth compact direction)
    (startupCutoffDerivativeGraph_base cutoff smooth compact direction) highNonnegative

theorem cutoffSecond (estimate : StartupAdjustableSpatialGraph order field high low)
    (outer inner : Fin 2) (highNonnegative : ∀ state,0≤high state) :
    StartupAdjustableSpatialGraph order (fun state => startupCutoffSecondDerivative cutoff smooth compact outer inner (field state)) high low :=
  estimate.map (startupCutoffSecondDerivativeGraph cutoff smooth compact outer inner) (startupCutoffSecondDerivative cutoff smooth compact outer inner)
    (startupCutoffSecondDerivativeGraph_base cutoff smooth compact outer inner) highNonnegative

/-- The complete literal compact zeroth remainder inherits the actual
lower graph estimates of all its phase and cutoff factors. -/
theorem cutoffZeroth {zeroth : State → StartupL2 3}
    {tensor : Fin 2 → Fin 2 → State → StartupL2 3} {flux : Fin 2 → State → StartupL2 3}
    (fieldEstimate : StartupAdjustableSpatialGraph order field high low)
    (zeroEstimate : StartupAdjustableSpatialGraph order zeroth high low)
    (tensorEstimate : ∀ outer inner,StartupAdjustableSpatialGraph order (tensor outer inner) high low)
    (fluxEstimate : ∀ direction,StartupAdjustableSpatialGraph order (flux direction) high low)
    (highNonnegative : ∀ state,0≤high state) :
    StartupAdjustableSpatialGraph order (fun state => startupCutoffEquationZeroth cutoff smooth compact (field state) (zeroth state)
      (fun outer inner => tensor outer inner state) (fun direction => flux direction state)) high low := by
  have tensors := sum _ (fun outer => sum _ (fun inner => cutoffSecond cutoff smooth compact (tensorEstimate outer inner) outer inner highNonnegative) highNonnegative) highNonnegative
  have fluxes := sum _ (fun direction => cutoffFirst cutoff smooth compact (fluxEstimate direction) direction highNonnegative) highNonnegative
  have fields := sum _ (fun direction : Fin 2 => cutoffSecond cutoff smooth compact fieldEstimate direction direction highNonnegative) highNonnegative
  exact (((cutoffGraph cutoff smooth compact zeroEstimate highNonnegative).add tensors).add fluxes).sub fields

theorem cutoffFlux {tensor : Fin 2 → Fin 2 → State → StartupL2 3} {flux : Fin 2 → State → StartupL2 3}
    (fieldEstimate : StartupAdjustableSpatialGraph order field high low)
    (tensorEstimate : ∀ outer inner,StartupAdjustableSpatialGraph order (tensor outer inner) high low)
    (fluxEstimate : ∀ direction,StartupAdjustableSpatialGraph order (flux direction) high low)
    (direction : Fin 2) (highNonnegative : ∀ state,0≤high state) :
    StartupAdjustableSpatialGraph order (fun state => startupCutoffEquationFlux cutoff smooth compact (field state)
      (fun outer inner => tensor outer inner state) (fun dir => flux dir state) direction) high low := by
  have first := sum _ (fun inner => cutoffFirst cutoff smooth compact (tensorEstimate direction inner) inner highNonnegative) highNonnegative
  have second := sum _ (fun outer => cutoffFirst cutoff smooth compact (tensorEstimate outer direction) outer highNonnegative) highNonnegative
  have last := (cutoffFirst cutoff smooth compact fieldEstimate direction highNonnegative).smul 2 highNonnegative
  exact (((cutoffGraph cutoff smooth compact (fluxEstimate direction) highNonnegative).add first).add second).sub last

end StartupAdjustableSpatialGraph
end Grad.CartesianStartup

import AKDP78SameSignedFluxGraphEstimates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger
namespace StartupSpatialAction
variable {L ell : ℝ}

def covariantPrimitive (rank : ℕ) : StartupSpatialAction rank 2 2 L ell :=
  (angular 2 rank (fun angle => ((angle*Real.cos angle : ℝ) : ℂ))
    (Complex.ofRealCLM.contDiff.comp (contDiff_id.mul Real.contDiff_cos))).sub
    ((value rank quarterValueMap).comp
      (angular 2 rank (fun angle => ((angle*Real.sin angle : ℝ) : ℂ))
        (Complex.ofRealCLM.contDiff.comp (contDiff_id.mul Real.contDiff_sin))))

theorem covariantPrimitive_coarse (rank : ℕ) :
    (covariantPrimitive (L := L) (ell := ell) rank).signed.coarse=startupCovariantPrimitiveKernel := rfl

theorem covariantPrimitive_originalEndpointControlled (parameters : PhaseParameters) (rank : ℕ) :
    (covariantPrimitive (L := L) (ell := ell) rank).OriginalEndpointControlled parameters :=
  (angular_originalEndpointControlled parameters 2 rank _ _).sub
    ((value_originalEndpointControlled parameters rank quarterValueMap).comp
      (angular_originalEndpointControlled parameters 2 rank _ _))

def lowerScalarFlux (rank : ℕ) (direction : Fin 2) : StartupSpatialAction rank 1 3 L ell :=
  if direction=0 then ((value rank (startupComponentEntry 0 0)).smul (-1)).add
      (((value rank (startupComponentEntry 1 0)).comp (trueAngular 1 rank 0)).smul 2)
  else (((value rank (startupComponentEntry 0 0)).comp (trueAngular 1 rank 0)).smul (-2)).sub
      (value rank (startupComponentEntry 1 0))

theorem lowerScalarFlux_originalEndpointControlled (parameters : PhaseParameters) (rank : ℕ) (direction : Fin 2) :
    (lowerScalarFlux (L := L) (ell := ell) rank direction).OriginalEndpointControlled parameters := by
  unfold lowerScalarFlux
  split_ifs
  · exact ((value_originalEndpointControlled parameters rank _).smul (-1)).add
      (((value_originalEndpointControlled parameters rank _).comp (trueAngular_originalEndpointControlled parameters 1 rank 0)).smul 2)
  · exact (((value_originalEndpointControlled parameters rank _).comp (trueAngular_originalEndpointControlled parameters 1 rank 0)).smul (-2)).sub
      (value_originalEndpointControlled parameters rank _)

def gradientVectorPart (rank : ℕ) : StartupSpatialAction rank 3 2 L ell :=
  ((planarMeanFree rank).comp (value rank planarPartMap)).add
    ((covariantPrimitive rank).comp (((value rank quarterValueMap).comp (value rank planarPartMap)).smul 2))

theorem gradientVectorPart_originalEndpointControlled (parameters : PhaseParameters) (rank : ℕ) :
    (gradientVectorPart (L := L) (ell := ell) rank).OriginalEndpointControlled parameters :=
  ((planarMeanFree_originalEndpointControlled parameters rank).comp (value_originalEndpointControlled parameters rank planarPartMap)).add
    ((covariantPrimitive_originalEndpointControlled parameters rank).comp
      (((value_originalEndpointControlled parameters rank quarterValueMap).comp (value_originalEndpointControlled parameters rank planarPartMap)).smul 2))

end StartupSpatialAction

def startupLowerScalarFluxKernel (direction : Fin 2) : StartupL2 1 →L[ℂ] StartupL2 3 :=
  if direction=0 then (-1 : ℂ) • originalValueKernel (startupComponentEntry 0 0)+
    (2 : ℂ) • (originalValueKernel (startupComponentEntry 1 0)).comp (startupTrueAngularInverse 1 0)
  else (-2 : ℂ) • (originalValueKernel (startupComponentEntry 0 0)).comp (startupTrueAngularInverse 1 0)-
    originalValueKernel (startupComponentEntry 1 0)

theorem startupLowerScalarFluxKernel_coarse {L ell : ℝ} (rank : ℕ) (direction : Fin 2) :
    (StartupSpatialAction.lowerScalarFlux (L := L) (ell := ell) rank direction).signed.coarse=startupLowerScalarFluxKernel direction := by
  unfold StartupSpatialAction.lowerScalarFlux startupLowerScalarFluxKernel
  split_ifs <;> rfl

theorem startupERLowerFlux_linear (lower : StartupL2 1) (gradient : StartupL2 2) (direction : Fin 2) :
    startupERLowerFlux lower gradient direction=startupLowerScalarFluxKernel direction lower-
      originalValueKernel (startupComponentEntry 2 direction) gradient := by
  unfold startupERLowerFlux startupLowerScalarFluxKernel
  split_ifs
  · simp only [add_apply,smul_apply,ContinuousLinearMap.comp_apply,neg_one_smul,neg_apply]
  · rfl

def startupGradientVectorKernel : StartupL2 3 →L[ℂ] StartupL2 2 :=
  originalPlanarMeanFreeKernel.comp (originalValueKernel planarPartMap)+
    startupCovariantPrimitiveKernel.comp ((2 : ℂ) • (originalValueKernel quarterValueMap).comp (originalValueKernel planarPartMap))

theorem startupGradientVectorKernel_coarse {L ell : ℝ} (rank : ℕ) :
    (StartupSpatialAction.gradientVectorPart (L := L) (ell := ell) rank).signed.coarse=startupGradientVectorKernel := rfl

end Grad.CartesianStartup

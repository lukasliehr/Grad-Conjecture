import AKCO7ActualSignedActionConstructors

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Ledger
namespace StartupSignedAction
variable {L sigma gamma ell : ℝ}

def identity (dimension : ℕ) : StartupSignedAction dimension dimension L ell :=
  fixed (ContinuousLinearMap.id ℂ _) (ContinuousLinearMap.id ℂ _)
    (startupCompatible_id dimension) (StartupCellwise.id dimension)

def value {input output : ℕ} (mapping : OperatorValue input output) : StartupSignedAction input output L ell :=
  fixed (originalValueKernel mapping) (originalValueFirstGraph mapping)
    (originalValueFirstGraph_compatible mapping) (originalValueKernel_cellwise mapping)

def complement : StartupSignedAction 3 3 L ell :=
  fixed originalComplementKernel originalComplementFirstGraph
    originalComplementFirstGraph_compatible originalComplementKernel_cellwise

def average : StartupSignedAction 2 2 L ell :=
  fixed originalAverageKernel originalAverageFirstGraph
    originalAverageFirstGraph_compatible originalAverageKernel_cellwise

def qrad : StartupSignedAction 2 2 L ell :=
  fixed startupGenuineQradKernel startupGenuineQradFirst startupGenuineQrad_compatible
    ((StartupCellwise.id 2).add ((originalValueKernel_cellwise quarterValueMap).comp
      (originalTangentialKernel_cellwise.comp (originalValueKernel_cellwise quarterValueMap))))

def planarMeanFree : StartupSignedAction 2 2 L ell :=
  fixed originalPlanarMeanFreeKernel originalPlanarMeanFreeFirstGraph originalPlanarMeanFreeFirstGraph_compatible
    ((StartupCellwise.id 2).sub originalAverageKernel_cellwise)

def scalarMeanFree : StartupSignedAction 1 1 L ell :=
  fixed originalScalarMeanFreeKernel originalScalarMeanFreeFirstGraph originalScalarMeanFreeFirstGraph_compatible
    ((StartupCellwise.id 1).sub (startupAngularKernel_cellwise _ _ _))

def current (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge)) : StartupSignedAction 3 3 L ell :=
  (identity 3).sub ((matrix admissible (complementExtensionFamily admissible gauge)
    (complementExtensionFamily_coherent admissible gauge coherent inverseCoherent)).comp
      (complement.comp (matrix admissible (fullGaugeFamily gauge) (fullGaugeFamily_coherent gauge coherent))))

variable (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell)
    (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))

def force : StartupSignedAction 3 2 L ell :=
  (qrad.comp ((matrix admissible data.rotatedPlanarProduct coherent.2.2.2.2.2.2.2.1).comp
    (current admissible data.gaugeDeviation coherent.2.2.2.1 inverseCoherent))).smul 2

def third : StartupSignedAction 3 1 L ell :=
  (scalarMeanFree.comp ((matrix admissible data.rotatedThirdProduct coherent.2.2.2.2.2.2.2.2).comp
    (current admissible data.gaugeDeviation coherent.2.2.2.1 inverseCoherent))).smul 2

def flux : StartupSignedAction 3 3 L ell :=
  (matrix admissible data.fluxDeviation coherent.2.2.2.2.1).comp
    (current admissible data.gaugeDeviation coherent.2.2.2.1 inverseCoherent)

def planarFlux : StartupSignedAction 3 2 L ell :=
  planarMeanFree.comp ((value planarPartMap).comp (flux admissible data coherent inverseCoherent))

def scalarFlux : StartupSignedAction 3 1 L ell :=
  scalarMeanFree.comp ((value toroidalPartMap).comp (flux admissible data coherent inverseCoherent))

def principalFlux : StartupSignedAction 3 2 L ell :=
  (planarFlux admissible data coherent inverseCoherent).sub
    (((value quarterValueMap).comp (average.comp (force admissible data coherent inverseCoherent))).smul (1/2))

theorem current_coarse :
    (current admissible data.gaugeDeviation coherent.2.2.2.1 inverseCoherent).coarse =
      originalCurrentKernel admissible data.gaugeDeviation coherent.2.2.2.1 inverseCoherent := rfl

theorem force_coarse : (force admissible data coherent inverseCoherent).coarse =
    startupGenuineForceKernel admissible data coherent inverseCoherent := rfl

theorem third_coarse : (third admissible data coherent inverseCoherent).coarse =
    originalThirdCorrectionKernel admissible data coherent inverseCoherent := rfl

theorem planarFlux_coarse : (planarFlux admissible data coherent inverseCoherent).coarse =
    originalPlanarFluxKernel admissible data coherent inverseCoherent := rfl

theorem scalarFlux_coarse : (scalarFlux admissible data coherent inverseCoherent).coarse =
    originalScalarFluxKernel admissible data coherent inverseCoherent := rfl

theorem principalFlux_coarse : (principalFlux admissible data coherent inverseCoherent).coarse =
    startupGenuinePrincipalFluxKernel admissible data coherent inverseCoherent := rfl

end StartupSignedAction
end Grad.CartesianStartup

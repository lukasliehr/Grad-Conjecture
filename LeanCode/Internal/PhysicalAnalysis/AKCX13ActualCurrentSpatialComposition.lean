import AKCX12OriginalFixedSpatialComposition

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxRecDepth 3000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
namespace StartupSpatialAction
variable {L sigma gamma ell : ℝ}

def current (admissible : Admissible L sigma gamma ell) (rank : ℕ)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge))
    (lengthNonzero : L ≠ 0) (scaleNonzero : ell ≠ 0) : StartupSpatialAction rank 3 3 L ell :=
  (identity rank 3).sub
    ((matrix admissible rank (complementExtensionFamily admissible gauge)
      (complementExtensionFamily_coherent admissible gauge coherent inverseCoherent) lengthNonzero scaleNonzero).comp
      ((complement rank).comp
        (matrix admissible rank (fullGaugeFamily gauge) (fullGaugeFamily_coherent gauge coherent) lengthNonzero scaleNonzero)))

variable (admissible : Admissible L sigma gamma ell) (rank : ℕ)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (lengthNonzero : L ≠ 0) (scaleNonzero : ell ≠ 0)

def force : StartupSpatialAction rank 3 2 L ell :=
  ((radial rank).comp
    ((matrix admissible rank data.rotatedPlanarProduct coherent.2.2.2.2.2.2.2.1 lengthNonzero scaleNonzero).comp
      (current admissible rank data.gaugeDeviation coherent.2.2.2.1 inverseCoherent lengthNonzero scaleNonzero))).smul 2

def third : StartupSpatialAction rank 3 1 L ell :=
  ((scalarMeanFree rank).comp
    ((matrix admissible rank data.rotatedThirdProduct coherent.2.2.2.2.2.2.2.2 lengthNonzero scaleNonzero).comp
      (current admissible rank data.gaugeDeviation coherent.2.2.2.1 inverseCoherent lengthNonzero scaleNonzero))).smul 2

def flux : StartupSpatialAction rank 3 3 L ell :=
  (matrix admissible rank data.fluxDeviation coherent.2.2.2.2.1 lengthNonzero scaleNonzero).comp
    (current admissible rank data.gaugeDeviation coherent.2.2.2.1 inverseCoherent lengthNonzero scaleNonzero)

def planarFlux : StartupSpatialAction rank 3 2 L ell :=
  (planarMeanFree rank).comp ((value rank planarPartMap).comp (flux admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero))

def scalarFlux : StartupSpatialAction rank 3 1 L ell :=
  (scalarMeanFree rank).comp ((value rank toroidalPartMap).comp (flux admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero))

def principalFlux : StartupSpatialAction rank 3 2 L ell :=
  (planarFlux admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero).sub
    (((value rank quarterValueMap).comp ((average rank).comp
      (force admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero))).smul (1/2))

theorem current_ranked :
    (current admissible rank data.gaugeDeviation coherent.2.2.2.1 inverseCoherent lengthNonzero scaleNonzero).ranked =
      StartupRankOperator.current admissible rank data.gaugeDeviation coherent.2.2.2.1 inverseCoherent := rfl

theorem force_ranked : (force admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero).ranked =
    StartupRankOperator.force admissible rank data coherent inverseCoherent := rfl

theorem principalFlux_ranked : (principalFlux admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero).ranked =
    StartupRankOperator.principalFlux admissible rank data coherent inverseCoherent := rfl

theorem current_coarse :
    (current admissible rank data.gaugeDeviation coherent.2.2.2.1 inverseCoherent lengthNonzero scaleNonzero).signed.coarse =
      originalCurrentKernel admissible data.gaugeDeviation coherent.2.2.2.1 inverseCoherent := rfl

theorem force_coarse : (force admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero).signed.coarse =
    startupGenuineForceKernel admissible data coherent inverseCoherent := rfl

theorem third_coarse : (third admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero).signed.coarse =
    originalThirdCorrectionKernel admissible data coherent inverseCoherent := rfl

theorem principalFlux_coarse : (principalFlux admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero).signed.coarse =
    startupGenuinePrincipalFluxKernel admissible data coherent inverseCoherent := rfl

end StartupSpatialAction
end Grad.CartesianStartup

import AKAA14OriginalFixedOperators

noncomputable section

set_option maxHeartbeats 1400000

namespace Grad.CartesianStartup

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger Grad.GenericCarriers

variable {L sigma gamma ell : ℝ}

def originalCurrentKernel (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge)) :
    StartupL2 3 →L[ℂ] StartupL2 3 :=
  ContinuousLinearMap.id ℂ _ -
    (originalMatrixKernel admissible (complementExtensionFamily admissible gauge)
      (complementExtensionFamily_coherent admissible gauge coherent inverseCoherent)).comp
      (originalComplementKernel.comp
        (originalMatrixKernel admissible (fullGaugeFamily gauge) (fullGaugeFamily_coherent gauge coherent)))

def originalRadialProjectionKernel : StartupL2 2 →L[ℂ] StartupL2 2 :=
  ContinuousLinearMap.id ℂ _ - originalTangentialKernel

/-- Literal a(w)=2 Qrad (RF_perp)^T F^{-T} Qa w, with its actual
 completed physical coefficient family and both original gauges. -/
def originalForceCorrectionKernel (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) :
    StartupL2 3 →L[ℂ] StartupL2 2 :=
  (2 : ℂ) • originalRadialProjectionKernel.comp
    ((originalMatrixKernel admissible data.rotatedPlanarProduct coherent.2.2.2.2.2.2.2.1).comp
      (originalCurrentKernel admissible data.gaugeDeviation coherent.2.2.2.1 inverseCoherent))

def originalThirdCorrectionKernel (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) :
    StartupL2 3 →L[ℂ] StartupL2 1 :=
  (2 : ℂ) • originalScalarMeanFreeKernel.comp
    ((originalMatrixKernel admissible data.rotatedThirdProduct coherent.2.2.2.2.2.2.2.2).comp
      (originalCurrentKernel admissible data.gaugeDeviation coherent.2.2.2.1 inverseCoherent))

def originalFluxKernel (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) :
    StartupL2 3 →L[ℂ] StartupL2 3 :=
  (originalMatrixKernel admissible data.fluxDeviation coherent.2.2.2.2.1).comp
    (originalCurrentKernel admissible data.gaugeDeviation coherent.2.2.2.1 inverseCoherent)

def originalPlanarFluxKernel (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) :
    StartupL2 3 →L[ℂ] StartupL2 2 :=
  originalPlanarMeanFreeKernel.comp ((originalValueKernel planarPartMap).comp
    (originalFluxKernel admissible data coherent inverseCoherent))

def originalScalarFluxKernel (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) :
    StartupL2 3 →L[ℂ] StartupL2 1 :=
  originalScalarMeanFreeKernel.comp ((originalValueKernel toroidalPartMap).comp
    (originalFluxKernel admissible data coherent inverseCoherent))

/-- The exact zero-order coefficient s=h_perp-JAa/2 in ER11. -/
def originalPrincipalFluxKernel (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) :
    StartupL2 3 →L[ℂ] StartupL2 2 :=
  originalPlanarFluxKernel admissible data coherent inverseCoherent -
    (1 / 2 : ℂ) • (originalValueKernel quarterValueMap).comp
      (originalAverageKernel.comp (originalForceCorrectionKernel admissible data coherent inverseCoherent))

end Grad.CartesianStartup

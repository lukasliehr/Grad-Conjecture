import AKAA29OriginalFixedFirstGraphs
import AKAA15LiteralCurrentRowKernels

noncomputable section

set_option maxHeartbeats 1800000

namespace Grad.CartesianStartup

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger Grad.GenericCarriers

variable {L sigma gamma ell : ℝ}

def originalCurrentFirstGraph (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge)) :
    StartupFirst 3 →L[ℂ] StartupFirst 3 :=
  ContinuousLinearMap.id ℂ _ -
    (startupMatrixFirstGraphCLM admissible (complementExtensionFamily admissible gauge)
      (complementExtensionFamily_coherent admissible gauge coherent inverseCoherent)).comp
      (originalComplementFirstGraph.comp
        (startupMatrixFirstGraphCLM admissible (fullGaugeFamily gauge) (fullGaugeFamily_coherent gauge coherent)))

def originalRadialProjectionFirstGraph : StartupFirst 2 →L[ℂ] StartupFirst 2 :=
  ContinuousLinearMap.id ℂ _ - originalTangentialFirstGraph

/-- Literal a(w)=2 Qrad (RF_perp)^T F^{-T} Qa w, with its actual
 completed physical coefficient family and both original gauges. -/
def originalForceCorrectionFirstGraph (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) :
    StartupFirst 3 →L[ℂ] StartupFirst 2 :=
  (2 : ℂ) • originalRadialProjectionFirstGraph.comp
    ((startupMatrixFirstGraphCLM admissible data.rotatedPlanarProduct coherent.2.2.2.2.2.2.2.1).comp
      (originalCurrentFirstGraph admissible data.gaugeDeviation coherent.2.2.2.1 inverseCoherent))

def originalThirdCorrectionFirstGraph (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) :
    StartupFirst 3 →L[ℂ] StartupFirst 1 :=
  (2 : ℂ) • originalScalarMeanFreeFirstGraph.comp
    ((startupMatrixFirstGraphCLM admissible data.rotatedThirdProduct coherent.2.2.2.2.2.2.2.2).comp
      (originalCurrentFirstGraph admissible data.gaugeDeviation coherent.2.2.2.1 inverseCoherent))

def originalFluxFirstGraph (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) :
    StartupFirst 3 →L[ℂ] StartupFirst 3 :=
  (startupMatrixFirstGraphCLM admissible data.fluxDeviation coherent.2.2.2.2.1).comp
    (originalCurrentFirstGraph admissible data.gaugeDeviation coherent.2.2.2.1 inverseCoherent)

def originalPlanarFluxFirstGraph (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) :
    StartupFirst 3 →L[ℂ] StartupFirst 2 :=
  originalPlanarMeanFreeFirstGraph.comp ((originalValueFirstGraph planarPartMap).comp
    (originalFluxFirstGraph admissible data coherent inverseCoherent))

def originalScalarFluxFirstGraph (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) :
    StartupFirst 3 →L[ℂ] StartupFirst 1 :=
  originalScalarMeanFreeFirstGraph.comp ((originalValueFirstGraph toroidalPartMap).comp
    (originalFluxFirstGraph admissible data coherent inverseCoherent))

/-- The exact zero-order coefficient s=h_perp-JAa/2 in ER11. -/
def originalPrincipalFluxFirstGraph (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) :
    StartupFirst 3 →L[ℂ] StartupFirst 2 :=
  originalPlanarFluxFirstGraph admissible data coherent inverseCoherent -
    (1 / 2 : ℂ) • (originalValueFirstGraph quarterValueMap).comp
      (originalAverageFirstGraph.comp (originalForceCorrectionFirstGraph admissible data coherent inverseCoherent))


theorem originalCurrentFirstGraph_compatible (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge)) :
    StartupCompatible (originalCurrentKernel admissible gauge coherent inverseCoherent)
      (originalCurrentFirstGraph admissible gauge coherent inverseCoherent) :=
  startupCompatible_sub (startupCompatible_id _)
    (startupCompatible_comp (startupMatrixFirstGraph_compatible _ _ _)
      (startupCompatible_comp originalComplementFirstGraph_compatible (startupMatrixFirstGraph_compatible _ _ _)))

theorem originalRadialProjectionFirstGraph_compatible :
    StartupCompatible originalRadialProjectionKernel originalRadialProjectionFirstGraph :=
  startupCompatible_sub (startupCompatible_id _) originalTangentialFirstGraph_compatible

variable (admissible : Admissible L sigma gamma ell)
  (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
  (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))

theorem originalForceCorrectionFirstGraph_compatible :
    StartupCompatible (originalForceCorrectionKernel admissible data coherent inverseCoherent)
      (originalForceCorrectionFirstGraph admissible data coherent inverseCoherent) :=
  startupCompatible_smul _ (startupCompatible_comp originalRadialProjectionFirstGraph_compatible
    (startupCompatible_comp (startupMatrixFirstGraph_compatible _ _ _)
      (originalCurrentFirstGraph_compatible _ _ _ _)))

theorem originalThirdCorrectionFirstGraph_compatible :
    StartupCompatible (originalThirdCorrectionKernel admissible data coherent inverseCoherent)
      (originalThirdCorrectionFirstGraph admissible data coherent inverseCoherent) :=
  startupCompatible_smul _ (startupCompatible_comp originalScalarMeanFreeFirstGraph_compatible
    (startupCompatible_comp (startupMatrixFirstGraph_compatible _ _ _)
      (originalCurrentFirstGraph_compatible _ _ _ _)))

theorem originalFluxFirstGraph_compatible :
    StartupCompatible (originalFluxKernel admissible data coherent inverseCoherent)
      (originalFluxFirstGraph admissible data coherent inverseCoherent) :=
  startupCompatible_comp (startupMatrixFirstGraph_compatible _ _ _) (originalCurrentFirstGraph_compatible _ _ _ _)

theorem originalPlanarFluxFirstGraph_compatible :
    StartupCompatible (originalPlanarFluxKernel admissible data coherent inverseCoherent)
      (originalPlanarFluxFirstGraph admissible data coherent inverseCoherent) :=
  startupCompatible_comp originalPlanarMeanFreeFirstGraph_compatible
    (startupCompatible_comp (originalValueFirstGraph_compatible _) (originalFluxFirstGraph_compatible _ _ _ _))

theorem originalScalarFluxFirstGraph_compatible :
    StartupCompatible (originalScalarFluxKernel admissible data coherent inverseCoherent)
      (originalScalarFluxFirstGraph admissible data coherent inverseCoherent) :=
  startupCompatible_comp originalScalarMeanFreeFirstGraph_compatible
    (startupCompatible_comp (originalValueFirstGraph_compatible _) (originalFluxFirstGraph_compatible _ _ _ _))

/-- The literal ER11 principal zero-order product s=h_perp-JAa/2 acts
 boundedly on the same first weak graph and has exactly its full-cell L2 action. -/
theorem originalPrincipalFluxFirstGraph_compatible :
    StartupCompatible (originalPrincipalFluxKernel admissible data coherent inverseCoherent)
      (originalPrincipalFluxFirstGraph admissible data coherent inverseCoherent) :=
  startupCompatible_sub (originalPlanarFluxFirstGraph_compatible _ _ _ _)
    (startupCompatible_smul _ (startupCompatible_comp (originalValueFirstGraph_compatible _)
      (startupCompatible_comp originalAverageFirstGraph_compatible
        (originalForceCorrectionFirstGraph_compatible _ _ _ _))))

end Grad.CartesianStartup

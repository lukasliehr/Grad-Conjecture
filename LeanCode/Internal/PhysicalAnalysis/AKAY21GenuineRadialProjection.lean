import AKAY19ScaledWeakConjugation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000

namespace Grad.CartesianStartup
open Grad.GenericCarriers Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

/-- The actual force projector I+JTJ removes the radial equivariant mean.
This corrects the old I-T specialization without changing its frozen evidence. -/
def startupGenuineQradKernel : StartupL2 2 →L[ℂ] StartupL2 2 :=
  ContinuousLinearMap.id ℂ _ + (originalValueKernel quarterValueMap).comp
    (originalTangentialKernel.comp (originalValueKernel quarterValueMap))

def startupGenuineQradFirst : StartupFirst 2 →L[ℂ] StartupFirst 2 :=
  ContinuousLinearMap.id ℂ _ + (originalValueFirstGraph quarterValueMap).comp
    (originalTangentialFirstGraph.comp (originalValueFirstGraph quarterValueMap))

theorem startupGenuineQrad_compatible : StartupCompatible startupGenuineQradKernel startupGenuineQradFirst :=
  startupCompatible_add (startupCompatible_id _)
    (startupCompatible_comp (originalValueFirstGraph_compatible _)
      (startupCompatible_comp originalTangentialFirstGraph_compatible (originalValueFirstGraph_compatible _)))

variable {L sigma gamma ell : ℝ}

def startupGenuineForceKernel (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) :
    StartupL2 3 →L[ℂ] StartupL2 2 :=
  (2 : ℂ) • startupGenuineQradKernel.comp
    ((originalMatrixKernel admissible data.rotatedPlanarProduct coherent.2.2.2.2.2.2.2.1).comp
      (originalCurrentKernel admissible data.gaugeDeviation coherent.2.2.2.1 inverseCoherent))

def startupGenuineForceFirst (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) :
    StartupFirst 3 →L[ℂ] StartupFirst 2 :=
  (2 : ℂ) • startupGenuineQradFirst.comp
    ((startupMatrixFirstGraphCLM admissible data.rotatedPlanarProduct coherent.2.2.2.2.2.2.2.1).comp
      (originalCurrentFirstGraph admissible data.gaugeDeviation coherent.2.2.2.1 inverseCoherent))

theorem startupGenuineForce_compatible (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) :
    StartupCompatible (startupGenuineForceKernel admissible data coherent inverseCoherent)
      (startupGenuineForceFirst admissible data coherent inverseCoherent) :=
  startupCompatible_smul _ (startupCompatible_comp startupGenuineQrad_compatible
    (startupCompatible_comp (startupMatrixFirstGraph_compatible _ _ _) (originalCurrentFirstGraph_compatible _ _ _ _)))

/-- ER11's s retains the correction from the genuine force projector. -/
def startupGenuinePrincipalFluxKernel (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) :
    StartupL2 3 →L[ℂ] StartupL2 2 :=
  originalPlanarFluxKernel admissible data coherent inverseCoherent -
    (1 / 2 : ℂ) • (originalValueKernel quarterValueMap).comp
      (originalAverageKernel.comp (startupGenuineForceKernel admissible data coherent inverseCoherent))

def startupGenuinePrincipalFluxFirst (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) :
    StartupFirst 3 →L[ℂ] StartupFirst 2 :=
  originalPlanarFluxFirstGraph admissible data coherent inverseCoherent -
    (1 / 2 : ℂ) • (originalValueFirstGraph quarterValueMap).comp
      (originalAverageFirstGraph.comp (startupGenuineForceFirst admissible data coherent inverseCoherent))

theorem startupGenuinePrincipalFlux_compatible (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) :
    StartupCompatible (startupGenuinePrincipalFluxKernel admissible data coherent inverseCoherent)
      (startupGenuinePrincipalFluxFirst admissible data coherent inverseCoherent) :=
  startupCompatible_sub (originalPlanarFluxFirstGraph_compatible _ _ _ _)
    (startupCompatible_smul _ (startupCompatible_comp (originalValueFirstGraph_compatible _)
      (startupCompatible_comp originalAverageFirstGraph_compatible (startupGenuineForce_compatible _ _ _ _))))

end Grad.CartesianStartup

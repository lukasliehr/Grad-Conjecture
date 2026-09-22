import AKBW14OriginalFixedRankOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxRecDepth 3000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger

namespace StartupRankOperator
variable {L sigma gamma ell : ℝ}

def current (admissible : Admissible L sigma gamma ell) (rank : ℕ)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge)) : StartupRankOperator rank 3 3 :=
  (identity rank 3).sub
    ((matrix admissible rank (complementExtensionFamily admissible gauge)
      (complementExtensionFamily_coherent admissible gauge coherent inverseCoherent)).comp
      ((complement rank).comp
        (matrix admissible rank (fullGaugeFamily gauge) (fullGaugeFamily_coherent gauge coherent))))

def force (admissible : Admissible L sigma gamma ell) (rank : ℕ)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) : StartupRankOperator rank 3 2 :=
  ((radial rank).comp
    ((matrix admissible rank data.rotatedPlanarProduct coherent.2.2.2.2.2.2.2.1).comp
      (current admissible rank data.gaugeDeviation coherent.2.2.2.1 inverseCoherent))).smul 2

def third (admissible : Admissible L sigma gamma ell) (rank : ℕ)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) : StartupRankOperator rank 3 1 :=
  ((scalarMeanFree rank).comp
    ((matrix admissible rank data.rotatedThirdProduct coherent.2.2.2.2.2.2.2.2).comp
      (current admissible rank data.gaugeDeviation coherent.2.2.2.1 inverseCoherent))).smul 2

def flux (admissible : Admissible L sigma gamma ell) (rank : ℕ)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) : StartupRankOperator rank 3 3 :=
  (matrix admissible rank data.fluxDeviation coherent.2.2.2.2.1).comp
    (current admissible rank data.gaugeDeviation coherent.2.2.2.1 inverseCoherent)

def planarFlux (admissible : Admissible L sigma gamma ell) (rank : ℕ)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) : StartupRankOperator rank 3 2 :=
  (planarMeanFree rank).comp ((value rank planarPartMap).comp (flux admissible rank data coherent inverseCoherent))

def scalarFlux (admissible : Admissible L sigma gamma ell) (rank : ℕ)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) : StartupRankOperator rank 3 1 :=
  (scalarMeanFree rank).comp ((value rank toroidalPartMap).comp (flux admissible rank data coherent inverseCoherent))

def principalFlux (admissible : Admissible L sigma gamma ell) (rank : ℕ)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) : StartupRankOperator rank 3 2 :=
  (planarFlux admissible rank data coherent inverseCoherent).sub
    (((value rank quarterValueMap).comp ((average rank).comp (force admissible rank data coherent inverseCoherent))).smul (1 / 2))

theorem current_bound_independent (admissible : Admissible L sigma gamma ell) (rank : ℕ)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge)) :
    (current admissible rank gauge coherent inverseCoherent).bound =
      (current admissible 0 gauge coherent inverseCoherent).bound := rfl

theorem force_bound_independent (admissible : Admissible L sigma gamma ell) (rank : ℕ)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) :
    (force admissible rank data coherent inverseCoherent).bound = (force admissible 0 data coherent inverseCoherent).bound := rfl

theorem third_bound_independent (admissible : Admissible L sigma gamma ell) (rank : ℕ)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) :
    (third admissible rank data coherent inverseCoherent).bound = (third admissible 0 data coherent inverseCoherent).bound := rfl

theorem principalFlux_bound_independent (admissible : Admissible L sigma gamma ell) (rank : ℕ)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) :
    (principalFlux admissible rank data coherent inverseCoherent).bound =
      (principalFlux admissible 0 data coherent inverseCoherent).bound := rfl

end StartupRankOperator
end Grad.CartesianStartup

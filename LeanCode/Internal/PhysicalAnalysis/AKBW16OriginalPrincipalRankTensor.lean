import AKBW15OriginalCurrentRankOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000
set_option synthInstance.maxHeartbeats 200000
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.Constraints.Gauges
open Grad.Constraints Grad.ActualAngularInverse
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger

namespace StartupRankOperator

def inverseCovector (rank : ℕ) (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight)
    (direction coordinate : Fin 2) : StartupRankOperator rank 3 3 :=
  angular 3 rank (startupCovectorWeight weight direction coordinate)
    (startupCovectorWeight_smooth weight smooth direction coordinate)

def trueInverseTensor (rank : ℕ) (input output : Fin 2) : StartupRankOperator rank 3 3 :=
  (inverseCovector rank (shiftPrimitiveKernel 0) (shiftPrimitiveKernel_smooth 0) input output).sub
    (((inverseCovector rank (shiftPrimitiveKernel 0) (shiftPrimitiveKernel_smooth 0) 0 output).comp
      (inverseCovector rank (angularCharacter 0) (angularCharacter_smooth 0) input 0)).add
    ((inverseCovector rank (shiftPrimitiveKernel 0) (shiftPrimitiveKernel_smooth 0) 1 output).comp
      (inverseCovector rank (angularCharacter 0) (angularCharacter_smooth 0) input 1)))

def principalFixed (rank : ℕ) (outer inner : Fin 2) (row : Fin 3) : StartupRankOperator rank 3 3 :=
  ![((value rank (startupPlanarRotatedEntryMap outer 1)).comp (trueInverseTensor rank 0 inner)).sub
      ((value rank (startupPlanarRotatedEntryMap outer 0)).comp (trueInverseTensor rank 1 inner)),
    if outer = inner then trueAngular 3 rank 0 else (identity rank 3).smul 0,
    (value rank (startupPlanarEntryMap outer inner)).sub
      ((((value rank (startupPlanarRotatedEntryMap outer 0)).comp (trueInverseTensor rank 0 inner)).add
        ((value rank (startupPlanarRotatedEntryMap outer 1)).comp (trueInverseTensor rank 1 inner))).smul 2)] row

variable {L sigma gamma ell : ℝ}

def embeddedRow (admissible : Admissible L sigma gamma ell) (rank : ℕ)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (row : Fin 3) : StartupRankOperator rank 3 3 :=
  ![(value rank planarInclusionMap).comp (force admissible rank data coherent inverseCoherent),
    (value rank toroidalInclusionMap).comp (third admissible rank data coherent inverseCoherent),
    (value rank planarInclusionMap).comp (principalFlux admissible rank data coherent inverseCoherent)] row

def principalTensor (admissible : Admissible L sigma gamma ell) (rank : ℕ)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (outer inner : Fin 2) : StartupRankOperator rank 3 3 :=
  (((principalFixed rank outer inner 0).comp (embeddedRow admissible rank data coherent inverseCoherent 0)).add
    ((principalFixed rank outer inner 1).comp (embeddedRow admissible rank data coherent inverseCoherent 1))).add
    ((principalFixed rank outer inner 2).comp (embeddedRow admissible rank data coherent inverseCoherent 2))

theorem principalFixed_bound_independent (rank : ℕ) (outer inner : Fin 2) (row : Fin 3) :
    (principalFixed rank outer inner row).bound = (principalFixed 0 outer inner row).bound := by
  fin_cases row
  · rfl
  · change (if outer = inner then trueAngular 3 rank 0 else (identity rank 3).smul 0).bound =
      (if outer = inner then trueAngular 3 0 0 else (identity 0 3).smul 0).bound
    split_ifs <;> rfl
  · rfl

theorem embeddedRow_bound_independent (admissible : Admissible L sigma gamma ell) (rank : ℕ)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (row : Fin 3) :
    (embeddedRow admissible rank data coherent inverseCoherent row).bound =
      (embeddedRow admissible 0 data coherent inverseCoherent row).bound := by fin_cases row <;> rfl

theorem principalTensor_bound_independent (admissible : Admissible L sigma gamma ell) (rank : ℕ)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (outer inner : Fin 2) :
    (principalTensor admissible rank data coherent inverseCoherent outer inner).bound =
      (principalTensor admissible 0 data coherent inverseCoherent outer inner).bound := by
  change ((principalFixed rank outer inner 0).bound * (embeddedRow admissible rank data coherent inverseCoherent 0).bound +
    (principalFixed rank outer inner 1).bound * (embeddedRow admissible rank data coherent inverseCoherent 1).bound) +
    (principalFixed rank outer inner 2).bound * (embeddedRow admissible rank data coherent inverseCoherent 2).bound = _
  simp only [principalFixed_bound_independent, embeddedRow_bound_independent]
  rfl

/-- Both genuine rank operators have the same finite numerical bound selected
at rank zero. No derivative order enters this smallness payment. -/
theorem principalTensor_uniform_bounds (admissible : Admissible L sigma gamma ell) (rank : ℕ)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (outer inner : Fin 2) :
    ‖(principalTensor admissible rank data coherent inverseCoherent outer inner).coarse‖ ≤
        (principalTensor admissible 0 data coherent inverseCoherent outer inner).bound ∧
      ‖(principalTensor admissible rank data coherent inverseCoherent outer inner).fine‖ ≤
        (principalTensor admissible 0 data coherent inverseCoherent outer inner).bound := by
  have same := principalTensor_bound_independent admissible rank data coherent inverseCoherent outer inner
  exact ⟨(principalTensor admissible rank data coherent inverseCoherent outer inner).coarse_bound.trans_eq same,
    (principalTensor admissible rank data coherent inverseCoherent outer inner).fine_bound.trans_eq same⟩

end StartupRankOperator
end Grad.CartesianStartup

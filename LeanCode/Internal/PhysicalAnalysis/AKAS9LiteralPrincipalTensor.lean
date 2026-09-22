import AKAS3TrueInverseTensorKernels

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace Grad.CartesianStartup
open Grad.GenericCarriers Grad.ClosedJets Grad.CartesianState Grad.Constraints.Gauges
open Grad.Constraints Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

/-- The literal planar elementary matrix embedded in the full three-component value. -/
def startupPlanarEntryMap (output input : Fin 2) : OperatorValue 3 3 :=
  planarInclusionMap.comp (((PiLp.proj 2 (fun _ : Fin 2 => ℂ) input).smulRight
    (PiLp.single (β := fun _ : Fin 2 => ℂ) 2 output 1)).comp planarPartMap)

def startupPlanarRotatedEntryMap (output input : Fin 2) : OperatorValue 3 3 :=
  planarInclusionMap.comp (quarterValueMap.comp (((PiLp.proj 2 (fun _ : Fin 2 => ℂ) input).smulRight
    (PiLp.single (β := fun _ : Fin 2 => ℂ) 2 output 1)).comp planarPartMap))

/-- Fixed ER11 tensor factors acting on a,c,s respectively. The curl
 signs, factor minus2 in HodgeDiv, and true angular mean subtraction
 are literal. No variable coefficient derivative has been extracted. -/
def startupPrincipalFixedKernel (outer inner : Fin 2) (row : Fin 3) : StartupL2 3 →L[ℂ] StartupL2 3 :=
  ![(originalValueKernel (startupPlanarRotatedEntryMap outer 1)).comp (startupTrueInverseTensorKernel 0 inner) -
      (originalValueKernel (startupPlanarRotatedEntryMap outer 0)).comp (startupTrueInverseTensorKernel 1 inner),
    if outer = inner then startupTrueAngularInverse 3 0 else 0,
    originalValueKernel (startupPlanarEntryMap outer inner) - (2 : ℂ) •
      ∑ middle : Fin 2, (originalValueKernel (startupPlanarRotatedEntryMap outer middle)).comp
        (startupTrueInverseTensorKernel middle inner)] row

def startupPrincipalFixedFirst (outer inner : Fin 2) (row : Fin 3) : StartupFirst 3 →L[ℂ] StartupFirst 3 :=
  ![(originalValueFirstGraph (startupPlanarRotatedEntryMap outer 1)).comp (startupTrueInverseTensorFirst 0 inner) -
      (originalValueFirstGraph (startupPlanarRotatedEntryMap outer 0)).comp (startupTrueInverseTensorFirst 1 inner),
    if outer = inner then startupTrueAngularFirstGraph 3 0 else 0,
    originalValueFirstGraph (startupPlanarEntryMap outer inner) - (2 : ℂ) •
      ∑ middle : Fin 2, (originalValueFirstGraph (startupPlanarRotatedEntryMap outer middle)).comp
        (startupTrueInverseTensorFirst middle inner)] row

theorem startupPrincipalFixed_compatible (outer inner : Fin 2) (row : Fin 3) :
    StartupCompatible (startupPrincipalFixedKernel outer inner row) (startupPrincipalFixedFirst outer inner row) := by
  fin_cases row
  · exact startupCompatible_sub
      (startupCompatible_comp (originalValueFirstGraph_compatible _) (startupTrueInverseTensor_compatible 0 inner))
      (startupCompatible_comp (originalValueFirstGraph_compatible _) (startupTrueInverseTensor_compatible 1 inner))
  · change StartupCompatible
      (if outer = inner then startupTrueAngularInverse 3 0 else 0)
      (if outer = inner then startupTrueAngularFirstGraph 3 0 else 0)
    by_cases same : outer = inner
    · rw [if_pos same, if_pos same]
      exact startupTrueAngularFirstGraph_compatible 3 0
    · rw [if_neg same, if_neg same]
      intro field
      exact map_zero (Grad.WeightedJets.base 3 1 openUnitDisk (fun _ => 0))
  · exact startupCompatible_sub (originalValueFirstGraph_compatible _)
      (startupCompatible_smul (2 : ℂ) (startupCompatible_sum
        (fun middle : Fin 2 => (originalValueKernel (startupPlanarRotatedEntryMap outer middle)).comp
          (startupTrueInverseTensorKernel middle inner))
        (fun middle : Fin 2 => (originalValueFirstGraph (startupPlanarRotatedEntryMap outer middle)).comp
          (startupTrueInverseTensorFirst middle inner))
        (fun middle : Fin 2 => startupCompatible_comp (originalValueFirstGraph_compatible _)
          (startupTrueInverseTensor_compatible middle inner))))

variable {L sigma gamma ell : ℝ}

/-- SAME actual variable-coefficient tensor before the physical scalar cutoff. -/
def startupActualPrincipalTensorKernel (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (outer inner : Fin 2) : StartupL2 3 →L[ℂ] StartupL2 3 :=
  ∑ row : Fin 3, (startupPrincipalFixedKernel outer inner row).comp
    (startupERKernelRow admissible data coherent inverseCoherent row)

def startupActualPrincipalTensorFirst (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (outer inner : Fin 2) : StartupFirst 3 →L[ℂ] StartupFirst 3 :=
  ∑ row : Fin 3, (startupPrincipalFixedFirst outer inner row).comp
    (startupERFirstRow admissible data coherent inverseCoherent row)

theorem startupActualPrincipalTensor_compatible (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (outer inner : Fin 2) :
    StartupCompatible (startupActualPrincipalTensorKernel admissible data coherent inverseCoherent outer inner)
      (startupActualPrincipalTensorFirst admissible data coherent inverseCoherent outer inner) :=
  startupCompatible_sum
    (fun row : Fin 3 => (startupPrincipalFixedKernel outer inner row).comp
      (startupERKernelRow admissible data coherent inverseCoherent row))
    (fun row : Fin 3 => (startupPrincipalFixedFirst outer inner row).comp
      (startupERFirstRow admissible data coherent inverseCoherent row))
    (fun row : Fin 3 => startupCompatible_comp (startupPrincipalFixed_compatible outer inner row)
      (startupERRow_compatible admissible data coherent inverseCoherent row))

end Grad.CartesianStartup

import AKCO8ActualNativeSignedRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 3000
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets Grad.Constraints Grad.Constraints.Gauges
open Grad.ActualAngularInverse Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Ledger

private theorem signedCellwise_zero (input output : ℕ) :
    StartupCellwise (0 : StartupL2 input →L[ℂ] StartupL2 output) := by
  intro cell
  exact ⟨0,fun _ => by simp⟩

private theorem signedCellwise_trueInverse (dimension : ℕ) (shift : ℤ) :
    StartupCellwise (startupTrueAngularInverse dimension shift) :=
  (startupAngularKernel_cellwise _ _ _).comp
    ((StartupCellwise.id dimension).sub (startupAngularKernel_cellwise _ _ _))

private theorem signedCellwise_inverseTensor (input output : Fin 2) :
    StartupCellwise (startupTrueInverseTensorKernel input output) := by
  unfold startupTrueInverseTensorKernel
  rw [Fin.sum_univ_two]
  exact (startupAngularKernel_cellwise _ _ _).sub
    (((startupAngularKernel_cellwise _ _ _).comp (startupAngularKernel_cellwise _ _ _)).add
      ((startupAngularKernel_cellwise _ _ _).comp (startupAngularKernel_cellwise _ _ _)))

private theorem signedCellwise_principalFixed (outer inner : Fin 2) (row : Fin 3) :
    StartupCellwise (startupPrincipalFixedKernel outer inner row) := by
  fin_cases row
  · exact ((originalValueKernel_cellwise _).comp (signedCellwise_inverseTensor 0 inner)).sub
      ((originalValueKernel_cellwise _).comp (signedCellwise_inverseTensor 1 inner))
  · change StartupCellwise (if outer = inner then startupTrueAngularInverse 3 0 else 0)
    by_cases same : outer = inner
    · rw [if_pos same]
      exact signedCellwise_trueInverse 3 0
    · rw [if_neg same]
      exact signedCellwise_zero 3 3
  · change StartupCellwise (originalValueKernel (startupPlanarEntryMap outer inner) - (2 : ℂ) •
      ∑ middle : Fin 2, (originalValueKernel (startupPlanarRotatedEntryMap outer middle)).comp
        (startupTrueInverseTensorKernel middle inner))
    rw [Fin.sum_univ_two]
    exact (originalValueKernel_cellwise _).sub
      ((((originalValueKernel_cellwise _).comp (signedCellwise_inverseTensor 0 inner)).add
        ((originalValueKernel_cellwise _).comp (signedCellwise_inverseTensor 1 inner))).smul 2)

namespace StartupSignedAction
variable {L sigma gamma ell : ℝ}

def principalFixed (outer inner : Fin 2) (row : Fin 3) : StartupSignedAction 3 3 L ell :=
  fixed (startupPrincipalFixedKernel outer inner row) (startupPrincipalFixedFirst outer inner row)
    (startupPrincipalFixed_compatible outer inner row) (signedCellwise_principalFixed outer inner row)

variable (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell)
    (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))

def principalTensor (outer inner : Fin 2) : StartupSignedAction 3 3 L ell :=
  (((principalFixed outer inner 0).comp
    ((value planarInclusionMap).comp (force admissible data coherent inverseCoherent))).add
    ((principalFixed outer inner 1).comp
      ((value toroidalInclusionMap).comp (third admissible data coherent inverseCoherent)))).add
    ((principalFixed outer inner 2).comp
      ((value planarInclusionMap).comp (principalFlux admissible data coherent inverseCoherent)))

theorem principalTensor_coarse (outer inner : Fin 2) :
    (principalTensor admissible data coherent inverseCoherent outer inner).coarse =
      startupGenuinePrincipalTensorKernel admissible data coherent inverseCoherent outer inner := by
  unfold startupGenuinePrincipalTensorKernel
  rw [Fin.sum_univ_three]
  rfl

/-- The literal original current/force/cofactor composition has a signed
leading split with an actual first graph for the lower remainder. The
highest input power remains entirely under the unchanged principal tensor. -/
theorem actualPrincipal_signedLeadingFirst (family : StartupSignedFamily 3 L ell)
    (power : ℕ) (lower : ∀ q < power, ∃ graph : StartupFirst 3,
      base 3 1 openUnitDisk (fun _ => 0) graph = family.moment q)
    (outer inner : Fin 2) :
    ∃ remainder : StartupFirst 3,
      ((principalTensor admissible data coherent inverseCoherent outer inner).action family).moment power =
        startupGenuinePrincipalTensorKernel admissible data coherent inverseCoherent outer inner (family.moment power) +
          base 3 1 openUnitDisk (fun _ => 0) remainder := by
  obtain ⟨remainder,same⟩ := (principalTensor admissible data coherent inverseCoherent outer inner).lowerRemainder
    family power lower
  rw [principalTensor_coarse] at same
  exact ⟨remainder,by rw [same]; abel⟩

end StartupSignedAction
end Grad.CartesianStartup

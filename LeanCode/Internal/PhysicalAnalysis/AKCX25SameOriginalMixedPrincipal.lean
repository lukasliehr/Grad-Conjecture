import AKCX24ActualPrincipalMixedLeading

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxRecDepth 3000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.WeightedJets Grad.WeightedJets.Ordered
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
namespace StartupSignedFamily
variable {dimension rank : ℕ} {L ell : ℝ}

theorem moment_congr_of_field (first second : StartupSignedFamily dimension L ell)
    (same : first.field = second.field) (power : ℕ) : first.moment power = second.moment power := by
  apply Grad.CellWeights.fields_ext dimension openUnitDisk
  intro cell
  rw [first.projection,second.projection,same]

theorem HasSpatialGrade.congr {first second : StartupSignedFamily dimension L ell}
    (regular : first.HasSpatialGrade rank) (same : first.field = second.field) : second.HasSpatialGrade rank := by
  intro power weight
  obtain ⟨graph,graphSame⟩ := regular power weight
  exact ⟨graph,graphSame.trans (first.moment_congr_of_field second same power)⟩

theorem rankDerivative_congr (first second : StartupSignedFamily dimension L ell)
    (one : first.HasSpatialGrade rank) (two : second.HasSpatialGrade rank)
    (same : first.field = second.field) (power : ℕ) : first.rankDerivative one power = second.rankDerivative two power := by
  exact second.rankDerivative_of_graph two power (one power 0).choose le_rfl
    ((one power 0).choose_spec.trans (first.moment_congr_of_field second same power))

end StartupSignedFamily
namespace StartupSignedAction
variable {L sigma gamma ell : ℝ}
variable (admissible : Admissible L sigma gamma ell) (rank : ℕ)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (lengthNonzero : L ≠ 0) (scaleNonzero : ell ≠ 0)
include lengthNonzero scaleNonzero

theorem actualPrincipal_spatialFamily_same (family : StartupSignedFamily 3 L ell) (outer inner : Fin 2) :
    ((StartupSpatialAction.principalTensor admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero outer inner).signed.action family).field =
      ((principalTensor admissible data coherent inverseCoherent outer inner).action family).field := by
  rw [StartupSignedAction.sameField,StartupSignedAction.sameField,
    StartupSpatialAction.principalTensor_coarse,principalTensor_coarse]

/-- Every spatial grade of the actual signed principal output retains all
natural cell reserves, for the exact representatives used by CO's native
weak equation. -/
theorem actualPrincipal_allWeightSpatial (family : StartupSignedFamily 3 L ell)
    (regular : family.HasSpatialGrade rank) (outer inner : Fin 2) :
    ((principalTensor admissible data coherent inverseCoherent outer inner).action family).HasSpatialGrade rank :=
  ((StartupSpatialAction.principalTensor admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero outer inner).preserves
    rank family regular).congr
    (actualPrincipal_spatialFamily_same admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero family outer inner)

/-- Exact mixed leading identity for the SAME original signed principal
family in the native ER equation, with the unchanged accepted BW rank
operator. Only the explicit nested induction lower data are used. -/
theorem actualPrincipal_mixedRankFirst (family : StartupSignedFamily 3 L ell)
    (regular : family.HasSpatialGrade rank) (power : ℕ)
    (lower : ∀ q < power, ∃ first : StartupFirst (startupTensorDimension 3 rank),
      base (startupTensorDimension 3 rank) 1 openUnitDisk (fun _ => 0) first = family.rankDerivative regular q)
    (outer inner : Fin 2) :
    ∃ remainder : StartupFirst (startupTensorDimension 3 rank),
      ((principalTensor admissible data coherent inverseCoherent outer inner).action family).rankDerivative
        (actualPrincipal_allWeightSpatial admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero family regular outer inner) power =
      (StartupRankOperator.principalTensor admissible rank data coherent inverseCoherent outer inner).coarse
        (family.rankDerivative regular power) +
      base (startupTensorDimension 3 rank) 1 openUnitDisk (fun _ => 0) remainder := by
  obtain ⟨remainder,equation⟩ := StartupSpatialAction.actualPrincipal_mixedLeadingFirst admissible rank data coherent inverseCoherent
    lengthNonzero scaleNonzero family regular power lower outer inner
  have sameDerivative := StartupSignedFamily.rankDerivative_congr
    ((StartupSpatialAction.principalTensor admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero outer inner).signed.action family)
    ((principalTensor admissible data coherent inverseCoherent outer inner).action family)
    ((StartupSpatialAction.principalTensor admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero outer inner).preserves rank family regular)
    (actualPrincipal_allWeightSpatial admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero family regular outer inner)
    (actualPrincipal_spatialFamily_same admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero family outer inner) power
  rw [sameDerivative] at equation
  exact ⟨remainder,equation⟩

end StartupSignedAction
end Grad.CartesianStartup

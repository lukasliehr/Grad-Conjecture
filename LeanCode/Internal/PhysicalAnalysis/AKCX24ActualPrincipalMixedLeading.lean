import AKCX23ActualMixedPrimitiveActions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxRecDepth 3000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap Grad.Constraints Grad.Constraints.Gauges
open Grad.WeightedJets
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
namespace StartupSpatialAction
variable {L sigma gamma ell : ℝ}
variable (admissible : Admissible L sigma gamma ell) (rank : ℕ)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (lengthNonzero : L ≠ 0) (scaleNonzero : ell ≠ 0)

theorem current_mixed :
    (current admissible rank data.gaugeDeviation coherent.2.2.2.1 inverseCoherent lengthNonzero scaleNonzero).HasMixedLeading :=
  (identity_mixed rank 3).sub
    ((matrix_mixed admissible rank (complementExtensionFamily admissible data.gaugeDeviation)
      (complementExtensionFamily_coherent admissible data.gaugeDeviation coherent.2.2.2.1 inverseCoherent) lengthNonzero scaleNonzero).comp
      ((complement_mixed rank).comp
        (matrix_mixed admissible rank (fullGaugeFamily data.gaugeDeviation)
          (fullGaugeFamily_coherent data.gaugeDeviation coherent.2.2.2.1) lengthNonzero scaleNonzero)))

theorem force_mixed :
    (force admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero).HasMixedLeading :=
  ((radial_mixed rank).comp
    ((matrix_mixed admissible rank data.rotatedPlanarProduct coherent.2.2.2.2.2.2.2.1 lengthNonzero scaleNonzero).comp
      (current_mixed admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero))).smul 2

theorem third_mixed :
    (third admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero).HasMixedLeading :=
  ((scalarMeanFree_mixed rank).comp
    ((matrix_mixed admissible rank data.rotatedThirdProduct coherent.2.2.2.2.2.2.2.2 lengthNonzero scaleNonzero).comp
      (current_mixed admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero))).smul 2

theorem flux_mixed :
    (flux admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero).HasMixedLeading :=
  (matrix_mixed admissible rank data.fluxDeviation coherent.2.2.2.2.1 lengthNonzero scaleNonzero).comp
    (current_mixed admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero)

theorem planarFlux_mixed :
    (planarFlux admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero).HasMixedLeading :=
  (planarMeanFree_mixed rank).comp ((value_mixed rank planarPartMap).comp
    (flux_mixed admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero))

theorem scalarFlux_mixed :
    (scalarFlux admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero).HasMixedLeading :=
  (scalarMeanFree_mixed rank).comp ((value_mixed rank toroidalPartMap).comp
    (flux_mixed admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero))

theorem principalFlux_mixed :
    (principalFlux admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero).HasMixedLeading :=
  (planarFlux_mixed admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero).sub
    (((value_mixed rank quarterValueMap).comp ((average_mixed rank).comp
      (force_mixed admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero))).smul (1/2))

theorem embeddedRow_mixed (row : Fin 3) :
    (embeddedRow admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero row).HasMixedLeading := by
  fin_cases row
  · exact (value_mixed rank planarInclusionMap).comp (force_mixed admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero)
  · exact (value_mixed rank toroidalInclusionMap).comp (third_mixed admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero)
  · exact (value_mixed rank planarInclusionMap).comp (principalFlux_mixed admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero)

theorem principalTensor_mixed (outer inner : Fin 2) :
    (principalTensor admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero outer inner).HasMixedLeading :=
  (((principalFixed_mixed rank outer inner 0).comp
    (embeddedRow_mixed admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero 0)).add
    ((principalFixed_mixed rank outer inner 1).comp
      (embeddedRow_mixed admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero 1))).add
    ((principalFixed_mixed rank outer inner 2).comp
      (embeddedRow_mixed admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero 2))

/-- The complete literal principal composition now closes the joint
spatial/axial leading split with exactly the nested induction premises. -/
theorem actualPrincipal_mixedLeadingFirst
    (family : StartupSignedFamily 3 L ell) (regular : family.HasSpatialGrade rank) (power : ℕ)
    (lower : ∀ q < power, ∃ first : StartupFirst (startupTensorDimension 3 rank),
      base (startupTensorDimension 3 rank) 1 openUnitDisk (fun _ => 0) first = family.rankDerivative regular q)
    (outer inner : Fin 2) :
    ∃ remainder : StartupFirst (startupTensorDimension 3 rank),
      ((principalTensor admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero outer inner).signed.action family).rankDerivative
        ((principalTensor admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero outer inner).preserves rank family regular) power =
      (StartupRankOperator.principalTensor admissible rank data coherent inverseCoherent outer inner).coarse
        (family.rankDerivative regular power) +
      base (startupTensorDimension 3 rank) 1 openUnitDisk (fun _ => 0) remainder := by
  obtain ⟨remainder,equation⟩ := principalTensor_mixed admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero
    outer inner family regular power lower
  rw [principalTensor_ranked] at equation
  exact ⟨remainder,equation⟩

end StartupSpatialAction
end Grad.CartesianStartup

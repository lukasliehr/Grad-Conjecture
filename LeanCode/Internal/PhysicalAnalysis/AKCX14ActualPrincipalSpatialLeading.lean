import AKCX13ActualCurrentSpatialComposition

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxRecDepth 3000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap Grad.Constraints Grad.Constraints.Gauges
open Grad.WeightedJets Grad.WeightedJets.Ordered
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
namespace StartupSpatialAction
variable {L sigma gamma ell : ℝ}
variable (admissible : Admissible L sigma gamma ell) (rank : ℕ)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (lengthNonzero : L ≠ 0) (scaleNonzero : ell ≠ 0)

def embeddedRow (row : Fin 3) : StartupSpatialAction rank 3 3 L ell :=
  ![(value rank planarInclusionMap).comp (force admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero),
    (value rank toroidalInclusionMap).comp (third admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero),
    (value rank planarInclusionMap).comp (principalFlux admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero)] row

def principalTensor (outer inner : Fin 2) : StartupSpatialAction rank 3 3 L ell :=
  (((principalFixed rank outer inner 0).comp (embeddedRow admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero 0)).add
    ((principalFixed rank outer inner 1).comp (embeddedRow admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero 1))).add
    ((principalFixed rank outer inner 2).comp (embeddedRow admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero 2))

theorem embeddedRow_ranked (row : Fin 3) :
    (embeddedRow admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero row).ranked =
      StartupRankOperator.embeddedRow admissible rank data coherent inverseCoherent row := by fin_cases row <;> rfl

theorem principalTensor_ranked (outer inner : Fin 2) :
    (principalTensor admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero outer inner).ranked =
      StartupRankOperator.principalTensor admissible rank data coherent inverseCoherent outer inner := by
  change (((principalFixed rank outer inner 0).ranked.comp
    (embeddedRow admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero 0).ranked).add
    ((principalFixed rank outer inner 1).ranked.comp
      (embeddedRow admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero 1).ranked)).add
    ((principalFixed rank outer inner 2).ranked.comp
      (embeddedRow admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero 2).ranked) = _
  rw [principalFixed_ranked,principalFixed_ranked,principalFixed_ranked,embeddedRow_ranked,embeddedRow_ranked,embeddedRow_ranked]
  rfl

theorem principalTensor_coarse (outer inner : Fin 2) :
    (principalTensor admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero outer inner).signed.coarse =
      startupGenuinePrincipalTensorKernel admissible data coherent inverseCoherent outer inner := by
  change ((principalFixed rank outer inner 0).signed.coarse.comp
    (originalValueKernel planarInclusionMap |>.comp (force admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero).signed.coarse) +
    (principalFixed rank outer inner 1).signed.coarse.comp
      (originalValueKernel toroidalInclusionMap |>.comp (third admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero).signed.coarse)) +
    (principalFixed rank outer inner 2).signed.coarse.comp
      (originalValueKernel planarInclusionMap |>.comp (principalFlux admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero).signed.coarse) = _
  rw [principalFixed_coarse,principalFixed_coarse,principalFixed_coarse,force_coarse,third_coarse,principalFlux_coarse]
  unfold startupGenuinePrincipalTensorKernel
  rw [Fin.sum_univ_three]
  rfl

include lengthNonzero scaleNonzero in
/-- The SAME original current/force/cofactor composition has the exact BW
principal rank operator as its spatial leading term. Every genuinely
nonempty coefficient allocation is paid from completed lower derivatives;
there is no regularity premise for the top derivative. -/
theorem actualPrincipal_spatialLeadingFirst
    (family : StartupSignedFamily 3 L ell) (regular : family.HasSpatialGrade rank)
    (field : GraphGrade 3 rank 0 openUnitDisk)
    (fieldSame : base 3 rank openUnitDisk (fun _ => 0) field = family.field)
    (image : GraphGrade 3 rank 0 openUnitDisk) (outer inner : Fin 2)
    (imageSame : base 3 rank openUnitDisk (fun _ => 0) image =
      startupGenuinePrincipalTensorKernel admissible data coherent inverseCoherent outer inner family.field) :
    ∃ remainder : StartupFirst (startupTensorDimension 3 rank),
      startupTensorFieldEquiv 3 rank
        (orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl image) =
      (StartupRankOperator.principalTensor admissible rank data coherent inverseCoherent outer inner).coarse
        (startupTensorFieldEquiv 3 rank
          (orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl field)) +
      base (startupTensorDimension 3 rank) 1 openUnitDisk (fun _ => 0) remainder := by
  let operator := principalTensor admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero outer inner
  have coarseSame := principalTensor_coarse admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero outer inner
  have rankedSame := principalTensor_ranked admissible rank data coherent inverseCoherent lengthNonzero scaleNonzero outer inner
  have same : base 3 rank openUnitDisk (fun _ => 0) image = operator.signed.coarse family.field := by
    rw [coarseSame]
    exact imageSame
  obtain ⟨remainder,equation⟩ := operator.leading family regular field fieldSame image same
  rw [rankedSame] at equation
  exact ⟨remainder,equation⟩

end StartupSpatialAction
end Grad.CartesianStartup

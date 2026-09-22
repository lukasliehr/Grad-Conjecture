import AKCX45HigherGraphRankFirst
import AKCX43SameSignedCompactSpatialEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 3000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.WeightedJets.Ordered Grad.TensorBootstrap
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

/-- The SAME localized and differentiated full ER tensor has the actual
rank principal operator as leading term. Source and all nonleading allocations form a genuine first graph. -/
theorem startupSame_localizedPrincipal_rankLeading {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (ledger : LedgerData L sigma gamma ell) (coherent : LedgerCoherent ledger)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.gaugeDeviation))
    (lengthNonzero : L ≠ 0) (scaleNonzero : ell ≠ 0)
    (cutoff : Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff) (compact : HasCompactSupport cutoff)
    (radial : ∀ first second : Spatial, ‖first‖ = ‖second‖ → cutoff first = cutoff second)
    (rank : ℕ) (family : StartupSignedFamily 3 L ell) (regular : family.HasSpatialGrade rank)
    (known : Fin 2 → Fin 2 → StartupSignedFirstFamily 3 L ell)
    (knownRegular : ∀ outer inner order, (known outer inner).toStartupSignedFamily.HasSpatialGrade order)
    (power : ℕ)
    (lower : ∀ q < power, ∃ first : StartupFirst (startupTensorDimension 3 rank),
      base (startupTensorDimension 3 rank) 1 openUnitDisk (fun _ => 0) first =
        (family.spatialCutoff cutoff smooth compact).rankDerivative (regular.spatialCutoff cutoff smooth compact) q)
    (data : StartupCompactSpatialEquation rank (tsupport cutoff))
    (fieldSame : base 3 rank openUnitDisk (fun _ => 0) data.field = startupCutoffL2 cutoff smooth compact (family.moment power))
    (tensorSame : ∀ outer inner, base 3 rank openUnitDisk (fun _ => 0) (data.tensor outer inner) =
      startupCutoffL2 cutoff smooth compact ((startupSignedFullTensor admissible ledger coherent inverseCoherent family known outer inner).moment power))
    (outer inner : Fin 2) :
    ∃ remainder : StartupFirst (startupTensorDimension 3 rank),
      startupTensorFieldEquiv 3 rank (orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl (data.tensor outer inner)) =
        (StartupRankOperator.principalTensor admissible rank ledger coherent inverseCoherent outer inner).coarse
          (startupTensorFieldEquiv 3 rank (orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl data.field))+
        base (startupTensorDimension 3 rank) 1 openUnitDisk (fun _ => 0) remainder := by
  let cut := family.spatialCutoff cutoff smooth compact
  have cutRegular : cut.HasSpatialGrade rank := regular.spatialCutoff cutoff smooth compact
  let source := (known outer inner).toStartupSignedFamily.spatialCutoff cutoff smooth compact
  have sourceRegular : source.HasSpatialGrade rank := (knownRegular outer inner rank).spatialCutoff cutoff smooth compact
  have sourceHigher : source.HasSpatialGrade (rank+1) := (knownRegular outer inner (rank+1)).spatialCutoff cutoff smooth compact
  let principal := (StartupSignedAction.principalTensor admissible ledger coherent inverseCoherent outer inner).action cut
  have principalRegular : principal.HasSpatialGrade rank := StartupSignedAction.actualPrincipal_allWeightSpatial admissible rank ledger coherent inverseCoherent
    lengthNonzero scaleNonzero cut cutRegular outer inner
  have sameFields : ((startupSignedFullTensor admissible ledger coherent inverseCoherent family known outer inner).spatialCutoff cutoff smooth compact).field =
      (principal.add source).field := by
    change startupCutoffL2 cutoff smooth compact
      (((StartupSignedAction.principalTensor admissible ledger coherent inverseCoherent outer inner).action family).field+(known outer inner).field) =
      ((StartupSignedAction.principalTensor admissible ledger coherent inverseCoherent outer inner).action cut).field+
        startupCutoffL2 cutoff smooth compact (known outer inner).field
    rw [StartupSignedAction.sameField,StartupSignedAction.sameField,StartupSignedAction.principalTensor_coarse,map_add]
    rw [← startupGenuinePrincipalTensor_cutoff admissible ledger coherent inverseCoherent cutoff smooth compact radial family.field outer inner]
    rfl
  have sameMoment := StartupSignedFamily.moment_congr_of_field _ _ sameFields power
  have imageSame : base 3 rank openUnitDisk (fun _ => 0) (data.tensor outer inner) = (principal.add source).moment power :=
    (tensorSame outer inner).trans sameMoment
  have derivativeSame := (principal.add source).rankDerivative_of_graph (principalRegular.add sourceRegular) power (data.tensor outer inner) le_rfl imageSame
  rw [StartupSignedFamily.rankDerivative_add principal source principalRegular sourceRegular power] at derivativeSame
  obtain ⟨principalRemainder,principalSame⟩ := StartupSignedAction.actualPrincipal_mixedRankFirst admissible rank ledger coherent inverseCoherent
    lengthNonzero scaleNonzero cut cutRegular power lower outer inner
  obtain ⟨sourceFirst,sourceSame⟩ := source.rankDerivative_firstOfHigher sourceRegular power (sourceHigher power 0)
  have fieldDerivative := cut.rankDerivative_of_graph cutRegular power data.field le_rfl fieldSame
  refine ⟨principalRemainder+sourceFirst,?_⟩
  rw [derivativeSame,principalSame,← sourceSame,← fieldDerivative,map_add]
  exact add_assoc _ _ _

end Grad.CartesianStartup

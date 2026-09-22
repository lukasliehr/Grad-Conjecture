import AKCX3LowerOrderedWeightedFirst
import AKCG10ActualAxialLeadingSplit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open MeasureTheory
open scoped BigOperators ContDiff
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.RepresentedKernel Grad.RepresentedKernel.WeakDerivatives Grad.RepresentedKernel.SpatialProduct
open Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation

/-- Every nonempty spatial coefficient allocation is an actual first
graph. Its input is a strictly lower complementary derivative, and its
frequency reserve is paid from the already available weighted grade. -/
theorem startupMatrixSpatialAllocation_first {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output order rank weight : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (word : Word rank) (bound : rank ≤ order) (reserve : rank ≤ weight)
    (field : GraphGrade input order weight openUnitDisk) (selected : Finset (Fin rank))
    (nonempty : selected ∈ (Finset.univ : Finset (Finset (Fin rank))).erase ∅) :
    ∃ graph : StartupFirst output, base output 1 openUnitDisk (fun _ => 0) graph =
      startupDerivativeKernel admissible family coherent (startupSelectedCoefficientIndex word selected)
        (startupReservedDerivative admissible (startupSelectedCoefficientIndex_reserve word selected (by omega))
          (startupComplementIndex word bound selected) field) := by
  have lowerRank := (startupMatrixRemainder_lowerRank selected nonempty).2
  obtain ⟨lower,lowerSame⟩ := startupOrderedDerivative_firstWeighted field
    (show selectedᶜ.card+1 ≤ order from by omega) (subword word selectedᶜ)
  have selectedBound : selected.card ≤ rank := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ selected
  have coefficientOrder : cartesianOrder (selectedIndex word selected) = selected.card :=
    word_direction_count_total selected.card (subword word selected)
  have paid : cartesianOrder (selectedIndex word selected) + 1 - 1 ≤ weight := by
    rw [coefficientOrder]
    omega
  let graph := startupDisplacementMatrixGraph admissible family coherent
    (selectedIndex word selected) 0 paid lower
  refine ⟨graph,?_⟩
  rw [startupDisplacementMatrixGraph_base,startupDisplacementKernel_zero]
  have indexSame : derivativeMultiIndex (startupShiftedIndex (selectedIndex word selected) (0,0)) =
      derivativeMultiIndex (startupSelectedCoefficientIndex word selected) := by
    rw [startupShiftedIndex_zero,startupSelectedCoefficientIndex_multi]
  have orderSame : derivativeOrder (startupShiftedIndex (selectedIndex word selected) (0,0)) =
      derivativeOrder (startupSelectedCoefficientIndex word selected) :=
    congrArg (fun pair : ℕ × ℕ => pair.1+pair.2) indexSame
  have inputSame :
      startupReservedDerivative admissible (startupShiftedZero_reserve (selectedIndex word selected) paid)
        (zeroIndex 1) lower =
      startupReservedDerivative admissible (startupSelectedCoefficientIndex_reserve word selected (by omega))
        (startupComplementIndex word bound selected) field := by
    have recovered : Realization.recoveredDerivative input 1 openUnitDisk (fun _ => weight) (zeroIndex 1) lower =
        Realization.recoveredDerivative input order openUnitDisk (fun _ => weight)
          (startupComplementIndex word bound selected) field := by
      rw [Realization.recoveredDerivative_zero,lowerSame,orderedDerivative_apply]
      rfl
    apply startupField_ae_ext
    filter_upwards [startupReservedDerivative_ae admissible
      (startupShiftedZero_reserve (selectedIndex word selected) paid) (zeroIndex 1) lower,
      startupReservedDerivative_ae admissible
        (startupSelectedCoefficientIndex_reserve word selected (show rank-1 ≤ weight from by omega))
        (startupComplementIndex word bound selected) field] with point left right
    intro cell
    rw [left cell,right cell,orderSame,recovered]
  rw [inputSame,startupDerivativeKernel_multi_congr admissible family coherent _ _ indexSame]

/-- The actual full spatial matrix remainder has a first graph using only
the available input spatial order. No top derivative first graph occurs
among the premises. -/
theorem startupMatrixOrderedRemainder_first {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output order rank weight : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (word : Word rank) (bound : rank ≤ order) (reserve : rank ≤ weight)
    (field : GraphGrade input order weight openUnitDisk) :
    ∃ graph : StartupFirst output, base output 1 openUnitDisk (fun _ => 0) graph =
      startupMatrixOrderedRemainder admissible family coherent word bound (by omega) field := by
  classical
  let selectedSets := (Finset.univ : Finset (Finset (Fin rank))).erase ∅
  have each := fun selected (member : selected ∈ selectedSets) =>
    startupMatrixSpatialAllocation_first admissible family coherent word bound reserve field selected member
  choose graphs same using each
  refine ⟨∑ selected ∈ selectedSets.attach, graphs selected.val selected.property,?_⟩
  simp only [map_sum,same]
  simpa only [startupMatrixOrderedRemainder,selectedSets] using
    (Finset.sum_attach selectedSets (fun selected : Finset (Fin rank) =>
      startupDerivativeKernel admissible family coherent (startupSelectedCoefficientIndex word selected)
        (startupReservedDerivative admissible (startupSelectedCoefficientIndex_reserve word selected (show rank-1 ≤ weight from by omega))
          (startupComplementIndex word bound selected) field)))

end Grad.CartesianStartup

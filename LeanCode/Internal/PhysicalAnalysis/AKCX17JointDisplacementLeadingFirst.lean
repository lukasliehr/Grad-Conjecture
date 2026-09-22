import AKCX16JointDisplacementWeakAllocation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory
open scoped BigOperators ContDiff
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.RepresentedKernel Grad.RepresentedKernel.WeakDerivatives Grad.RepresentedKernel.SpatialProduct
open Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation

theorem startupDisplacement_emptyAllocation {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output order rank weight : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (power : ℕ) (word : Word rank) (bound : rank ≤ order) (reserve : rank - 1 ≤ weight)
    (field : GraphGrade input order weight openUnitDisk) :
    startupDisplacementKernel admissible family coherent (startupSelectedCoefficientIndex word ∅) power
      (startupReservedDerivative admissible (startupSelectedCoefficientIndex_reserve word ∅ reserve)
        (startupComplementIndex word bound ∅) field) =
      startupDisplacementKernel admissible family coherent zeroDerivativeIndex power
        (orderedDerivative input order rank openUnitDisk (fun _ => weight) bound field word) := by
  have indexSame : derivativeMultiIndex (startupSelectedCoefficientIndex word ∅) = derivativeMultiIndex zeroDerivativeIndex := by
    rw [startupSelectedCoefficientIndex_multi, startupEmpty_selectedIndex]
    rfl
  have inputSame : startupReservedDerivative admissible (startupSelectedCoefficientIndex_reserve word ∅ reserve)
      (startupComplementIndex word bound ∅) field =
      orderedDerivative input order rank openUnitDisk (fun _ => weight) bound field word := by
    have noReserve : derivativeOrder (startupSelectedCoefficientIndex word ∅) - 1 = 0 := by
      rw [startupSelectedCoefficientIndex_order]
      rfl
    have realized := startupReservedDerivative_ae admissible
      (startupSelectedCoefficientIndex_reserve word ∅ reserve) (startupComplementIndex word bound ∅) field
    have recovered : Realization.recoveredDerivative input order openUnitDisk (fun _ => weight)
      (startupComplementIndex word bound ∅) field =
      orderedDerivative input order rank openUnitDisk (fun _ => weight) bound field word := by
      rw [← startupInputDerivative_recovered]
      rw [startupFull_subword]
      exact startupEmpty_inputDerivative bound field word
    apply startupField_ae_ext
    filter_upwards [realized] with point same
    intro cell
    rw [same cell, noReserve, pow_zero, Complex.ofReal_one, one_smul, recovered]
  rw [startupDisplacementKernel_multi_congr admissible family coherent _ _ indexSame power, inputSame]


def startupDisplacementOrderedRemainder {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output order rank weight : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (power : ℕ) (word : Word rank) (bound : rank ≤ order) (reserve : rank-1 ≤ weight)
    (field : GraphGrade input order weight openUnitDisk) : StartupL2 output :=
  ∑ selected ∈ (Finset.univ : Finset (Finset (Fin rank))).erase ∅,
    startupDisplacementKernel admissible family coherent (startupSelectedCoefficientIndex word selected) power
      (startupReservedDerivative admissible (startupSelectedCoefficientIndex_reserve word selected reserve)
        (startupComplementIndex word bound selected) field)

theorem startupDisplacement_weakLeadingSplit {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output order rank weight : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (power : ℕ) (word : Word rank) (bound : rank ≤ order) (reserve : rank-1 ≤ weight)
    (field : GraphGrade input order weight openUnitDisk) :
    HasWeakOrderedDerivative output openUnitDisk rank word
      (startupDisplacementKernel admissible family coherent zeroDerivativeIndex power
        (base input order openUnitDisk (fun _ => weight) field))
      (startupDisplacementKernel admissible family coherent zeroDerivativeIndex power
        (orderedDerivative input order rank openUnitDisk (fun _ => weight) bound field word) +
        startupDisplacementOrderedRemainder admissible family coherent power word bound reserve field) := by
  classical
  have actual := startupDisplacement_orderedWeak admissible family coherent power word bound reserve field
  let term := fun selected : Finset (Fin rank) =>
    startupDisplacementKernel admissible family coherent (startupSelectedCoefficientIndex word selected) power
      (startupReservedDerivative admissible (startupSelectedCoefficientIndex_reserve word selected reserve)
        (startupComplementIndex word bound selected) field)
  have split := Finset.sum_erase_add (s := (Finset.univ : Finset (Finset (Fin rank)))) term (Finset.mem_univ ∅)
  change startupDisplacementOrderedRemainder admissible family coherent power word bound reserve field + term ∅ = _ at split
  have zero := startupDisplacement_emptyAllocation admissible family coherent power word bound reserve field
  change term ∅ = _ at zero
  rw [zero,add_comm] at split
  rw [← split] at actual
  exact actual

theorem startupDisplacementOrderedRemainder_first {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output order rank weight : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (power : ℕ) (word : Word rank) (bound : rank ≤ order) (reserve : rank ≤ weight)
    (field : GraphGrade input order weight openUnitDisk) :
    ∃ graph : StartupFirst output, base output 1 openUnitDisk (fun _ => 0) graph =
      startupDisplacementOrderedRemainder admissible family coherent power word bound (by omega) field := by
  classical
  let selectedSets := (Finset.univ : Finset (Finset (Fin rank))).erase ∅
  have each := fun selected (member : selected ∈ selectedSets) =>
    startupDisplacementSpatialAllocation_first admissible family coherent power word bound reserve field selected member
  choose graphs same using each
  refine ⟨∑ selected ∈ selectedSets.attach, graphs selected.val selected.property,?_⟩
  simp only [map_sum,same]
  simpa only [startupDisplacementOrderedRemainder,selectedSets] using
    (Finset.sum_attach selectedSets (fun selected : Finset (Fin rank) =>
      startupDisplacementKernel admissible family coherent (startupSelectedCoefficientIndex word selected) power
        (startupReservedDerivative admissible (startupSelectedCoefficientIndex_reserve word selected (show rank-1 ≤ weight from by omega))
          (startupComplementIndex word bound selected) field)))

end Grad.CartesianStartup

import AKCG5ActualMatrixLeadingAllocation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open MeasureTheory
open scoped BigOperators ContDiff
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.RepresentedKernel Grad.RepresentedKernel.WeakDerivatives Grad.RepresentedKernel.SpatialProduct
open Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation

def startupMatrixOrderedRemainder {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output order rank weight : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (word : Word rank) (bound : rank ≤ order) (reserve : rank - 1 ≤ weight)
    (field : GraphGrade input order weight openUnitDisk) : StartupL2 output :=
  ∑ selected ∈ (Finset.univ : Finset (Finset (Fin rank))).erase ∅,
    startupDerivativeKernel admissible family coherent (startupSelectedCoefficientIndex word selected)
      (startupReservedDerivative admissible (startupSelectedCoefficientIndex_reserve word selected reserve)
        (startupComplementIndex word bound selected) field)

/-- Exact full-cell Leibniz split. The principal part is the original
matrix on the top input derivative. Every remainder differentiates the
coefficient at least once and uses the strictly lower complementary word. -/
theorem startupActualMatrix_weakLeadingSplit {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output order rank weight : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (word : Word rank) (bound : rank ≤ order) (reserve : rank - 1 ≤ weight)
    (field : GraphGrade input order weight openUnitDisk) :
    HasWeakOrderedDerivative output openUnitDisk rank word
      (originalMatrixKernel admissible family coherent (base input order openUnitDisk (fun _ => weight) field))
      (originalMatrixKernel admissible family coherent
        (orderedDerivative input order rank openUnitDisk (fun _ => weight) bound field word) +
        startupMatrixOrderedRemainder admissible family coherent word bound reserve field) := by
  classical
  have actual := startupActualMatrix_orderedWeak admissible family coherent word bound reserve field
  let term := fun selected : Finset (Fin rank) =>
    startupDerivativeKernel admissible family coherent (startupSelectedCoefficientIndex word selected)
      (startupReservedDerivative admissible (startupSelectedCoefficientIndex_reserve word selected reserve)
        (startupComplementIndex word bound selected) field)
  have split := Finset.sum_erase_add (s := (Finset.univ : Finset (Finset (Fin rank)))) term (Finset.mem_univ ∅)
  change startupMatrixOrderedRemainder admissible family coherent word bound reserve field + term ∅ = _ at split
  have zero := startupActualMatrix_emptyAllocation admissible family coherent word bound reserve field
  change term ∅ = _ at zero
  rw [zero, add_comm] at split
  rw [← split] at actual
  exact actual

theorem startupMatrixRemainder_lowerRank {rank : ℕ} (selected : Finset (Fin rank))
    (member : selected ∈ (Finset.univ : Finset (Finset (Fin rank))).erase ∅) :
    selected.Nonempty ∧ selectedᶜ.card < rank := by
  have nonempty : selected.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp member).1
  refine ⟨nonempty, ?_⟩
  have sum := Finset.card_add_card_compl selected
  rw [Fintype.card_fin] at sum
  have positive := Finset.card_pos.mpr nonempty
  omega

end Grad.CartesianStartup

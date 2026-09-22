import AKCB2RestoredInputCellReserve

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.RepresentedKernel Grad.RepresentedKernel.WeakDerivatives Grad.RepresentedKernel.SpatialProduct

/-- The full derivative kernel's frequency normalization is cancelled
by a reserve on its input cell, before any Fourier mixing. -/
theorem startupActualEntry_reserved {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension order weight : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (coefficientIndex : DerivativeIndex grade)
    (bound : derivativeOrder coefficientIndex - 1 ≤ weight) (fieldIndex : JetIndex order)
    (jet : GraphGrade inputDimension order weight openUnitDisk) (output input : ℤ) :
    operator (startupSingleEntryData
      (startupConjugatedCoefficientJet admissible family coherent input (output-input)) output input)
      (derivativeMultiIndex coefficientIndex) 0
      (Realization.recoveredDerivative inputDimension order openUnitDisk (fun _ => weight) fieldIndex jet) =
    Grad.FullCellKernel.insertCell outputDimension openUnitDisk output
      (Grad.FullCellKernel.entry (startupDerivativeKernelData admissible family coherent coefficientIndex) output input
        (fieldCellProjection inputDimension openUnitDisk input
          (startupReservedDerivative admissible bound fieldIndex jet))) := by
  have positive : 0 < scaledCellWeight L ell input ^ (derivativeOrder coefficientIndex - 1) :=
    pow_pos (zero_lt_one.trans_le (scaledCellWeight_one_le L ell input)) _
  have nonzero : ((scaledCellWeight L ell input ^ (derivativeOrder coefficientIndex - 1) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr positive.ne'
  rw [startupSingleEntry_literal_operator,startupDerivativeKernel_entry,startupReservedDerivative_projection,
    map_smul,startupDerivativeCoefficient,closedOperatorL2_smul]
  simp only [smul_apply,smul_smul,mul_inv_cancel₀ nonzero,one_smul]

def startupSelectedCoefficientIndex {rank : ℕ} (word : Word rank) (selected : Finset (Fin rank)) :
    DerivativeIndex rank := by
  have total := word_direction_count_total selected.card (subword word selected)
  have bounded : selected.card ≤ rank := by simpa only [Fintype.card_fin] using Finset.card_le_univ selected
  exact ⟨(⟨(selectedIndex word selected).1,by dsimp [selectedIndex]; omega⟩,
    ⟨(selectedIndex word selected).2,by dsimp [selectedIndex]; omega⟩),by dsimp [selectedIndex]; omega⟩

theorem startupSelectedCoefficientIndex_multi {rank : ℕ} (word : Word rank) (selected : Finset (Fin rank)) :
    derivativeMultiIndex (startupSelectedCoefficientIndex word selected) = selectedIndex word selected := rfl

theorem startupSelectedCoefficientIndex_order {rank : ℕ} (word : Word rank) (selected : Finset (Fin rank)) :
    derivativeOrder (startupSelectedCoefficientIndex word selected) = selected.card :=
  word_direction_count_total selected.card (subword word selected)

theorem startupSelectedCoefficientIndex_reserve {rank weight : ℕ}
    (word : Word rank) (selected : Finset (Fin rank)) (reserve : rank - 1 ≤ weight) :
    derivativeOrder (startupSelectedCoefficientIndex word selected) - 1 ≤ weight := by
  rw [startupSelectedCoefficientIndex_order]
  have bounded : selected.card ≤ rank := by simpa only [Fintype.card_fin] using Finset.card_le_univ selected
  omega

end Grad.CartesianStartup

import GSP4PolarMatrixMoments

noncomputable section
open scoped BigOperators ContDiff
namespace Grad.ActualGaugeSigmaPrimitives
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.GenericCarriers Grad.SourceCollarCoefficients
open Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation

def polarEntryCellTerm (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3) (coherent : FamilyCoherent family)
    (row column : Fin 3) (slot : Fin 2 × Fin 2) (cell : ℤ) : ℝ × ℝ → ComplexEuclidean 1 :=
  angularCharacterField (polarEntryFrequency row column slot) (originalPolarValue
    (coefficientColumnJet parameters (mappedMatrixFamily parameters family row slot.1)
      (mappedMatrixFamily_coherent parameters family coherent row slot.1) cell (kappaLaurentRight column slot.2)))

theorem polarEntryCellTerm_smooth (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3) (coherent : FamilyCoherent family)
    (row column : Fin 3) (slot : Fin 2 × Fin 2) (cell : ℤ) :
    ContDiff ℝ ∞ (polarEntryCellTerm parameters family coherent row column slot cell) :=
  angularCharacterField_smooth _ _ (originalPolarValue_smooth _)

def polarEntryCell (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3) (coherent : FamilyCoherent family)
    (row column : Fin 3) (cell : ℤ) : ℝ × ℝ → ComplexEuclidean 1 :=
  ∑ slot, polarEntryCellTerm parameters family coherent row column slot cell

theorem polarEntryCell_smooth (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3) (coherent : FamilyCoherent family)
    (row column : Fin 3) (cell : ℤ) : ContDiff ℝ ∞ (polarEntryCell parameters family coherent row column cell) := by
  unfold polarEntryCell
  simpa only [← Finset.sum_apply] using ContDiff.sum
    (fun slot _ => polarEntryCellTerm_smooth parameters family coherent row column slot cell)

theorem polarEntryCell_coefficient (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3) (coherent : FamilyCoherent family)
    (row column : Fin 3) (cell mode : ℤ) (radial : ℕ) (radius : ℝ) :
    radialCoefficientJet (polarEntryCell parameters family coherent row column cell) mode radial radius =
      polarEntryFourier parameters family coherent row column radial radius (mode, cell) := by
  rw [polarEntryCell, radialCoefficientJet_finsetSum _ _
    (fun slot _ => polarEntryCellTerm_smooth parameters family coherent row column slot cell)]
  apply Finset.sum_congr rfl
  intro slot _
  rw [polarEntryCellTerm, radialCoefficientJet_angularCharacter _ _ (originalPolarValue_smooth _)]
  rfl

theorem polarEntryFourier_hasDerivAt (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3) (coherent : FamilyCoherent family)
    (row column : Fin 3) (mode : ℤ × ℤ) (radial : ℕ) (radius : ℝ) :
    HasDerivAt (fun radius => polarEntryFourier parameters family coherent row column radial radius mode)
      (polarEntryFourier parameters family coherent row column (radial + 1) radius mode) radius := by
  have equality : (fun radius => polarEntryFourier parameters family coherent row column radial radius mode) =
      radialCoefficientJet (polarEntryCell parameters family coherent row column mode.2) mode.1 radial := by
    funext radius
    exact (polarEntryCell_coefficient parameters family coherent row column mode.2 mode.1 radial radius).symm
  rw [equality, ← polarEntryCell_coefficient parameters family coherent row column mode.2 mode.1]
  exact radialCoefficientJet_hasDerivAt _ (polarEntryCell_smooth parameters family coherent row column mode.2) mode.1 radial radius

end Grad.ActualGaugeSigmaPrimitives

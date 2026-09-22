import SCC17PolarFourierCalculus

noncomputable section
open scoped BigOperators ContDiff

namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation
open Grad.SourceCollarDivision Grad.SourceCollarRestriction Grad.SourceCollarAngular

def kappaPolarCellTerm (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (slot : Fin 2 × Fin 2) (cell : ℤ) : ℝ × ℝ → ComplexEuclidean 1 :=
  angularCharacterField (kappaLaurentFrequency component slot) (originalPolarValue
    (coefficientColumnJet parameters
      (mappedCofactorFamily parameters L epsilon field (scalarRowMapping (tangentialLaurentVector slot.1)))
      (mappedCofactorFamily_coherent parameters L rho epsilon field _ low) cell (kappaLaurentRight component slot.2)))

theorem kappaPolarCellTerm_smooth (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (slot : Fin 2 × Fin 2) (cell : ℤ) :
    ContDiff ℝ ∞ (kappaPolarCellTerm parameters L rho epsilon field low component slot cell) :=
  angularCharacterField_smooth _ _ (originalPolarValue_smooth _)

def kappaPolarCell (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (cell : ℤ) : ℝ × ℝ → ComplexEuclidean 1 :=
  ∑ slot, kappaPolarCellTerm parameters L rho epsilon field low component slot cell

theorem kappaPolarCell_smooth (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (cell : ℤ) :
    ContDiff ℝ ∞ (kappaPolarCell parameters L rho epsilon field low component cell) := by
  unfold kappaPolarCell
  simpa only [← Finset.sum_apply] using ContDiff.sum
    (fun slot _ => kappaPolarCellTerm_smooth parameters L rho epsilon field low component slot cell)

theorem kappaPolarCell_coefficient (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (cell mode : ℤ) (radial : ℕ) (radius : ℝ) :
    radialCoefficientJet (kappaPolarCell parameters L rho epsilon field low component cell) mode radial radius =
      kappaFourier parameters L rho epsilon field low component radial radius (mode, cell) := by
  rw [kappaPolarCell, radialCoefficientJet_finsetSum _ _
    (fun slot _ => kappaPolarCellTerm_smooth parameters L rho epsilon field low component slot cell)]
  apply Finset.sum_congr rfl
  intro slot _
  rw [kappaPolarCellTerm, radialCoefficientJet_angularCharacter _ _ (originalPolarValue_smooth _)]
  rfl

/-- The coefficient indexed by radial k+1 is the actual derivative of the
coefficient indexed by k, not a separate freely chosen graph coordinate. -/
theorem kappaFourier_hasDerivAt (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (mode : ℤ × ℤ) (radial : ℕ) (radius : ℝ) :
    HasDerivAt (fun radius => kappaFourier parameters L rho epsilon field low component radial radius mode)
      (kappaFourier parameters L rho epsilon field low component (radial + 1) radius mode) radius := by
  have equality : (fun radius => kappaFourier parameters L rho epsilon field low component radial radius mode) =
      radialCoefficientJet (kappaPolarCell parameters L rho epsilon field low component mode.2) mode.1 radial := by
    funext radius
    exact (kappaPolarCell_coefficient parameters L rho epsilon field low component mode.2 mode.1 radial radius).symm
  rw [equality, ← kappaPolarCell_coefficient parameters L rho epsilon field low component mode.2 mode.1]
  exact radialCoefficientJet_hasDerivAt _
    (kappaPolarCell_smooth parameters L rho epsilon field low component mode.2) mode.1 radial radius

end Grad.SourceCollarCoefficients

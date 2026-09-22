import GPA4CellAngularCalculus

noncomputable section
open scoped BigOperators
namespace Grad.ActualPhysicalAngular
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.BoundaryTrace Grad.SourceCollarCoefficients
open Grad.SourceCollarDivision Grad.SourceCollarRestriction Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation

def sigmaAngularCellBudget (parameters : PhaseParameters) (L epsilon : ℝ) (field : ACore parameters 3)
    (component : Fin 3) (cell : ℤ) : ℝ :=
  ∑ slot : Fin 2 × Fin 2, characterColumnAngularBudget parameters
    (mappedMatrixFamily parameters (originalCofactorDeviation parameters L epsilon field) 0 slot.1) (kappaLaurentRight component slot.2) (polarEntryFrequency 0 component slot) cell

theorem sigmaAngularCellBudget_summable (parameters : PhaseParameters) (L epsilon : ℝ) (field : ACore parameters 3)
    (component : Fin 3) :
    Summable (sigmaAngularCellBudget parameters L epsilon field component) :=
  summable_sum (fun slot _ => characterColumnAngularBudget_summable parameters (mappedMatrixFamily parameters (originalCofactorDeviation parameters L epsilon field) 0 slot.1)
    (kappaLaurentRight component slot.2) (polarEntryFrequency 0 component slot))

theorem sigmaAngularCell_periodic (parameters : PhaseParameters) (L rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (source : ℤ) :
    Function.Periodic (polarEntryCell parameters (originalCofactorDeviation parameters L epsilon field) (originalCofactorDeviation_coherent parameters L rho epsilon field low) 0 component source) (0, 2 * Real.pi) := by
  intro point
  change (∑ slot : Fin 2 × Fin 2, polarEntryCellTerm parameters (originalCofactorDeviation parameters L epsilon field) (originalCofactorDeviation_coherent parameters L rho epsilon field low) 0 component slot source) (point + (0, 2 * Real.pi)) =
    (∑ slot : Fin 2 × Fin 2, polarEntryCellTerm parameters (originalCofactorDeviation parameters L epsilon field) (originalCofactorDeviation_coherent parameters L rho epsilon field low) 0 component slot source) point
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro slot _
  exact angularCharacterField_periodic (polarEntryFrequency 0 component slot) _ (originalPolarValue_periodic _) point

theorem sigmaAngularCell_bound (parameters : PhaseParameters) (L rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (source : ℤ)
    (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    ‖scalarCellAngular (polarEntryCell parameters (originalCofactorDeviation parameters L epsilon field) (originalCofactorDeviation_coherent parameters L rho epsilon field low) 0 component source) radius angle‖ ≤
      sigmaAngularCellBudget parameters L epsilon field component source := by
  apply (PiLp.norm_apply_le _ 0).trans
  change ‖angularJet 1 (∑ slot : Fin 2 × Fin 2, polarEntryCellTerm parameters (originalCofactorDeviation parameters L epsilon field) (originalCofactorDeviation_coherent parameters L rho epsilon field low) 0 component slot source) (radius, angle)‖ ≤ _
  rw [angularJet_one_finsetSum _ _ (fun slot _ => polarEntryCellTerm_smooth parameters (originalCofactorDeviation parameters L epsilon field) (originalCofactorDeviation_coherent parameters L rho epsilon field low) 0 component slot source)]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro slot _
  change ‖angularJet 1 (angularCharacterField (polarEntryFrequency 0 component slot) (originalPolarValue
    (coefficientColumnJet parameters (mappedMatrixFamily parameters (originalCofactorDeviation parameters L epsilon field) 0 slot.1) (mappedMatrixFamily_coherent parameters (originalCofactorDeviation parameters L epsilon field) (originalCofactorDeviation_coherent parameters L rho epsilon field low) 0 slot.1) source (kappaLaurentRight component slot.2)))) (radius, angle)‖ ≤ _
  rw [characterColumn_angularJet]
  exact characterColumnAngularValue_bound parameters (mappedMatrixFamily parameters (originalCofactorDeviation parameters L epsilon field) 0 slot.1) (mappedMatrixFamily_coherent parameters (originalCofactorDeviation parameters L epsilon field) (originalCofactorDeviation_coherent parameters L rho epsilon field low) 0 slot.1) source
    (kappaLaurentRight component slot.2) (polarEntryFrequency 0 component slot) radius angle nonnegative bounded

end Grad.ActualPhysicalAngular


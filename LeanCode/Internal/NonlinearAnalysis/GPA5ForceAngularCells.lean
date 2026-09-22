import GPA4CellAngularCalculus

noncomputable section
open scoped BigOperators
namespace Grad.ActualPhysicalAngular
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.BoundaryTrace Grad.SourceCollarCoefficients
open Grad.SourceCollarDivision Grad.SourceCollarRestriction Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation

def forceAngularCellBudget (parameters : PhaseParameters) (L epsilon : ℝ) (field : ACore parameters 3)
    (kind : Fin 2) (component : Fin 3) (cell : ℤ) : ℝ :=
  ∑ slot : Fin 2 × Fin 2, characterColumnAngularBudget parameters
    (mappedForceFamily parameters L epsilon field (scalarRowMapping (forceLaurentLeft kind slot.1))) (kappaLaurentRight component slot.2) (forceLaurentFrequency kind component slot) cell

theorem forceAngularCellBudget_summable (parameters : PhaseParameters) (L epsilon : ℝ) (field : ACore parameters 3)
    (kind : Fin 2) (component : Fin 3) :
    Summable (forceAngularCellBudget parameters L epsilon field kind component) :=
  summable_sum (fun slot _ => characterColumnAngularBudget_summable parameters (mappedForceFamily parameters L epsilon field (scalarRowMapping (forceLaurentLeft kind slot.1)))
    (kappaLaurentRight component slot.2) (forceLaurentFrequency kind component slot))

theorem forceAngularCell_periodic (parameters : PhaseParameters) (L rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (kind : Fin 2) (component : Fin 3) (source : ℤ) :
    Function.Periodic (forcePolarCell parameters L rho epsilon field kind low component source) (0, 2 * Real.pi) := by
  intro point
  change (∑ slot : Fin 2 × Fin 2, forcePolarCellTerm parameters L rho epsilon field kind low component slot source) (point + (0, 2 * Real.pi)) =
    (∑ slot : Fin 2 × Fin 2, forcePolarCellTerm parameters L rho epsilon field kind low component slot source) point
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro slot _
  exact angularCharacterField_periodic (forceLaurentFrequency kind component slot) _ (originalPolarValue_periodic _) point

theorem forceAngularCell_bound (parameters : PhaseParameters) (L rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (kind : Fin 2) (component : Fin 3) (source : ℤ)
    (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    ‖scalarCellAngular (forcePolarCell parameters L rho epsilon field kind low component source) radius angle‖ ≤
      forceAngularCellBudget parameters L epsilon field kind component source := by
  apply (PiLp.norm_apply_le _ 0).trans
  change ‖angularJet 1 (∑ slot : Fin 2 × Fin 2, forcePolarCellTerm parameters L rho epsilon field kind low component slot source) (radius, angle)‖ ≤ _
  rw [angularJet_one_finsetSum _ _ (fun slot _ => forcePolarCellTerm_smooth parameters L rho epsilon field kind low component slot source)]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro slot _
  change ‖angularJet 1 (angularCharacterField (forceLaurentFrequency kind component slot) (originalPolarValue
    (coefficientColumnJet parameters (mappedForceFamily parameters L epsilon field (scalarRowMapping (forceLaurentLeft kind slot.1))) (mappedForceFamily_coherent parameters L rho epsilon field _ low) source (kappaLaurentRight component slot.2)))) (radius, angle)‖ ≤ _
  rw [characterColumn_angularJet]
  exact characterColumnAngularValue_bound parameters (mappedForceFamily parameters L epsilon field (scalarRowMapping (forceLaurentLeft kind slot.1))) (mappedForceFamily_coherent parameters L rho epsilon field _ low) source
    (kappaLaurentRight component slot.2) (forceLaurentFrequency kind component slot) radius angle nonnegative bounded

end Grad.ActualPhysicalAngular


import BCT5BoundaryFourierMoments
import GPA7PhysicalSeriesDifferentiation

noncomputable section
open scoped BigOperators ContDiff

namespace Grad.ActualBoundaryPrimitives

open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.BoundaryTrace Grad.SourceCollarCoefficients
open Grad.SourceCollarDivision Grad.SourceCollarRestriction Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives
open Grad.ActualPhysicalAngular Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation

/-- A summable cellwise derivative bound for the accepted full polar
coefficient representation; needed before differentiating its axial sum. -/
def polarFamilyAngularBudget (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3)
    (row component : Fin 3) (cell : ℤ) : ℝ :=
  ∑ slot : Fin 2 × Fin 2, characterColumnAngularBudget parameters
    (mappedMatrixFamily parameters family row slot.1) (kappaLaurentRight component slot.2)
    (polarEntryFrequency row component slot) cell

theorem polarFamilyAngularBudget_summable (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3)
    (row component : Fin 3) : Summable (polarFamilyAngularBudget parameters family row component) :=
  summable_sum (fun slot _ => characterColumnAngularBudget_summable parameters
    (mappedMatrixFamily parameters family row slot.1) (kappaLaurentRight component slot.2)
    (polarEntryFrequency row component slot))

theorem polarFamilyAngular_periodic (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3)
    (coherent : FamilyCoherent family) (row component : Fin 3) (source : ℤ) :
    Function.Periodic (polarEntryCell parameters family coherent row component source) (0, 2 * Real.pi) := by
  intro point
  change (∑ slot : Fin 2 × Fin 2, polarEntryCellTerm parameters family coherent row component slot source)
    (point + (0, 2 * Real.pi)) =
      (∑ slot : Fin 2 × Fin 2, polarEntryCellTerm parameters family coherent row component slot source) point
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro slot _
  exact angularCharacterField_periodic (polarEntryFrequency row component slot) _
    (originalPolarValue_periodic _) point

theorem polarFamilyAngular_bound (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3)
    (coherent : FamilyCoherent family) (row component : Fin 3) (source : ℤ)
    (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    ‖scalarCellAngular (polarEntryCell parameters family coherent row component source) radius angle‖ ≤
      polarFamilyAngularBudget parameters family row component source := by
  apply (PiLp.norm_apply_le _ 0).trans
  change ‖angularJet 1 (∑ slot : Fin 2 × Fin 2,
    polarEntryCellTerm parameters family coherent row component slot source) (radius, angle)‖ ≤ _
  rw [angularJet_one_finsetSum _ _ (fun slot _ =>
    polarEntryCellTerm_smooth parameters family coherent row component slot source)]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro slot _
  change ‖angularJet 1 (angularCharacterField (polarEntryFrequency row component slot) (originalPolarValue
    (coefficientColumnJet parameters (mappedMatrixFamily parameters family row slot.1)
      (mappedMatrixFamily_coherent parameters family coherent row slot.1) source
      (kappaLaurentRight component slot.2)))) (radius, angle)‖ ≤ _
  rw [characterColumn_angularJet]
  exact characterColumnAngularValue_bound parameters (mappedMatrixFamily parameters family row slot.1)
    (mappedMatrixFamily_coherent parameters family coherent row slot.1) source
    (kappaLaurentRight component slot.2) (polarEntryFrequency row component slot)
    radius angle nonnegative bounded

/-- Genuine ordinary angular derivative of any actual coherent polar matrix
family, with the exact two-frequency Fourier derivative law. -/
theorem polarFamily_classicalAngular (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3)
    (coherent : FamilyCoherent family) (row component : Fin 3)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    let physical := fun axialAngle angle => polarMatrixEntry row component angle
      (Grad.GaugeCoefficients.Physical.Ledger.familyMatrix family 0 axialAngle
        (polarClosedPoint radius angle nonnegative bounded))
    (∀ axialAngle, Differentiable ℝ (physical axialAngle)) ∧
    ∀ mode : ℤ × ℤ,
      angularCoefficient (fun angle => angularCoefficient (fun axialAngle =>
        deriv (physical axialAngle) angle) mode.2) mode.1 =
          angularCoefficientSequence (polarEntryScalar parameters family coherent row component 0 radius) mode := by
  dsimp only
  have correspondence := physicalClassicalAngular_correspondence
    (polarEntryCell parameters family coherent row component)
    (polarEntryCell_smooth parameters family coherent row component)
    (polarFamilyAngular_periodic parameters family coherent row component) radius _
    (fun axialAngle angle => polarEntryCell_fourier parameters family coherent row component radius angle axialAngle nonnegative bounded)
    (fun angle => polarEntryCell_norm_summable parameters family coherent row component radius angle nonnegative bounded)
    (polarFamilyAngularBudget parameters family row component)
    (polarFamilyAngularBudget_summable parameters family row component)
    (fun cell angle => polarFamilyAngular_bound parameters family coherent row component cell radius angle nonnegative bounded)
  refine ⟨correspondence.1, ?_⟩
  intro mode
  rw [correspondence.2 mode, polarEntry_doubleCoefficient parameters family coherent row component radius nonnegative bounded]
  rfl

end Grad.ActualBoundaryPrimitives

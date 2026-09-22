import AKAQ11OriginalA4FlatDecay

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open scoped BigOperators ENNReal
namespace Grad.OriginalFlatAxisDecay.Consumer
open Grad.FourierGrade Grad.CartesianState Grad.ClosedJets Grad.SourceCollarDivision
open Grad.Constraints Grad.NonlinearRange Grad.BoundaryLift
open Grad.OriginalFlatAxisDecay

theorem originalFirstJetFlat_of_core {dimension : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters dimension 4)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (field.toCore.val cell)) :
    OriginalFirstJetFlat parameters (aGradeEta parameters field) := by
  have origin : ambientClosedDisk 0 = (⟨0,by simp [closedUnitDisk]⟩ : ClosedDisk) := Subtype.ext origin_val
  constructor
  · intro cell
    rw [completedOriginalCell_core,origin]
    have law := zeroJets cell 0 (by omega) emptyCartesianWord
    simpa only [closedDerivative_zero_order] using law
  · intro cell direction
    rw [completedCellDerivative_eta,origin]
    exact zeroJets cell 1 (by omega) (fun _ => direction)

/-- Literal original A4 consumer: the two actual lambda-weighted sequences
are in ell2, and satisfy GK03 at the unchanged phase parameters. -/
theorem originalA4_physical_kernel_decay
    (parameters : PhaseParameters) (field : AGrade parameters 3 4)
    (zeroValue : ∀ cell, completedOriginalCell parameters (by omega : 3 ≤ 4) cell field (ambientClosedDisk 0) = 0)
    (zeroDerivative : ∀ (cell : ℤ) (direction : Fin 2),
      completedCellDerivative parameters 1 (fun _ => direction) cell field (ambientClosedDisk 0) = 0)
    (point : ClosedDisk) :
    ∃ (values rotations : lp (fun _ : ℤ => ComplexEuclidean 3) 2),
      (∀ cell, values.val cell = (cellFrequency cell : ℂ) •
        (cartesianWeight parameters cell point.val • completedOriginalCell parameters (by omega) cell field point)) ∧
      (∀ cell, rotations.val cell = (cellFrequency cell : ℂ) •
        (cartesianWeight parameters cell point.val •
          ((point.val 0 : ℂ) • completedCellDerivative parameters 1 (fun _ => 1) cell field point -
            (point.val 1 : ℂ) • completedCellDerivative parameters 1 (fun _ => 0) cell field point))) ∧
      ‖values‖ + ‖rotations‖ ≤ flatDecayConstant * ‖point.val‖^(3/2:ℝ) * ‖field‖ := by
  let flat : OriginalFirstJetFlat parameters field := ⟨zeroValue,zeroDerivative⟩
  refine ⟨originalFlatValueVector parameters field flat point,originalFlatRotationVector parameters field flat point,?_,?_,originalA4_flat_decay parameters field flat point⟩
  · intro cell
    change (cellFrequency cell : ℂ) • completedWeightedCell parameters (by omega) cell field point = _
    rw [completedWeightedCell,ContinuousLinearMap.comp_apply,originalWeightAction_apply]
  · intro cell
    rfl

/-- The same estimate on the project's exact smooth flat-core jets, with
the literal rotationJet retained for the subsequent physical GK adapter. -/
theorem originalSmooth_flat_kernel_decay (parameters : PhaseParameters)
    (field : GradeCore parameters 3 4)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (field.toCore.val cell)) (point : ClosedDisk) :
    ∃ (values rotations : lp (fun _ : ℤ => ComplexEuclidean 3) 2),
      (∀ cell, values.val cell = (cellFrequency cell : ℂ) •
        (cartesianWeight parameters cell point.val • (field.toCore.val cell).value point)) ∧
      (∀ cell, rotations.val cell = (cellFrequency cell : ℂ) •
        (cartesianWeight parameters cell point.val • (rotationJet (field.toCore.val cell)).value point)) ∧
      ‖values‖ + ‖rotations‖ ≤ flatDecayConstant * ‖point.val‖^(3/2:ℝ) * ‖field‖ := by
  let flat := originalFirstJetFlat_of_core parameters field zeroJets
  refine ⟨originalFlatValueVector parameters (aGradeEta parameters field) flat point,
    originalFlatRotationVector parameters (aGradeEta parameters field) flat point,?_,?_,?_⟩
  · intro cell
    change (cellFrequency cell : ℂ) • completedWeightedCell parameters (by omega) cell (aGradeEta parameters field) point = _
    rw [completedWeightedCell_core,phaseWeightedJet_value]
  · intro cell
    change (cellFrequency cell : ℂ) • (cartesianWeight parameters cell point.val •
      originalRotationAt parameters cell point (aGradeEta parameters field)) = _
    rw [originalRotationAt_core]
  · simpa only [aGradeEta_norm] using originalA4_flat_decay parameters (aGradeEta parameters field) flat point

end Grad.OriginalFlatAxisDecay.Consumer

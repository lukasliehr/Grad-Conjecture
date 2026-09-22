import SCD21ClosedRadialGraph
import BL32JetEvaluation

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState Grad.CompatibleCompletion Grad.BoundaryLift

/-- Reuse the accepted closed-disk realization of the original A-grade. -/
def completedOriginalCell {dimension grade : ℕ} (parameters : PhaseParameters)
    (large : 3 ≤ grade) (cell : ℤ) :
    AGrade parameters dimension grade →L[ℂ] C(ClosedDisk, ComplexEuclidean dimension) :=
  (completedCellDerivative parameters 0 emptyCartesianWord cell).comp (completedInclusion parameters large)

theorem completedOriginalCell_core {dimension grade : ℕ} (parameters : PhaseParameters)
    (large : 3 ≤ grade) (cell : ℤ) (field : GradeCore parameters dimension grade) :
    completedOriginalCell parameters large cell (aGradeEta parameters field) = (field.toCore.val cell).value := by
  rw [completedOriginalCell, ContinuousLinearMap.comp_apply, completedInclusion_apply_eta,
    completedCellDerivative_eta, closedDerivative_zero_order]
  rfl

def originalWeightContinuous (parameters : PhaseParameters) (cell : ℤ) : C(ClosedDisk, ℂ) where
  toFun point := cartesianWeight parameters cell point.val
  continuous_toFun := Complex.continuous_ofReal.comp
    ((cartesianWeight_contDiff parameters cell).continuous.comp continuous_subtype_val)

def originalWeightAction {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ) :
    C(ClosedDisk, ComplexEuclidean dimension) →L[ℂ] C(ClosedDisk, ComplexEuclidean dimension) :=
  LinearMap.mkContinuous
    { toFun := fun field => ⟨fun point => originalWeightContinuous parameters cell point • field point,
        (originalWeightContinuous parameters cell).continuous.smul field.continuous⟩
      map_add' := fun first second => by
        apply ContinuousMap.ext
        intro point
        exact smul_add _ _ _
      map_smul' := fun scalar field => by
        apply ContinuousMap.ext
        intro point
        exact smul_comm _ scalar _ }
    ‖originalWeightContinuous parameters cell‖ (fun field => by
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      intro point
      change ‖originalWeightContinuous parameters cell point • field point‖ ≤ _
      rw [norm_smul]
      exact mul_le_mul
        (ContinuousMap.norm_coe_le_norm (originalWeightContinuous parameters cell) point)
        (ContinuousMap.norm_coe_le_norm field point) (norm_nonneg _) (norm_nonneg _))

theorem originalWeightAction_apply {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (field : C(ClosedDisk, ComplexEuclidean dimension)) (point : ClosedDisk) :
    originalWeightAction parameters cell field point = cartesianWeight parameters cell point.val • field point := by
  exact Complex.coe_smul _ _

def completedWeightedCell {dimension grade : ℕ} (parameters : PhaseParameters)
    (large : 3 ≤ grade) (cell : ℤ) :
    AGrade parameters dimension grade →L[ℂ] C(ClosedDisk, ComplexEuclidean dimension) :=
  (originalWeightAction parameters cell).comp (completedOriginalCell parameters large cell)

theorem completedWeightedCell_core {dimension grade : ℕ} (parameters : PhaseParameters)
    (large : 3 ≤ grade) (cell : ℤ) (field : GradeCore parameters dimension grade) :
    completedWeightedCell parameters large cell (aGradeEta parameters field) =
      (phaseWeightedJet parameters cell (field.toCore.val cell)).value := by
  apply ContinuousMap.ext
  intro point
  rw [completedWeightedCell, ContinuousLinearMap.comp_apply, completedOriginalCell_core,
    originalWeightAction_apply, phaseWeightedJet_value]

/-- Only the original value trace is zero. No first-jet or angular
constraint is added to the stated flat-division domain. -/
def OriginalValueFlat {dimension grade : ℕ} (parameters : PhaseParameters) (large : 3 ≤ grade)
    (field : AGrade parameters dimension grade) : Prop :=
  ∀ cell, completedOriginalCell parameters large cell field (ambientClosedDisk 0) = 0

theorem originalValueFlat_weighted {dimension grade : ℕ} (parameters : PhaseParameters) (large : 3 ≤ grade)
    (field : AGrade parameters dimension grade) (flat : OriginalValueFlat parameters large field) (cell : ℤ) :
    completedWeightedCell parameters large cell field (ambientClosedDisk 0) = 0 := by
  rw [completedWeightedCell, ContinuousLinearMap.comp_apply, originalWeightAction_apply, flat cell, smul_zero]

end Grad.SourceCollarDivision

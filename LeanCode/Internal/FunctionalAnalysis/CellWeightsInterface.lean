import GC1Proof
import Mathlib.LinearAlgebra.LinearPMap

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue Cells FieldL2 cellProjection fieldCellProjection)
open scoped Topology BigOperators

namespace Grad.CellWeights

def cellWeight (cell : ℤ) : ℝ := Real.sqrt (1 + (cell : ℝ) ^ 2)

def inverseFactor (order : ℕ) (cell : ℤ) : ℂ := ((cellWeight cell : ℂ) ^ order)⁻¹

def positiveFactor (order : ℕ) (cell : ℤ) : ℂ := (cellWeight cell : ℂ) ^ order

def derivativeFactor (order : ℕ) (cell : ℤ) : ℂ := (Complex.I * (cell : ℂ)) ^ order

def multiplierGraph {Input Output : Type*}
    [NormedAddCommGroup Input] [NormedSpace ℂ Input]
    [NormedAddCommGroup Output] [NormedSpace ℂ Output]
    (evaluation : ℤ → Input →L[ℂ] Output) (factor : ℤ → ℂ) : Submodule ℂ (Input × Input) :=
  ⨅ cell : ℤ, ((evaluation cell).comp (ContinuousLinearMap.snd ℂ Input Input) -
    factor cell • (evaluation cell).comp (ContinuousLinearMap.fst ℂ Input Input)).ker

def cellGraph (dimension : ℕ) (factor : ℤ → ℂ) :
    Submodule ℂ (Cells (PhysicalValue dimension) × Cells (PhysicalValue dimension)) :=
  multiplierGraph (cellProjection (PhysicalValue dimension)) factor

def fieldGraph (dimension : ℕ) (domain : Set Spatial) (factor : ℤ → ℂ) :
    Submodule ℂ (FieldL2 dimension domain × FieldL2 dimension domain) :=
  multiplierGraph (fieldCellProjection dimension domain) factor

def EvaluationGoal : Prop :=
  ∀ (dimension : ℕ) (domain : Set Spatial),
    (∀ cell : ℤ, ‖cellProjection (PhysicalValue dimension) cell‖ ≤ 1 ∧
      ‖fieldCellProjection dimension domain cell‖ ≤ 1) ∧
    (∀ field : FieldL2 dimension domain, ∀ᵐ point ∂volume.restrict domain, ∀ cell : ℤ,
      fieldCellProjection dimension domain cell field point = field point cell) ∧
    (∀ first second : Cells (PhysicalValue dimension),
      (∀ cell, cellProjection (PhysicalValue dimension) cell first =
        cellProjection (PhysicalValue dimension) cell second) → first = second) ∧
    (∀ first second : FieldL2 dimension domain,
      (∀ cell, fieldCellProjection dimension domain cell first =
        fieldCellProjection dimension domain cell second) → first = second)

def RecoveryGoal : Prop :=
  ∀ (dimension : ℕ) (domain : Set Spatial),
    ∃ (cellRecovery : ℕ → Cells (PhysicalValue dimension) →L[ℂ] Cells (PhysicalValue dimension))
      (fieldRecovery : ℕ → FieldL2 dimension domain →L[ℂ] FieldL2 dimension domain),
      (∀ order, ‖cellRecovery order‖ ≤ 1 ∧ Function.Injective (cellRecovery order)) ∧
      (∀ order, ‖fieldRecovery order‖ ≤ 1 ∧ Function.Injective (fieldRecovery order)) ∧
      (∀ order cells cell, cellRecovery order cells cell = inverseFactor order cell • cells cell) ∧
      (∀ order field, ∀ᵐ point ∂volume.restrict domain, ∀ cell,
        fieldRecovery order field point cell = inverseFactor order cell • field point cell) ∧
      cellRecovery 0 = ContinuousLinearMap.id ℂ _ ∧
      fieldRecovery 0 = ContinuousLinearMap.id ℂ _ ∧
      (∀ first second, (cellRecovery first).comp (cellRecovery second) = cellRecovery (first + second)) ∧
      (∀ first second, (fieldRecovery first).comp (fieldRecovery second) = fieldRecovery (first + second))

def GraphGoal : Prop :=
  ∀ (dimension : ℕ) (domain : Set Spatial) (factor : ℤ → ℂ),
    IsClosed (cellGraph dimension factor : Set (Cells (PhysicalValue dimension) × Cells (PhysicalValue dimension))) ∧
    IsClosed (fieldGraph dimension domain factor : Set (FieldL2 dimension domain × FieldL2 dimension domain)) ∧
    (∀ first second, (first, second) ∈ cellGraph dimension factor ↔
      ∀ cell : ℤ, second cell = factor cell • first cell) ∧
    (∀ first second, (first, second) ∈ fieldGraph dimension domain factor ↔
      ∀ cell : ℤ, fieldCellProjection dimension domain cell second =
        factor cell • fieldCellProjection dimension domain cell first) ∧
    (∀ first second third, (first, second) ∈ cellGraph dimension factor →
      (first, third) ∈ cellGraph dimension factor → second = third) ∧
    (∀ first second third, (first, second) ∈ fieldGraph dimension domain factor →
      (first, third) ∈ fieldGraph dimension domain factor → second = third)

#check ContinuousLinearMap.coeFn_compLpL
#check Submodule.toLinearPMap
#check Submodule.toLinearPMap_graph_eq
#check Submodule.mem_graph_toLinearPMap
#check lp.memℓp
#check Memℓp.mono'
#check lp.norm_mono

end Grad.CellWeights

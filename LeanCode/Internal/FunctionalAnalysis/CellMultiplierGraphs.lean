import CellWeightsProof

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue Cells FieldL2 cellProjection fieldCellProjection)
open scoped Topology BigOperators

namespace Grad.CellWeights

section Generic

variable {Input Output : Type*}
  [NormedAddCommGroup Input] [NormedSpace ℂ Input]
  [NormedAddCommGroup Output] [NormedSpace ℂ Output]
  (evaluation : ℤ → Input →L[ℂ] Output) (factor : ℤ → ℂ)

theorem mem_multiplierGraph (pair : Input × Input) : pair ∈ multiplierGraph evaluation factor ↔
    ∀ cell : ℤ, evaluation cell pair.2 = factor cell • evaluation cell pair.1 := by
  simp only [multiplierGraph, Submodule.mem_iInf, LinearMap.mem_ker]
  change (∀ cell : ℤ, evaluation cell pair.2 - factor cell • evaluation cell pair.1 = 0) ↔ _
  simp only [sub_eq_zero]

theorem multiplierGraph_closed : IsClosed (multiplierGraph evaluation factor : Set (Input × Input)) := by
  unfold multiplierGraph
  rw [Submodule.coe_iInf]
  exact isClosed_iInter (fun cell =>
    ((evaluation cell).comp (ContinuousLinearMap.snd ℂ Input Input) -
      factor cell • (evaluation cell).comp (ContinuousLinearMap.fst ℂ Input Input)).isClosed_ker)

theorem multiplierGraph_unique
    (separate : ∀ first second, (∀ cell, evaluation cell first = evaluation cell second) → first = second)
    {first second third : Input}
    (firstGraph : (first, second) ∈ multiplierGraph evaluation factor)
    (secondGraph : (first, third) ∈ multiplierGraph evaluation factor) : second = third := by
  apply separate
  intro cell
  exact ((mem_multiplierGraph evaluation factor _).mp firstGraph cell).trans
    ((mem_multiplierGraph evaluation factor _).mp secondGraph cell).symm

end Generic

theorem cellGraph_mem (dimension : ℕ) (factor : ℤ → ℂ)
    (first second : Cells (PhysicalValue dimension)) :
    (first, second) ∈ cellGraph dimension factor ↔ ∀ cell : ℤ, second cell = factor cell • first cell :=
  mem_multiplierGraph _ _ _

theorem fieldGraph_mem (dimension : ℕ) (domain : Set Spatial) (factor : ℤ → ℂ)
    (first second : FieldL2 dimension domain) : (first, second) ∈ fieldGraph dimension domain factor ↔
    ∀ cell : ℤ, fieldCellProjection dimension domain cell second =
      factor cell • fieldCellProjection dimension domain cell first := mem_multiplierGraph _ _ _

theorem cellGraph_unique (dimension : ℕ) (factor : ℤ → ℂ)
    {first second third : Cells (PhysicalValue dimension)}
    (firstGraph : (first, second) ∈ cellGraph dimension factor)
    (secondGraph : (first, third) ∈ cellGraph dimension factor) : second = third :=
  multiplierGraph_unique _ _ (fun _ _ => cells_ext (PhysicalValue dimension)) firstGraph secondGraph

theorem fieldGraph_unique (dimension : ℕ) (domain : Set Spatial) (factor : ℤ → ℂ)
    {first second third : FieldL2 dimension domain}
    (firstGraph : (first, second) ∈ fieldGraph dimension domain factor)
    (secondGraph : (first, third) ∈ fieldGraph dimension domain factor) : second = third :=
  multiplierGraph_unique _ _ (fun _ _ => fields_ext dimension domain) firstGraph secondGraph

theorem cellGraph_zero_fst (dimension : ℕ) (factor : ℤ → ℂ)
    (pair : Cells (PhysicalValue dimension) × Cells (PhysicalValue dimension))
    (membership : pair ∈ cellGraph dimension factor) (firstZero : pair.1 = 0) : pair.2 = 0 := by
  apply lp.ext
  funext cell
  have equation := (cellGraph_mem dimension factor pair.1 pair.2).mp membership cell
  simpa only [firstZero, lp.coeFn_zero, Pi.zero_apply, smul_zero] using equation

theorem fieldGraph_zero_fst (dimension : ℕ) (domain : Set Spatial) (factor : ℤ → ℂ)
    (pair : FieldL2 dimension domain × FieldL2 dimension domain)
    (membership : pair ∈ fieldGraph dimension domain factor) (firstZero : pair.1 = 0) : pair.2 = 0 := by
  apply fields_ext dimension domain
  intro cell
  have equation := (fieldGraph_mem dimension domain factor pair.1 pair.2).mp membership cell
  simpa only [firstZero, map_zero, smul_zero] using equation

def cellOperator (dimension : ℕ) (factor : ℤ → ℂ) :
    Cells (PhysicalValue dimension) →ₗ.[ℂ] Cells (PhysicalValue dimension) :=
  (cellGraph dimension factor).toLinearPMap

def fieldOperator (dimension : ℕ) (domain : Set Spatial) (factor : ℤ → ℂ) :
    FieldL2 dimension domain →ₗ.[ℂ] FieldL2 dimension domain :=
  (fieldGraph dimension domain factor).toLinearPMap

theorem cellOperator_graph (dimension : ℕ) (factor : ℤ → ℂ) :
    (cellOperator dimension factor).graph = cellGraph dimension factor :=
  (cellGraph dimension factor).toLinearPMap_graph_eq (cellGraph_zero_fst dimension factor)

theorem fieldOperator_graph (dimension : ℕ) (domain : Set Spatial) (factor : ℤ → ℂ) :
    (fieldOperator dimension domain factor).graph = fieldGraph dimension domain factor :=
  (fieldGraph dimension domain factor).toLinearPMap_graph_eq (fieldGraph_zero_fst dimension domain factor)

theorem cellOperator_domain (dimension : ℕ) (factor : ℤ → ℂ) (first : Cells (PhysicalValue dimension)) :
    first ∈ (cellOperator dimension factor).domain ↔
      ∃ second : Cells (PhysicalValue dimension), ∀ cell : ℤ, second cell = factor cell • first cell := by
  change first ∈ (cellGraph dimension factor).map (LinearMap.fst ℂ _ _) ↔ _
  simp only [Submodule.mem_map, Prod.exists, LinearMap.fst_apply, exists_and_right,
    exists_eq_right, cellGraph_mem]

theorem fieldOperator_domain (dimension : ℕ) (domain : Set Spatial) (factor : ℤ → ℂ)
    (first : FieldL2 dimension domain) : first ∈ (fieldOperator dimension domain factor).domain ↔
      ∃ second : FieldL2 dimension domain, ∀ cell : ℤ,
        fieldCellProjection dimension domain cell second = factor cell • fieldCellProjection dimension domain cell first := by
  change first ∈ (fieldGraph dimension domain factor).map (LinearMap.fst ℂ _ _) ↔ _
  simp only [Submodule.mem_map, Prod.exists, LinearMap.fst_apply, exists_and_right,
    exists_eq_right, fieldGraph_mem]

theorem cellOperator_apply (dimension : ℕ) (factor : ℤ → ℂ)
    (first : (cellOperator dimension factor).domain) (cell : ℤ) :
    cellOperator dimension factor first cell = factor cell • first.val cell :=
  (cellGraph_mem dimension factor _ _).mp
    (Submodule.mem_graph_toLinearPMap (cellGraph_zero_fst dimension factor) first) cell

theorem fieldOperator_apply (dimension : ℕ) (domain : Set Spatial) (factor : ℤ → ℂ)
    (first : (fieldOperator dimension domain factor).domain) (cell : ℤ) :
    fieldCellProjection dimension domain cell (fieldOperator dimension domain factor first) =
      factor cell • fieldCellProjection dimension domain cell first.val :=
  (fieldGraph_mem dimension domain factor _ _).mp
    (Submodule.mem_graph_toLinearPMap (fieldGraph_zero_fst dimension domain factor) first) cell

theorem graph_consumer : GraphGoal := by
  intro dimension domain factor
  exact ⟨multiplierGraph_closed _ _, multiplierGraph_closed _ _,
    cellGraph_mem dimension factor, fieldGraph_mem dimension domain factor,
    fun _ _ _ => cellGraph_unique dimension factor, fun _ _ _ => fieldGraph_unique dimension domain factor⟩

theorem positive_graphs_closed (dimension : ℕ) (domain : Set Spatial) (order : ℕ) :
    IsClosed ((cellOperator dimension (positiveFactor order)).graph :
      Set (Cells (PhysicalValue dimension) × Cells (PhysicalValue dimension))) ∧
    IsClosed ((fieldOperator dimension domain (positiveFactor order)).graph :
      Set (FieldL2 dimension domain × FieldL2 dimension domain)) := by
  rw [cellOperator_graph, fieldOperator_graph]
  exact ⟨multiplierGraph_closed _ _, multiplierGraph_closed _ _⟩

theorem derivative_graphs_closed (dimension : ℕ) (domain : Set Spatial) (order : ℕ) :
    IsClosed ((cellOperator dimension (derivativeFactor order)).graph :
      Set (Cells (PhysicalValue dimension) × Cells (PhysicalValue dimension))) ∧
    IsClosed ((fieldOperator dimension domain (derivativeFactor order)).graph :
      Set (FieldL2 dimension domain × FieldL2 dimension domain)) := by
  rw [cellOperator_graph, fieldOperator_graph]
  exact ⟨multiplierGraph_closed _ _, multiplierGraph_closed _ _⟩

end Grad.CellWeights

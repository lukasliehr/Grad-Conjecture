import AJB35OriginalLowDataFiniteApproximation
import AIZ1ActualEnergyTranslations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Filter
open scoped Topology BigOperators
namespace Grad.AnnularOrbitGenerators

section ClosedLp
variable {ι V : Type*} [DecidableEq ι] [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- A closed Fourier graph stable under genuine single-mode cuts contains
every scalar multiplier whose full stored coordinates are square summable. -/
theorem closedLpGraph_weighted (graph : Submodule ℂ (lp (fun _ : ι => V) 2))
    (closed : IsClosed (graph : Set (lp (fun _ : ι => V) 2)))
    (single : ∀ field : graph, ∀ index, lp.single 2 index (field.val index) ∈ graph)
    (field : graph) (weighted : lp (fun _ : ι => V) 2) (coefficient : ι → ℂ)
    (actual : ∀ index, weighted index = coefficient index • field.val index) :
    weighted ∈ graph := by
  apply closed.mem_of_tendsto (originalLpCut_tendsto weighted)
  apply Filter.Eventually.of_forall
  intro support
  apply graph.sum_mem
  intro index _
  have same : lp.single 2 index (weighted index) =
      coefficient index • (lp.single 2 index (field.val index) : lp (fun _ : ι => V) 2) := by
    rw [actual]
    exact (lp.singleContinuousLinearMap ℂ (fun _ : ι => V) 2 index).map_smul _ _
  rw [same]
  exact graph.smul_mem _ (single field index)

end ClosedLp
end Grad.AnnularOrbitGenerators
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularGrades Grad.AnnularOrbitGenerators

variable (lower length : ℝ) (positive : 0 < lower)

/-- One actual high Fourier mode of the completed energy graph. -/
def energySingle (index : HighAnnularMode) :
    annularEnergySpace lower length positive →L[ℂ] annularEnergySpace lower length positive :=
  annularEnergyDiagonal lower length positive (fun mode => if mode = index then 1 else 0)
    1 (by norm_num) (fun mode => by split_ifs <;> norm_num)

theorem energySingle_apply (index : HighAnnularMode)
    (field : annularEnergySpace lower length positive) :
    (energySingle lower length positive index field).val = lp.single 2 index (field.val index) := by
  apply lp.ext
  funext mode
  rw [energySingle, annularEnergyDiagonal_apply, lp.single_apply, Pi.single_apply]
  by_cases same : mode = index
  · subst mode
    simp
  · simp [same]

/-- The arbitrary summable scalar weight stays in the ORIGINAL closed W,
including its radial derivative, potential and true outer trace coordinates. -/
def energySummableMultiplier (field : annularEnergySpace lower length positive)
    (coefficient : HighAnnularMode → ℂ)
    (summable : Memℓp (fun index => coefficient index • field.val index) 2) :
    annularEnergySpace lower length positive :=
  ⟨⟨_, summable⟩, closedLpGraph_weighted (annularEnergySpace lower length positive)
    (LinearMap.range (finiteAnnularEnergyCore lower length positive)).isClosed_topologicalClosure
    (fun source index => by
      rw [← energySingle_apply lower length positive index source]
      exact (energySingle lower length positive index source).property)
    field ⟨_, summable⟩ coefficient (fun _ => rfl)⟩

theorem energySummableMultiplier_apply (field : annularEnergySpace lower length positive)
    (coefficient : HighAnnularMode → ℂ)
    (summable : Memℓp (fun index => coefficient index • field.val index) 2) (index : HighAnnularMode) :
    (energySummableMultiplier lower length positive field coefficient summable).val index =
      coefficient index • field.val index := rfl

end Grad.AnnularHighGenerators

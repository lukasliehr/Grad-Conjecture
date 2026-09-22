import ADW5ActualFiniteSmoothCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularOmegaGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularGrades Grad.AnnularFluxTrace
open Grad.CircularHighRegularity Grad.CircularHighWeak
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Original finite smooth values with their forced omega^-1 radial derivative. -/
def annularOmegaFiniteSmoothCore (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length) :
    (HighAnnularMode →₀ SmoothRadialCore 1) →ₗ[ℝ] AnnularOmegaAmbient lower :=
  ((annularOmegaFromNuCoordinates lower length positive lengthPositive).restrictScalars ℝ).toLinearMap.comp
    (annularNuFiniteSmoothCore lower)

theorem annularOmegaFiniteSmoothCore_mem (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) (core : HighAnnularMode →₀ SmoothRadialCore 1) :
    annularOmegaFiniteSmoothCore lower length positive lengthPositive core ∈
      annularOmegaGraph lower length positive lengthPositive :=
  annularOmegaFromNu_mem lower length positive lengthPositive
    ⟨annularNuFiniteSmoothCore lower core, annularNuFiniteSmoothCore_mem lower positive bounded core⟩

/-- The entire independently defined Domega is the closure of its actual
finite Fourier smooth radial core. No density is assumed. -/
theorem annularOmegaFiniteSmoothCore_closure (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) :
    (LinearMap.range (annularOmegaFiniteSmoothCore lower length positive lengthPositive)).topologicalClosure =
      (annularOmegaGraph lower length positive lengthPositive).restrictScalars ℝ := by
  let subspace := (LinearMap.range (annularOmegaFiniteSmoothCore lower length positive lengthPositive)).topologicalClosure
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨core, rfl⟩
      exact annularOmegaFiniteSmoothCore_mem lower length positive bounded lengthPositive core
    · exact annularOmegaGraph_closed lower length positive lengthPositive
  · intro field member
    have included : (LinearMap.range (annularNuFiniteSmoothCore lower)).topologicalClosure ≤
        subspace.comap ((annularOmegaFromNuCoordinates lower length positive lengthPositive).restrictScalars ℝ).toLinearMap := by
      apply Submodule.topologicalClosure_minimal
      · rintro _ ⟨core, rfl⟩
        apply Submodule.le_topologicalClosure
        exact ⟨core, rfl⟩
      · exact (LinearMap.range (annularOmegaFiniteSmoothCore lower length positive lengthPositive)).isClosed_topologicalClosure.preimage
          (annularOmegaFromNuCoordinates lower length positive lengthPositive).continuous
    rw [annularNuFiniteSmoothCore_closure lower positive bounded] at included
    have transported := included (show annularOmegaNuCoordinates lower length positive lengthPositive field ∈
      (annularFluxWeakGraph lower positive).restrictScalars ℝ from member)
    change annularOmegaFromNuCoordinates lower length positive lengthPositive
      (annularOmegaNuCoordinates lower length positive lengthPositive field) ∈ subspace at transported
    rw [annularOmegaCoordinates_left] at transported
    exact transported

/-- Exact BF1--BF3 high-flux carrier consumer. This concerns the two original
Domega coordinates only, and does not assert the remaining Xalpha blocks. -/
theorem annularOriginalOmegaGraph_consumer (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) :
    IsClosed (annularOmegaGraph lower length positive lengthPositive : Set (AnnularOmegaAmbient lower)) ∧
    Function.Injective (fun field : annularOmegaGraph lower length positive lengthPositive => field.val 0) ∧
    (LinearMap.range (annularOmegaFiniteSmoothCore lower length positive lengthPositive)).topologicalClosure =
      (annularOmegaGraph lower length positive lengthPositive).restrictScalars ℝ ∧
    (∀ field : annularOmegaGraph lower length positive lengthPositive,
      ‖field‖ ^ 2 = ‖field.val 0‖ ^ 2 + ‖field.val 1‖ ^ 2) :=
  ⟨annularOmegaGraph_closed lower length positive lengthPositive,
    annularOmegaGraph_value_injective lower length positive bounded lengthPositive,
    annularOmegaFiniteSmoothCore_closure lower length positive bounded lengthPositive,
    annularOmegaGraph_norm_sq lower length positive lengthPositive⟩

end Grad.AnnularOmegaGraph

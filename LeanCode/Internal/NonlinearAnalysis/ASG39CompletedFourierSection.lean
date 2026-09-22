import ASG38FiniteFourierSection

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

def sourceCoreClosureInclusion (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (angular cell : ℕ) : AnnularSourceH1 parameters dimension lower angular cell →L[ℝ]
      (LinearMap.range (finiteSourceCore parameters dimension lower angular cell)).topologicalClosure :=
  LinearMap.mkContinuous
    { toFun := fun field => ⟨field, finiteSourceCore_denseRange parameters dimension lower angular cell field⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun _ => by simp)

theorem annularFourierSection_exists (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ) :
    ∃ sectionMap : AnnularSourceH1 parameters dimension lower angular cell →L[ℝ]
        FourierContinuousSection dimension lower,
      (∀ core, sectionMap (finiteSourceCore parameters dimension lower angular cell core) =
        finiteFourierSection dimension lower core) ∧
      (∀ field, ‖sectionMap field‖ ≤ sourceEndpointConstant lower * ‖field‖) := by
  have nonnegative : 0 ≤ sourceEndpointConstant lower := Real.sqrt_nonneg _
  have estimate := finiteFourierSection_bound parameters dimension lower positive bounded angular cell
  let : AddCommGroup ((ℤ × ℤ) →₀ SmoothRadialCore dimension) :=
    @Finsupp.instAddCommGroup (ℤ × ℤ) (SmoothRadialCore dimension) inferInstance
  let : Module ℝ ((ℤ × ℤ) →₀ SmoothRadialCore dimension) := Finsupp.module _ _
  have result : ∃ extension :
      (LinearMap.range (finiteSourceCore parameters dimension lower angular cell)).topologicalClosure →L[ℝ]
        FourierContinuousSection dimension lower,
      (∀ core, extension ⟨finiteSourceCore parameters dimension lower angular cell core,
        Submodule.le_topologicalClosure _ ⟨core, rfl⟩⟩ = finiteFourierSection dimension lower core) ∧
      (∀ field, ‖extension field‖ ≤ sourceEndpointConstant lower * ‖field‖) := by
    with_reducible exact (collarRange_extension
      (C := (ℤ × ℤ) →₀ SmoothRadialCore dimension)
      (F := AnnularSourceH1 parameters dimension lower angular cell)
      (T := FourierContinuousSection dimension lower)
      (finiteSourceCore parameters dimension lower angular cell)
      (finiteFourierSection dimension lower) (sourceEndpointConstant lower) nonnegative estimate)
  obtain ⟨extension, coreLaw, bound⟩ := result
  refine ⟨extension.comp (sourceCoreClosureInclusion parameters dimension lower angular cell), ?_, ?_⟩
  · exact coreLaw
  · intro field
    exact bound (sourceCoreClosureInclusion parameters dimension lower angular cell field)

/-- The full normalized Fourier sequence is continuous on the closed collar.
This is a uniform limit in C(I, l2), not merely separate mode continuity. -/
def annularFourierSection (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ) :
    AnnularSourceH1 parameters dimension lower angular cell →L[ℝ] FourierContinuousSection dimension lower :=
  (annularFourierSection_exists parameters dimension lower positive bounded angular cell).choose

theorem annularFourierSection_core (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (core : (ℤ × ℤ) →₀ SmoothRadialCore dimension) :
    annularFourierSection parameters dimension lower positive bounded angular cell
      (finiteSourceCore parameters dimension lower angular cell core) = finiteFourierSection dimension lower core :=
  (annularFourierSection_exists parameters dimension lower positive bounded angular cell).choose_spec.1 core

theorem annularFourierSection_bound (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (field : AnnularSourceH1 parameters dimension lower angular cell) :
    ‖annularFourierSection parameters dimension lower positive bounded angular cell field‖ ≤
      sourceEndpointConstant lower * ‖field‖ :=
  (annularFourierSection_exists parameters dimension lower positive bounded angular cell).choose_spec.2 field

end Grad.AnnularSourceGraph

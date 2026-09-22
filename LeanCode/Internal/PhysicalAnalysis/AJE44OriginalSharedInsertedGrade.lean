import AJE43CompleteStrongFiniteApproximation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open Set Filter
open scoped Topology BigOperators
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularKernelL2 Grad.AnnularOrbitGenerators Grad.AnnularLowEnergy
attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  strongCarrierNormed strongCarrierSeminormed strongCarrierRealNormed strongCarrierRealModule

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)

/-- The literal original BF insertion on every coordinate of the single
shared carrier. The source graphs include both value and radial derivative;
Rg and all independent incoming data are measured in the same norm. -/
def StrongInsertedGrade (grade : ℕ) (data weighted : StrongDataCarrier parameters lower positive bounded 0 0) : Prop :=
  (∀ slot mode, weighted.val.ofLp.1.ofLp.1.ofLp.1 slot mode =
    Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade • data.val.ofLp.1.ofLp.1.ofLp.1 slot mode) ∧
  (∀ slot mode, weighted.val.ofLp.1.ofLp.1.ofLp.2 slot mode =
    Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade • data.val.ofLp.1.ofLp.1.ofLp.2 slot mode) ∧
  (∀ mode, weighted.val.ofLp.1.ofLp.2.ofLp.1.ofLp.1 mode =
    Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade • data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.1 mode) ∧
  (∀ mode, weighted.val.ofLp.1.ofLp.2.ofLp.1.ofLp.2 mode =
    Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade • data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.2 mode) ∧
  (∀ mode, weighted.val.ofLp.1.ofLp.2.ofLp.2.ofLp.1.val mode =
    Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade • data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.1.val mode) ∧
  (∀ mode, weighted.val.ofLp.1.ofLp.2.ofLp.2.ofLp.2 mode =
    Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ grade • data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.2 mode) ∧
  (∀ index, weighted.val.ofLp.2 index =
    Grad.AnnularVariational.annularFrequency index.2.val.1 index.2.val.2 ^ grade • data.val.ofLp.2 index)

/-- Exact support predicate for finite Fourier data, with the full shared
F0/RF0/F2 tuple cut together and actual independent boundary supports. -/
def StrongSupported (support : StrongCutSupport) (data : StrongDataCarrier parameters lower positive bounded 0 0) : Prop :=
  (∀ slot mode, mode ∉ support.1 → data.val.ofLp.1.ofLp.1.ofLp.1 slot mode = 0) ∧
  (∀ slot mode, mode ∉ support.1 → data.val.ofLp.1.ofLp.1.ofLp.2 slot mode = 0) ∧
  (∀ mode, mode ∉ support.1 → data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.1 mode = 0) ∧
  (∀ mode, mode ∉ support.1 → data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.2 mode = 0) ∧
  (∀ mode, mode ∉ support.1 → data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.1.val mode = 0) ∧
  (∀ mode, mode ∉ support.2.1 → data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.2 mode = 0) ∧
  (∀ index, index ∉ support.2.2 → data.val.ofLp.2 index = 0)

theorem strongDataCut_supported (support : StrongCutSupport)
    (data : StrongDataCarrier parameters lower positive bounded 0 0) :
    StrongSupported parameters lower positive bounded support (strongDataCut parameters lower positive bounded support data) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro slot mode outside
    change sourceLpCut support.1 (data.val.ofLp.1.ofLp.1.ofLp.1 slot) mode = 0
    rw [sourceLpCut_apply,if_neg outside]
  · intro slot mode outside
    change sourceLpCut support.1 (data.val.ofLp.1.ofLp.1.ofLp.2 slot) mode = 0
    rw [sourceLpCut_apply,if_neg outside]
  · intro mode outside
    change sourceLpCut support.1 data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.1 mode = 0
    rw [sourceLpCut_apply,if_neg outside]
  · intro mode outside
    change sourceLpCut support.1 data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.2 mode = 0
    rw [sourceLpCut_apply,if_neg outside]
  · intro mode outside
    change sourceLpCut support.1 data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.1.val mode = 0
    rw [sourceLpCut_apply,if_neg outside]
  · intro mode outside
    change sourceLpCut support.2.1 data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.2 mode = 0
    rw [sourceLpCut_apply,if_neg outside]
  · intro index outside
    change sourceLpCut support.2.2 data.val.ofLp.2 index = 0
    rw [sourceLpCut_apply,if_neg outside]

theorem strongDataCut_inserted (support : StrongCutSupport) (grade : ℕ)
    (data weighted : StrongDataCarrier parameters lower positive bounded 0 0)
    (actual : StrongInsertedGrade parameters lower positive bounded grade data weighted) :
    StrongInsertedGrade parameters lower positive bounded grade
      (strongDataCut parameters lower positive bounded support data)
      (strongDataCut parameters lower positive bounded support weighted) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro slot
    exact sourceLpCut_realWeighted support.1 _ _ _ (actual.1 slot)
  · intro slot
    exact sourceLpCut_realWeighted support.1 _ _ _ (actual.2.1 slot)
  · exact sourceLpCut_realWeighted support.1 _ _ _ actual.2.2.1
  · exact sourceLpCut_realWeighted support.1 _ _ _ actual.2.2.2.1
  · exact sourceLpCut_realWeighted support.1 _ _ _ actual.2.2.2.2.1
  · exact sourceLpCut_realWeighted support.2.1 _ _ _ actual.2.2.2.2.2.1
  · exact sourceLpCut_realWeighted support.2.2 _ _ _ actual.2.2.2.2.2.2

/-- Simultaneous approximation at the original base and any prescribed
inserted grade; the same finite cut preserves every defining source law. -/
theorem strongDataCut_graded_approximation (grade : ℕ)
    (data weighted : StrongDataCarrier parameters lower positive bounded 0 0)
    (actual : StrongInsertedGrade parameters lower positive bounded grade data weighted) :
    (∀ support, StrongSupported parameters lower positive bounded support (strongDataCut parameters lower positive bounded support data)) ∧
    (∀ support, StrongInsertedGrade parameters lower positive bounded grade
      (strongDataCut parameters lower positive bounded support data) (strongDataCut parameters lower positive bounded support weighted)) ∧
    Tendsto (fun support => strongDataCut parameters lower positive bounded support data) strongCutFilter (𝓝 data) ∧
    Tendsto (fun support => strongDataCut parameters lower positive bounded support weighted) strongCutFilter (𝓝 weighted) :=
  ⟨fun support => strongDataCut_supported parameters lower positive bounded support data,
    fun support => strongDataCut_inserted parameters lower positive bounded support grade data weighted actual,
    strongDataCut_tendsto parameters lower positive bounded data,
    strongDataCut_tendsto parameters lower positive bounded weighted⟩

end Grad.AnnularStrongOrbit

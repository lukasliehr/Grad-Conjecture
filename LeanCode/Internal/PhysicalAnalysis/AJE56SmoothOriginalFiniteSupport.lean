import AJE55ExactSmoothSourceCore
import AJE44OriginalSharedInsertedGrade

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open Set Filter
open scoped Topology BigOperators
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularLowEnergy
attribute [local instance] originalAmbientRealNormed

variable (parameters : PhaseParameters) (lower : ℝ)

def OriginalSourceSupported (support : StrongCutSupport) (data : OriginalStrongCarrier parameters lower 0 0) : Prop :=
  (∀ mode, mode ∉ support.1 → data.val.ofLp.1.ofLp.1.ofLp.1 mode = 0) ∧
  (∀ mode, mode ∉ support.1 → data.val.ofLp.1.ofLp.1.ofLp.2 mode = 0) ∧
  (∀ mode, mode ∉ support.1 → data.val.ofLp.1.ofLp.2.ofLp.1 mode = 0) ∧
  (∀ mode, mode ∉ support.1 → data.val.ofLp.1.ofLp.2.ofLp.2 mode = 0) ∧
  (∀ mode, mode ∉ support.1 → data.val.ofLp.2.ofLp.1.val mode = 0) ∧
  (∀ mode, mode ∉ support.2.1 → data.val.ofLp.2.ofLp.2.ofLp.1 mode = 0) ∧
  (∀ index, index ∉ support.2.2 → data.val.ofLp.2.ofLp.2.ofLp.2 index = 0)

def originalSmoothSupport (core : OriginalSmoothSourceCore parameters) : StrongCutSupport :=
  (core.1.1.1.support ∪ core.1.1.2.support ∪ core.1.2.1.support ∪ core.1.2.2.support ∪ core.2.1.1,
    core.2.2.1.support,core.2.2.2.support)

private theorem meanFreeCore_zero (core : RadialFourierSourceCore) (mode : ℤ × ℤ)
    (zero : core mode = 0) : meanFreeRadialCore core mode = 0 := by
  rw [meanFreeRadialCore_apply,zero]
  split_ifs <;> rfl

theorem originalSmoothStrongData_supported (positive : 0 < lower) (bounded : lower ≤ 1)
    (core : OriginalSmoothSourceCore parameters) :
    OriginalSourceSupported parameters lower (originalSmoothSupport parameters core)
      (originalSmoothStrongData parameters lower positive bounded core) := by
  have outside (mode : ℤ × ℤ) (absent : mode ∉ (originalSmoothSupport parameters core).1) :
      core.1.1.1 mode = 0 ∧ core.1.1.2 mode = 0 ∧ core.1.2.1 mode = 0 ∧ core.1.2.2 mode = 0 ∧ mode ∉ core.2.1.1 := by
    simpa only [originalSmoothSupport,Finset.mem_union,not_or,Finsupp.notMem_support_iff,and_assoc] using absent
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro mode absent
    rw [(originalSmoothStrongData_graph_modes parameters lower positive bounded core mode).1,(outside mode absent).1,map_zero]
  · intro mode absent
    rw [(originalSmoothStrongData_graph_modes parameters lower positive bounded core mode).2,
      meanFreeCore_zero _ _ (outside mode absent).2.1,map_zero]
  · intro mode absent
    rw [(originalSmoothStrongData_forcing parameters lower positive bounded core).1,finiteSmoothRadialSource_mode,
      meanFreeCore_zero _ _ (outside mode absent).2.2.1,map_zero]
  · intro mode absent
    rw [(originalSmoothStrongData_forcing parameters lower positive bounded core).2,finiteSmoothRadialSource_mode,
      meanFreeCore_zero _ _ (outside mode absent).2.2.2.1,map_zero]
  · intro mode absent
    change sourceLpCut core.2.1.1 core.2.1.2.val mode = 0
    rw [sourceLpCut_apply,if_neg (outside mode absent).2.2.2.2]
  · intro mode absent
    change finiteLpSourceCore (LinearMap.id : ComplexEuclidean 1 →ₗ[ℝ] ComplexEuclidean 1) core.2.2.1 mode = 0
    rw [finiteLpSourceCore_apply]
    exact Finsupp.notMem_support_iff.mp absent
  · intro index absent
    change finiteLpSourceCore (LinearMap.id : ComplexEuclidean 1 →ₗ[ℝ] ComplexEuclidean 1) core.2.2.2 index = 0
    rw [finiteLpSourceCore_apply]
    exact Finsupp.notMem_support_iff.mp absent

end Grad.AnnularStrongOrbit

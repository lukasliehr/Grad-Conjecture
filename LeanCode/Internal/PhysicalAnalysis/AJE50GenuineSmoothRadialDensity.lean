import AJE45FiniteSourceGraphOrbitSmoothness
import ASG17SmoothRadialPrimitives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators ENNReal
namespace Grad.AnnularStrongOrbit
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularSourceGraph

section FiniteCore
variable {ι C E : Type*} [DecidableEq ι] [AddCommMonoid C] [Module ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E]

def finiteLpSourceCore (mapping : C →ₗ[ℝ] E) : (ι →₀ C) →ₗ[ℝ] lp (fun _ : ι => E) 2 :=
  Finsupp.lsum ℝ (fun index => (lp.singleContinuousLinearMap ℝ (fun _ : ι => E) 2 index).toLinearMap.comp mapping)

theorem finiteLpSourceCore_single (mapping : C →ₗ[ℝ] E) (index : ι) (core : C) :
    finiteLpSourceCore mapping (Finsupp.single index core) = lp.single 2 index (mapping core) := by
  rw [finiteLpSourceCore,Finsupp.lsum_single]
  rfl

theorem finiteLpSourceCore_apply (mapping : C →ₗ[ℝ] E) (core : ι →₀ C) (index : ι) :
    finiteLpSourceCore mapping core index = mapping (core index) := by
  rw [finiteLpSourceCore,Finsupp.lsum_apply,Finsupp.sum,lp.coeFn_sum,Finset.sum_apply]
  change (∑ other ∈ core.support,(lp.single 2 other (mapping (core other)) : lp (fun _ : ι => E) 2) index) = _
  simp only [lp.single_apply,Pi.single_apply]
  rw [Finset.sum_eq_single index]
  · simp only [ite_true]
  · intro other _ different
    exact if_neg (Ne.symm different)
  · intro outside
    rw [Finsupp.notMem_support_iff.mp outside,map_zero]
    simp

theorem finiteLpSourceCore_denseRange (mapping : C →ₗ[ℝ] E) (dense : DenseRange mapping) :
    DenseRange (finiteLpSourceCore (ι := ι) mapping) := by
  let subspace := (LinearMap.range (finiteLpSourceCore (ι := ι) mapping)).topologicalClosure
  have singleMember (index : ι) (field : E) : (lp.single 2 index field : lp (fun _ : ι => E) 2) ∈ subspace := by
    apply isClosed_property dense
      ((LinearMap.range (finiteLpSourceCore (ι := ι) mapping)).isClosed_topologicalClosure.preimage
        (lp.singleContinuousLinearMap ℝ (fun _ : ι => E) 2 index).continuous) _ field
    intro core
    apply Submodule.le_topologicalClosure
    exact ⟨Finsupp.single index core,finiteLpSourceCore_single mapping index core⟩
  have closureTop : subspace = ⊤ := by
    apply top_unique
    intro field _
    have convergence : HasSum (fun index : ι => (lp.single 2 index (field index) : lp (fun _ : ι => E) 2)) field :=
      lp.hasSum_single (by norm_num) field
    apply (LinearMap.range (finiteLpSourceCore (ι := ι) mapping)).isClosed_topologicalClosure.mem_of_tendsto convergence
    exact Filter.Eventually.of_forall (fun support => subspace.sum_mem (fun index _ => singleMember index (field index)))
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr closureTop
end FiniteCore

/-- Finite full Fourier sources with actual globally smooth radial modes,
not merely smooth translation orbits. -/
def finiteSmoothRadialSource (dimension : ℕ) (lower : ℝ) :
    ((ℤ × ℤ) →₀ SmoothRadialCore dimension) →ₗ[ℝ] DivisionRow dimension lower :=
  finiteLpSourceCore (smoothRadialValueL2 dimension lower)

theorem finiteSmoothRadialSource_denseRange (dimension : ℕ) (lower : ℝ) :
    DenseRange (finiteSmoothRadialSource dimension lower) :=
  finiteLpSourceCore_denseRange (smoothRadialValueL2 dimension lower) (smoothRadialValueL2_denseRange dimension lower)

theorem finiteSmoothRadialSource_mode (dimension : ℕ) (lower : ℝ)
    (core : (ℤ × ℤ) →₀ SmoothRadialCore dimension) (mode : ℤ × ℤ) :
    finiteSmoothRadialSource dimension lower core mode = smoothRadialValueL2 dimension lower (core mode) :=
  finiteLpSourceCore_apply _ _ _

theorem finiteSmoothRadialSource_radial (dimension : ℕ) (lower : ℝ)
    (core : (ℤ × ℤ) →₀ SmoothRadialCore dimension) (mode : ℤ × ℤ) :
    ContDiff ℝ ∞ (core mode).val.val.1 ∧
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      finiteSmoothRadialSource dimension lower core mode radius = (core mode).val.val.1 radius := by
  refine ⟨(core mode).property,?_⟩
  rw [finiteSmoothRadialSource_mode]
  exact (collarContinuous_memLp (ComplexEuclidean dimension) lower (core mode).val.val.1).coeFn_toLp

section Pair
variable {C D E F : Type*} [AddCommMonoid C] [Module ℝ C] [AddCommMonoid D] [Module ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def realHilbertSourcePair (first : C →ₗ[ℝ] E) (second : D →ₗ[ℝ] F) : (C × D) →ₗ[ℝ] WithLp 2 (E × F) :=
  (WithLp.linearEquiv 2 ℝ (E × F)).symm.toLinearMap.comp (first.prodMap second)

theorem realHilbertSourcePair_denseRange (first : C →ₗ[ℝ] E) (second : D →ₗ[ℝ] F)
    (firstDense : DenseRange first) (secondDense : DenseRange second) : DenseRange (realHilbertSourcePair first second) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.surjective.denseRange.comp
    (firstDense.prodMap secondDense) (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.continuous
end Pair

end Grad.AnnularStrongOrbit

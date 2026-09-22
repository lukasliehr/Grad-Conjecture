import AAW6SameSolutionSmoothness
import ASG17SmoothRadialPrimitives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

def annularSmoothBulkMode (lower : ℝ) : SmoothRadialCore 1 →ₗ[ℝ] RadialL2 1 lower :=
  ((radialSqrtMap 1 lower).restrictScalars ℝ).toLinearMap.comp (smoothRadialValueL2 1 lower)

theorem annularSmoothBulkMode_denseRange (lower : ℝ) (positive : 0 < lower) :
    DenseRange (annularSmoothBulkMode lower) := by
  have onto : Function.Surjective (radialSqrtMap 1 lower) :=
    fun field => ⟨radialOrdinary 1 lower positive field, radialSqrt_ordinary lower positive field⟩
  exact onto.denseRange.comp (smoothRadialValueL2_denseRange 1 lower) (radialSqrtMap 1 lower).continuous

def annularBulkModeSingle (lower : ℝ) (mode : HighAnnularMode) :
    RadialL2 1 lower →L[ℝ] AnnularBulk lower :=
  lp.singleContinuousLinearMap ℝ (fun _ : HighAnnularMode => RadialL2 1 lower) 2 mode

/-- The actual finite-mode smooth radial bulk data, stored with sqrt(r).
The original curved phase is removed only when reading the physical data. -/
def annularFiniteSmoothBulk (lower : ℝ) :
    (HighAnnularMode →₀ SmoothRadialCore 1) →ₗ[ℝ] AnnularBulk lower :=
  Finsupp.lsum ℝ (fun mode => (annularBulkModeSingle lower mode).toLinearMap.comp (annularSmoothBulkMode lower))

theorem annularFiniteSmoothBulk_single (lower : ℝ) (mode : HighAnnularMode) (core : SmoothRadialCore 1) :
    annularFiniteSmoothBulk lower (Finsupp.single mode core) = annularBulkModeSingle lower mode (annularSmoothBulkMode lower core) := by
  rw [annularFiniteSmoothBulk, Finsupp.lsum_single]
  rfl

theorem annularFiniteSmoothBulk_apply (lower : ℝ) (core : HighAnnularMode →₀ SmoothRadialCore 1)
    (mode : HighAnnularMode) :
    annularFiniteSmoothBulk lower core mode = annularSmoothBulkMode lower (core mode) := by
  classical
  rw [annularFiniteSmoothBulk, Finsupp.lsum_apply, Finsupp.sum, lp.coeFn_sum, Finset.sum_apply]
  change (∑ other ∈ core.support,
    (lp.single 2 other (annularSmoothBulkMode lower (core other)) : AnnularBulk lower) mode) = _
  simp only [lp.single_apply, Pi.single_apply]
  rw [Finset.sum_eq_single mode]
  · simp only [ite_true]
  · intro other _ different
    exact if_neg (Ne.symm different)
  · intro missing
    rw [Finsupp.notMem_support_iff.mp missing, map_zero]
    simp

theorem annularFiniteSmoothBulk_denseRange (lower : ℝ) (positive : 0 < lower) :
    DenseRange (annularFiniteSmoothBulk lower) := by
  let subspace := (LinearMap.range (annularFiniteSmoothBulk lower)).topologicalClosure
  have singleMember (mode : HighAnnularMode) (field : RadialL2 1 lower) :
      annularBulkModeSingle lower mode field ∈ subspace := by
    apply isClosed_property (annularSmoothBulkMode_denseRange lower positive)
      ((LinearMap.range (annularFiniteSmoothBulk lower)).isClosed_topologicalClosure.preimage
        (annularBulkModeSingle lower mode).continuous) _ field
    intro core
    apply Submodule.le_topologicalClosure
    exact ⟨Finsupp.single mode core, annularFiniteSmoothBulk_single lower mode core⟩
  have closureTop : subspace = ⊤ := by
    apply top_unique
    intro field _
    have convergence : HasSum (fun mode : HighAnnularMode => annularBulkModeSingle lower mode (field mode)) field :=
      lp.hasSum_single (by norm_num) field
    apply (LinearMap.range (annularFiniteSmoothBulk lower)).isClosed_topologicalClosure.mem_of_tendsto convergence
    exact Filter.Eventually.of_forall (fun support => subspace.sum_mem (fun mode _ => singleMember mode (field mode)))
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr closureTop

def annularSmoothPhysicalCurve (parameters : PhaseParameters) (mode : HighAnnularMode)
    (core : SmoothRadialCore 1) : C(ℝ, ComplexEuclidean 1) :=
  ⟨fun radius => annularInversePhase parameters mode.val.2 radius • core.val.val.1 radius,
    (annularInversePhase parameters mode.val.2).continuous.smul core.val.val.1.continuous⟩

theorem annularSmoothPhysicalCurve_smooth (parameters : PhaseParameters) (mode : HighAnnularMode)
    (core : SmoothRadialCore 1) : ContDiff ℝ ∞ (annularSmoothPhysicalCurve parameters mode core) :=
  ((radialPhase_smooth parameters mode.val.2).neg.exp).smul core.property

theorem annularSmoothBulkMode_physical (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (core : SmoothRadialCore 1) :
    annularDecodeMode parameters lower positive mode (annularSmoothBulkMode lower core)
      =ᵐ[volume.restrict (Icc lower 1)] annularSmoothPhysicalCurve parameters mode core := by
  change collarScalar 1 lower (annularInversePhase parameters mode.val.2)
      (radialOrdinary 1 lower positive (radialSqrtMap 1 lower (smoothRadialValueL2 1 lower core))) =ᵐ[_] _
  rw [radialOrdinary_sqrt]
  filter_upwards [collarScalar_ae 1 lower (annularInversePhase parameters mode.val.2) (smoothRadialValueL2 1 lower core),
    (collarContinuous_memLp (ComplexEuclidean 1) lower core.val.val.1).coeFn_toLp] with radius multiplied base
  change smoothRadialValueL2 1 lower core radius = _ at base
  rw [multiplied, base]
  rfl

end Grad.AnnularRegularity

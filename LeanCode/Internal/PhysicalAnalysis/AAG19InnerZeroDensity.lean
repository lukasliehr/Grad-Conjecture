import AAG14CompletedInnerLift

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularVariational

open Grad.ClosedJets

def annularZeroSmoothCore (lower : ℝ) : Submodule ℂ (HighAnnularMode →₀ complexSmoothRadialCore 1) :=
  (finiteAnnularTraceCore lower 0).ker

theorem annularZeroSmoothCore_iff (lower : ℝ) (core : HighAnnularMode →₀ complexSmoothRadialCore 1) :
    core ∈ annularZeroSmoothCore lower ↔ ∀ mode, (core mode).val.1 lower = 0 := by
  constructor
  · intro zero mode
    have equality := congrArg (fun boundary : AnnularBoundary => boundary mode) zero
    rw [finiteAnnularTraceCore_apply] at equality
    change (Real.sqrt (annularFrequency mode.val.1 mode.val.2) : ℂ) • (core mode).val.1 lower = 0 at equality
    have nonzero : (Real.sqrt (annularFrequency mode.val.1 mode.val.2) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (zero_lt_one.trans_le (annularFrequency_one_le _ _))).ne'
    exact (smul_eq_zero.mp equality).resolve_left nonzero
  · intro zero
    apply lp.ext
    funext mode
    rw [finiteAnnularTraceCore_apply]
    change (Real.sqrt (annularFrequency mode.val.1 mode.val.2) : ℂ) • (core mode).val.1 lower = 0
    rw [zero, smul_zero]

def annularZeroSmoothInto (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (lengthPositive : 0 < length) :
    annularZeroSmoothCore lower →ₗ[ℂ] annularInnerZero lower length positive bounded lengthPositive :=
  (((annularEnergyCoreInto lower length positive).comp (annularZeroSmoothCore lower).subtype).codRestrict _
    (fun core => by
      change annularEnergyTrace lower length positive bounded lengthPositive 0
        (annularEnergyCoreInto lower length positive core.val) = 0
      rw [annularEnergyTrace_core]
      exact core.property))

def annularZeroProjectionRaw (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (lengthPositive : 0 < length) :
    annularEnergySpace lower length positive →L[ℂ] annularEnergySpace lower length positive :=
  ContinuousLinearMap.id ℂ _ - (annularInnerLift lower length positive bounded).comp
    (annularEnergyTrace lower length positive bounded lengthPositive 0)

theorem annularZeroProjectionRaw_mem (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (lengthPositive : 0 < length) (field : annularEnergySpace lower length positive) :
    annularZeroProjectionRaw lower length positive bounded lengthPositive field ∈
      annularInnerZero lower length positive bounded lengthPositive := by
  change annularEnergyTrace lower length positive bounded lengthPositive 0
    (field - annularInnerLift lower length positive bounded
      (annularEnergyTrace lower length positive bounded lengthPositive 0 field)) = 0
  rw [map_sub, annularInnerLift_inner, sub_self]

def annularZeroProjection (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (lengthPositive : 0 < length) :
    annularEnergySpace lower length positive →L[ℂ] annularInnerZero lower length positive bounded lengthPositive :=
  (annularZeroProjectionRaw lower length positive bounded lengthPositive).codRestrict _
    (annularZeroProjectionRaw_mem lower length positive bounded lengthPositive)

theorem annularZeroProjection_identity (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (lengthPositive : 0 < length) (field : annularInnerZero lower length positive bounded lengthPositive) :
    annularZeroProjection lower length positive bounded lengthPositive field.val = field := by
  apply Subtype.ext
  change field.val - annularInnerLift lower length positive bounded
    (annularEnergyTrace lower length positive bounded lengthPositive 0 field.val) = field.val
  have zero : annularEnergyTrace lower length positive bounded lengthPositive 0 field.val = 0 := field.property
  rw [zero, map_zero, sub_zero]

theorem liftedFiniteTrace_mem_smoothRange (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (core : HighAnnularMode →₀ complexSmoothRadialCore 1) :
    annularInnerLift lower length positive bounded (finiteAnnularTraceCore lower 0 core) ∈
      LinearMap.range (annularEnergyCoreInto lower length positive) := by
  classical
  rw [finiteAnnularTraceCore, finiteLpLinear, Finsupp.lsum_apply, Finsupp.sum, map_sum]
  apply (LinearMap.range (annularEnergyCoreInto lower length positive)).sum_mem
  intro mode _
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
    lp.singleContinuousLinearMap_apply]
  let vector := (Real.sqrt (annularFrequency mode.val.1 mode.val.2) : ℂ) •
    complexCoreEndpoint 1 (Grad.AnnularSourceGraph.radialEndpointRadius lower 0) (core mode)
  refine ⟨Finsupp.single mode (annularInnerLiftMode lower mode vector), ?_⟩
  have singleEquality := (annularInnerLift_single lower length positive bounded mode vector).symm
  convert singleEquality using 1
  congr 1
  apply lp.ext
  funext index
  simp only [lp.single_apply, Pi.single_apply]
  by_cases same : index = mode
  · simp only [same]
    rfl
  · simp only [same, if_false]

theorem annularZeroProjection_core_mem (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (lengthPositive : 0 < length) (core : HighAnnularMode →₀ complexSmoothRadialCore 1) :
    annularZeroProjection lower length positive bounded lengthPositive
      (annularEnergyCoreInto lower length positive core) ∈
        LinearMap.range (annularZeroSmoothInto lower length positive bounded lengthPositive) := by
  let projected := annularZeroProjection lower length positive bounded lengthPositive
    (annularEnergyCoreInto lower length positive core)
  have smooth : projected.val ∈ LinearMap.range (annularEnergyCoreInto lower length positive) := by
    change annularEnergyCoreInto lower length positive core -
      annularInnerLift lower length positive bounded
        (annularEnergyTrace lower length positive bounded lengthPositive 0 (annularEnergyCoreInto lower length positive core)) ∈ _
    rw [annularEnergyTrace_core]
    exact (LinearMap.range (annularEnergyCoreInto lower length positive)).sub_mem ⟨core, rfl⟩
      (liftedFiniteTrace_mem_smoothRange lower length positive bounded core)
  rcases smooth with ⟨corrected, equality⟩
  have zero : corrected ∈ annularZeroSmoothCore lower := by
    change finiteAnnularTraceCore lower 0 corrected = 0
    rw [← annularEnergyTrace_core lower length positive bounded lengthPositive 0 corrected, equality]
    exact projected.property
  exact ⟨⟨corrected, zero⟩, Subtype.ext equality⟩

/-- AG8: the genuine finite smooth core with exactly zero inner value is
dense in the full kernel of the completed sharp inner trace. -/
theorem annularZeroSmoothInto_denseRange (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (lengthPositive : 0 < length) :
    DenseRange (annularZeroSmoothInto lower length positive bounded lengthPositive) := by
  let image := LinearMap.range (annularZeroSmoothInto lower length positive bounded lengthPositive)
  have projected (field : annularEnergySpace lower length positive) :
      annularZeroProjection lower length positive bounded lengthPositive field ∈ image.topologicalClosure := by
    apply isClosed_property (annularEnergyCoreInto_denseRange lower length positive)
      (image.isClosed_topologicalClosure.preimage (annularZeroProjection lower length positive bounded lengthPositive).continuous) _ field
    intro core
    exact Submodule.le_topologicalClosure _ (annularZeroProjection_core_mem lower length positive bounded lengthPositive core)
  change Dense (image : Set (annularInnerZero lower length positive bounded lengthPositive))
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply top_unique
  intro field _
  have member := projected field.val
  rw [annularZeroProjection_identity] at member
  exact member

end Grad.AnnularVariational

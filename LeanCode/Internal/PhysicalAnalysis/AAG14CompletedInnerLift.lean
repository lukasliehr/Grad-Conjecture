import AAG9CompletedSharpTrace
import AAG12InnerLiftCore

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularVariational

open Grad.ClosedJets

def annularInnerLiftModeEnergy (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (mode : HighAnnularMode) :
    ComplexEuclidean 1 →L[ℂ] AnnularModeEnergyAmbient lower :=
  ((annularModeEnergyCore lower length positive mode.val.1 mode.val.2).comp (annularInnerLiftMode lower mode)).mkContinuous
    (annularInnerLiftConstant lower length) (annularInnerLiftMode_energy_bound lower length positive bounded mode)

def annularInnerLiftRaw (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    AnnularBoundary →L[ℂ] AnnularEnergyAmbient lower :=
  complexLpTwoMap (annularInnerLiftModeEnergy lower length positive bounded) (annularInnerLiftConstant lower length)
    (Real.sqrt_nonneg _) (annularInnerLiftMode_energy_bound lower length positive bounded)

theorem annularInnerLiftRaw_apply (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (boundary : AnnularBoundary) (mode : HighAnnularMode) :
    annularInnerLiftRaw lower length positive bounded boundary mode =
      annularModeEnergyCore lower length positive mode.val.1 mode.val.2 (annularInnerLiftMode lower mode (boundary mode)) := rfl

theorem annularInnerLiftRaw_single (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : HighAnnularMode) (vector : ComplexEuclidean 1) :
    annularInnerLiftRaw lower length positive bounded (lp.single 2 mode vector) =
      finiteAnnularEnergyCore lower length positive (Finsupp.single mode (annularInnerLiftMode lower mode vector)) := by
  classical
  apply lp.ext
  funext index
  rw [annularInnerLiftRaw_apply, finiteAnnularEnergyCore_apply]
  simp only [lp.single_apply, Pi.single_apply, Finsupp.single_apply]
  by_cases same : mode = index
  · subst index
    simp only [ite_true]
  · simp only [same, Ne.symm same, ite_false, map_zero]

theorem annularInnerLiftRaw_mem (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (boundary : AnnularBoundary) :
    annularInnerLiftRaw lower length positive bounded boundary ∈ annularEnergySpace lower length positive := by
  let domain := (annularEnergySpace lower length positive).comap
    (annularInnerLiftRaw lower length positive bounded).toLinearMap
  have closed : IsClosed (domain : Set AnnularBoundary) :=
    (LinearMap.range (finiteAnnularEnergyCore lower length positive)).isClosed_topologicalClosure.preimage
      (annularInnerLiftRaw lower length positive bounded).continuous
  have single (mode : HighAnnularMode) (vector : ComplexEuclidean 1) : lp.single 2 mode vector ∈ domain := by
    change annularInnerLiftRaw lower length positive bounded (lp.single 2 mode vector) ∈ annularEnergySpace lower length positive
    rw [annularInnerLiftRaw_single]
    exact Submodule.le_topologicalClosure _ ⟨Finsupp.single mode (annularInnerLiftMode lower mode vector), rfl⟩
  apply closed.mem_of_tendsto (lp.hasSum_single (by norm_num) boundary)
  exact Filter.Eventually.of_forall (fun support => domain.sum_mem (fun mode _ => single mode (boundary mode)))

def annularInnerLift (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    AnnularBoundary →L[ℂ] annularEnergySpace lower length positive :=
  (annularInnerLiftRaw lower length positive bounded).codRestrict _
    (annularInnerLiftRaw_mem lower length positive bounded)

theorem annularInnerLift_bound (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (boundary : AnnularBoundary) :
    ‖annularInnerLift lower length positive bounded boundary‖ ≤ annularInnerLiftConstant lower length * ‖boundary‖ := by
  change ‖annularInnerLiftRaw lower length positive bounded boundary‖ ≤ _
  exact complexLpTwoMap_bound (annularInnerLiftModeEnergy lower length positive bounded)
    (annularInnerLiftConstant lower length) (Real.sqrt_nonneg _)
    (annularInnerLiftMode_energy_bound lower length positive bounded) boundary

theorem annularInnerLift_single (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : HighAnnularMode) (vector : ComplexEuclidean 1) :
    annularInnerLift lower length positive bounded (lp.single 2 mode vector) =
      annularEnergyCoreInto lower length positive (Finsupp.single mode (annularInnerLiftMode lower mode vector)) :=
  Subtype.ext (annularInnerLiftRaw_single lower length positive bounded mode vector)

theorem annularBoundaryLinearMap_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (first second : AnnularBoundary →L[ℂ] E)
    (same : ∀ mode vector, first (lp.single 2 mode vector) = second (lp.single 2 mode vector)) : first = second := by
  apply ContinuousLinearMap.ext
  intro boundary
  have member : boundary ∈ (first - second).ker := by
    apply (first - second).isClosed_ker.mem_of_tendsto (lp.hasSum_single (by norm_num) boundary)
    apply Filter.Eventually.of_forall
    intro support
    apply (first - second).ker.sum_mem
    intro mode _
    change first (lp.single 2 mode (boundary mode)) - second (lp.single 2 mode (boundary mode)) = 0
    exact sub_eq_zero.mpr (same mode (boundary mode))
  exact sub_eq_zero.mp member

theorem annularInnerLift_inner (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (lengthPositive : 0 < length) (boundary : AnnularBoundary) :
    annularEnergyTrace lower length positive bounded lengthPositive 0
      (annularInnerLift lower length positive bounded boundary) = boundary := by
  have maps : (annularEnergyTrace lower length positive bounded lengthPositive 0).comp
      (annularInnerLift lower length positive bounded) = ContinuousLinearMap.id ℂ AnnularBoundary := by
    apply annularBoundaryLinearMap_ext
    intro mode vector
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, annularInnerLift_single, annularEnergyTrace_core]
    apply lp.ext
    funext index
    rw [finiteAnnularTraceCore_apply]
    classical
    simp only [Finsupp.single_apply, lp.single_apply, Pi.single_apply]
    by_cases same : mode = index
    · subst index
      simpa only [ite_true, Grad.AnnularSourceGraph.radialEndpointRadius] using annularInnerLiftMode_inner lower mode vector
    · simp [same, Ne.symm same]
  exact congrArg (fun mapping : AnnularBoundary →L[ℂ] AnnularBoundary => mapping boundary) maps

theorem annularInnerLift_outer (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (lengthPositive : 0 < length) (boundary : AnnularBoundary) :
    annularEnergyTrace lower length positive bounded lengthPositive 1
      (annularInnerLift lower length positive bounded boundary) = 0 := by
  have maps : (annularEnergyTrace lower length positive bounded lengthPositive 1).comp
      (annularInnerLift lower length positive bounded) = 0 := by
    apply annularBoundaryLinearMap_ext
    intro mode vector
    simp only [ContinuousLinearMap.comp_apply, zero_apply, annularInnerLift_single, annularEnergyTrace_core]
    apply lp.ext
    funext index
    rw [finiteAnnularTraceCore_apply]
    classical
    simp only [Finsupp.single_apply, lp.coeFn_zero, Pi.zero_apply]
    by_cases same : mode = index
    · subst index
      simp only [ite_true, show Grad.AnnularSourceGraph.radialEndpointRadius lower (1 : Fin 2) = 1 from rfl,
        annularInnerLiftMode_outer lower bounded, smul_zero]
    · simp [same]
  exact congrArg (fun mapping : AnnularBoundary →L[ℂ] AnnularBoundary => mapping boundary) maps

end Grad.AnnularVariational

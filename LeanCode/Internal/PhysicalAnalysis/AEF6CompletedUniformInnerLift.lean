import AEF5UniformInnerEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularUniformBoundary
open Grad.ClosedJets Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularSourceGraph

def uniformInnerLiftModeEnergy (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length) (mode : HighAnnularMode) :
    ComplexEuclidean 1 →L[ℂ] AnnularModeEnergyAmbient lower :=
  ((annularModeEnergyCore lower length positive mode.val.1 mode.val.2).comp
    (uniformInnerLiftMode lower mode)).mkContinuous
    (uniformInnerLiftConstant length)
    (uniformInnerLiftMode_energy_bound lower length positive lowerHalf lengthPositive mode)

def uniformInnerLiftRaw (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length) :
    AnnularBoundary →L[ℂ] AnnularEnergyAmbient lower :=
  complexLpTwoMap (uniformInnerLiftModeEnergy lower length positive lowerHalf lengthPositive)
    (uniformInnerLiftConstant length) (Real.sqrt_nonneg _)
    (uniformInnerLiftMode_energy_bound lower length positive lowerHalf lengthPositive)

@[simp] theorem uniformInnerLiftRaw_apply (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (boundary : AnnularBoundary) (mode : HighAnnularMode) :
    uniformInnerLiftRaw lower length positive lowerHalf lengthPositive boundary mode =
      annularModeEnergyCore lower length positive mode.val.1 mode.val.2
        (uniformInnerLiftMode lower mode (boundary mode)) := rfl

theorem uniformInnerLiftRaw_single (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (mode : HighAnnularMode) (vector : ComplexEuclidean 1) :
    uniformInnerLiftRaw lower length positive lowerHalf lengthPositive (lp.single 2 mode vector) =
      finiteAnnularEnergyCore lower length positive
        (Finsupp.single mode (uniformInnerLiftMode lower mode vector)) := by
  classical
  apply lp.ext
  funext index
  rw [uniformInnerLiftRaw_apply, finiteAnnularEnergyCore_apply]
  simp only [lp.single_apply, Pi.single_apply, Finsupp.single_apply]
  by_cases same : mode = index
  · subst index
    simp only [ite_true]
  · simp only [same, Ne.symm same, ite_false, map_zero]

theorem uniformInnerLiftRaw_mem (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length) (boundary : AnnularBoundary) :
    uniformInnerLiftRaw lower length positive lowerHalf lengthPositive boundary ∈
      annularEnergySpace lower length positive := by
  let domain := (annularEnergySpace lower length positive).comap
    (uniformInnerLiftRaw lower length positive lowerHalf lengthPositive).toLinearMap
  have closed : IsClosed (domain : Set AnnularBoundary) :=
    (LinearMap.range (finiteAnnularEnergyCore lower length positive)).isClosed_topologicalClosure.preimage
      (uniformInnerLiftRaw lower length positive lowerHalf lengthPositive).continuous
  have single (mode : HighAnnularMode) (vector : ComplexEuclidean 1) :
      lp.single 2 mode vector ∈ domain := by
    change uniformInnerLiftRaw lower length positive lowerHalf lengthPositive
      (lp.single 2 mode vector) ∈ annularEnergySpace lower length positive
    rw [uniformInnerLiftRaw_single]
    exact Submodule.le_topologicalClosure _
      ⟨Finsupp.single mode (uniformInnerLiftMode lower mode vector), rfl⟩
  apply closed.mem_of_tendsto (lp.hasSum_single (by norm_num) boundary)
  exact Filter.Eventually.of_forall
    (fun support => domain.sum_mem (fun mode _ => single mode (boundary mode)))

/-- Completed uniform lift into the original physical AAG energy carrier. -/
def uniformInnerLift (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length) :
    AnnularBoundary →L[ℂ] annularEnergySpace lower length positive :=
  (uniformInnerLiftRaw lower length positive lowerHalf lengthPositive).codRestrict _
    (uniformInnerLiftRaw_mem lower length positive lowerHalf lengthPositive)

theorem uniformInnerLift_bound (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length) (boundary : AnnularBoundary) :
    ‖uniformInnerLift lower length positive lowerHalf lengthPositive boundary‖ ≤
      uniformInnerLiftConstant length * ‖boundary‖ := by
  change ‖uniformInnerLiftRaw lower length positive lowerHalf lengthPositive boundary‖ ≤ _
  exact complexLpTwoMap_bound
    (uniformInnerLiftModeEnergy lower length positive lowerHalf lengthPositive)
    (uniformInnerLiftConstant length) (Real.sqrt_nonneg _)
    (uniformInnerLiftMode_energy_bound lower length positive lowerHalf lengthPositive) boundary

@[simp] theorem uniformInnerLift_single (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (mode : HighAnnularMode) (vector : ComplexEuclidean 1) :
    uniformInnerLift lower length positive lowerHalf lengthPositive (lp.single 2 mode vector) =
      annularEnergyCoreInto lower length positive
        (Finsupp.single mode (uniformInnerLiftMode lower mode vector)) :=
  Subtype.ext (uniformInnerLiftRaw_single lower length positive lowerHalf lengthPositive mode vector)

@[simp] theorem uniformInnerLift_inner (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length) (boundary : AnnularBoundary) :
    annularEnergyTrace lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
      (uniformInnerLift lower length positive lowerHalf lengthPositive boundary) = boundary := by
  have maps : (annularEnergyTrace lower length positive (lowerHalf.trans_lt (by norm_num))
      lengthPositive 0).comp (uniformInnerLift lower length positive lowerHalf lengthPositive) =
      ContinuousLinearMap.id ℂ AnnularBoundary := by
    apply annularBoundaryLinearMap_ext
    intro mode vector
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      uniformInnerLift_single, annularEnergyTrace_core]
    apply lp.ext
    funext index
    rw [finiteAnnularTraceCore_apply]
    classical
    simp only [Finsupp.single_apply, lp.single_apply, Pi.single_apply]
    by_cases same : mode = index
    · subst index
      simpa only [ite_true, radialEndpointRadius] using
        uniformInnerLiftMode_inner lower positive lowerHalf mode vector
    · simp [same, Ne.symm same]
  exact congrArg (fun mapping : AnnularBoundary →L[ℂ] AnnularBoundary => mapping boundary) maps

@[simp] theorem uniformInnerLift_outer (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length) (boundary : AnnularBoundary) :
    annularEnergyTrace lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 1
      (uniformInnerLift lower length positive lowerHalf lengthPositive boundary) = 0 := by
  have maps : (annularEnergyTrace lower length positive (lowerHalf.trans_lt (by norm_num))
      lengthPositive 1).comp (uniformInnerLift lower length positive lowerHalf lengthPositive) = 0 := by
    apply annularBoundaryLinearMap_ext
    intro mode vector
    simp only [ContinuousLinearMap.comp_apply, zero_apply, uniformInnerLift_single,
      annularEnergyTrace_core]
    apply lp.ext
    funext index
    rw [finiteAnnularTraceCore_apply]
    classical
    simp only [Finsupp.single_apply, lp.coeFn_zero, Pi.zero_apply]
    by_cases same : mode = index
    · subst index
      simp only [ite_true, show radialEndpointRadius lower (1 : Fin 2) = 1 from rfl,
        uniformInnerLiftMode_outer, smul_zero]
    · simp [same]
  exact congrArg (fun mapping : AnnularBoundary →L[ℂ] AnnularBoundary => mapping boundary) maps

end Grad.AnnularUniformBoundary

import PhysicalSimilarity
import Mathlib.Tactic.Module

noncomputable section

open Set

namespace Grad.MainAssembly.RoundAxisSimilarity

open Grad.MainTarget

private def axisPoint (radius angle : ℝ) : Vec :=
  vector (radius * Real.cos angle) (radius * Real.sin angle) 0

private theorem axisPoint_mem (radius angle : ℝ) :
    axisPoint radius angle ∈ roundAxis radius :=
  ⟨angle, rfl⟩

private theorem neg_mem_roundAxis (radius : ℝ) {point : Vec}
    (membership : point ∈ roundAxis radius) :
    -point ∈ roundAxis radius := by
  rcases membership with ⟨angle, rfl⟩
  refine ⟨angle + Real.pi, ?_⟩
  ext coordinate
  fin_cases coordinate <;>
    simp [vector, Real.cos_add, Real.sin_add]

theorem norm_eq_abs_radius_of_mem_roundAxis (radius : ℝ) {point : Vec}
    (membership : point ∈ roundAxis radius) :
    ‖point‖ = |radius| := by
  rcases membership with ⟨angle, rfl⟩
  apply (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq (F := Vec), sq_abs,
    PiLp.inner_apply]
  norm_num [vector, Fin.sum_univ_succ]
  nlinarith [Real.sin_sq_add_cos_sq angle]

theorem third_eq_zero_of_mem_roundAxis (radius : ℝ) {point : Vec}
    (membership : point ∈ roundAxis radius) :
    point 2 = 0 := by
  rcases membership with ⟨angle, rfl⟩
  rfl

private theorem reflected_mem_roundAxis
    (sourceRadius targetRadius spatialScale : ℝ)
    (orthogonal : Vec ≃ₗᵢ[ℝ] Vec) (translation : Vec)
    (axisEquality :
      (fun point : Vec => spatialScale • orthogonal point + translation) ''
          roundAxis sourceRadius = roundAxis targetRadius)
    {point : Vec} (membership : point ∈ roundAxis targetRadius) :
    (2 : ℝ) • translation - point ∈ roundAxis targetRadius := by
  rw [← axisEquality] at membership ⊢
  rcases membership with ⟨source, sourceMembership, rfl⟩
  refine ⟨-source, neg_mem_roundAxis sourceRadius sourceMembership, ?_⟩
  simp only [map_neg, smul_neg]
  module

private theorem inner_axisPoint_first (radius : ℝ) (point : Vec) :
    inner ℝ point (axisPoint radius 0) = radius * point 0 := by
  rw [PiLp.inner_apply]
  norm_num [axisPoint, vector, Fin.sum_univ_succ]

private theorem inner_axisPoint_second (radius : ℝ) (point : Vec) :
    inner ℝ point (axisPoint radius (Real.pi / 2)) = radius * point 1 := by
  rw [PiLp.inner_apply]
  norm_num [axisPoint, vector, Fin.sum_univ_succ]

/-- Exact `NG_R08`: a positive similarity carrying one positive-radius round
axis onto another has zero translation and scales the source radius to the
target radius.  The translation conclusion is obtained from the unique center
of the target circle, proved here by its antipodal points rather than assumed
as a property of similarities. -/
theorem roundAxis_similarity_scale_translation
    (sourceRadius targetRadius spatialScale : ℝ)
    (orthogonal : Vec ≃ₗᵢ[ℝ] Vec) (translation : Vec)
    (sourcePositive : 0 < sourceRadius) (targetPositive : 0 < targetRadius)
    (scalePositive : 0 < spatialScale)
    (axisEquality :
      (fun point : Vec => spatialScale • orthogonal point + translation) ''
          roundAxis sourceRadius = roundAxis targetRadius) :
    spatialScale * sourceRadius = targetRadius ∧ translation = 0 := by
  let first := axisPoint targetRadius 0
  let second := axisPoint targetRadius (Real.pi / 2)
  have firstMembership : first ∈ roundAxis targetRadius :=
    axisPoint_mem targetRadius 0
  have negativeFirstMembership : -first ∈ roundAxis targetRadius :=
    neg_mem_roundAxis targetRadius firstMembership
  have secondMembership : second ∈ roundAxis targetRadius :=
    axisPoint_mem targetRadius (Real.pi / 2)
  have negativeSecondMembership : -second ∈ roundAxis targetRadius :=
    neg_mem_roundAxis targetRadius secondMembership
  have reflectedFirst := reflected_mem_roundAxis sourceRadius targetRadius
    spatialScale orthogonal translation axisEquality firstMembership
  have reflectedNegativeFirst := reflected_mem_roundAxis sourceRadius targetRadius
    spatialScale orthogonal translation axisEquality negativeFirstMembership
  have reflectedSecond := reflected_mem_roundAxis sourceRadius targetRadius
    spatialScale orthogonal translation axisEquality secondMembership
  have reflectedNegativeSecond := reflected_mem_roundAxis sourceRadius targetRadius
    spatialScale orthogonal translation axisEquality negativeSecondMembership
  have reflectedFirstNorm : ‖(2 : ℝ) • translation - first‖ = targetRadius := by
    simpa [abs_of_pos targetPositive] using
      norm_eq_abs_radius_of_mem_roundAxis targetRadius reflectedFirst
  have reflectedNegativeFirstNorm : ‖(2 : ℝ) • translation + first‖ = targetRadius := by
    have normIdentity :=
      norm_eq_abs_radius_of_mem_roundAxis targetRadius reflectedNegativeFirst
    simpa [abs_of_pos targetPositive, sub_neg_eq_add] using normIdentity
  have reflectedSecondNorm : ‖(2 : ℝ) • translation - second‖ = targetRadius := by
    simpa [abs_of_pos targetPositive] using
      norm_eq_abs_radius_of_mem_roundAxis targetRadius reflectedSecond
  have reflectedNegativeSecondNorm : ‖(2 : ℝ) • translation + second‖ = targetRadius := by
    have normIdentity :=
      norm_eq_abs_radius_of_mem_roundAxis targetRadius reflectedNegativeSecond
    simpa [abs_of_pos targetPositive, sub_neg_eq_add] using normIdentity
  have firstOrthogonal : inner ℝ ((2 : ℝ) • translation) first = 0 := by
    have addSquare := norm_add_sq_real ((2 : ℝ) • translation) first
    have subSquare := norm_sub_sq_real ((2 : ℝ) • translation) first
    rw [reflectedNegativeFirstNorm] at addSquare
    rw [reflectedFirstNorm] at subSquare
    linarith
  have secondOrthogonal : inner ℝ ((2 : ℝ) • translation) second = 0 := by
    have addSquare := norm_add_sq_real ((2 : ℝ) • translation) second
    have subSquare := norm_sub_sq_real ((2 : ℝ) • translation) second
    rw [reflectedNegativeSecondNorm] at addSquare
    rw [reflectedSecondNorm] at subSquare
    linarith
  have translationFirst : translation 0 = 0 := by
    rw [inner_axisPoint_first targetRadius ((2 : ℝ) • translation)] at firstOrthogonal
    rw [PiLp.smul_apply] at firstOrthogonal
    simp only [smul_eq_mul] at firstOrthogonal
    change targetRadius * (2 * translation 0) = 0 at firstOrthogonal
    nlinarith
  have translationSecond : translation 1 = 0 := by
    rw [inner_axisPoint_second targetRadius ((2 : ℝ) • translation)] at secondOrthogonal
    rw [PiLp.smul_apply] at secondOrthogonal
    simp only [smul_eq_mul] at secondOrthogonal
    change targetRadius * (2 * translation 1) = 0 at secondOrthogonal
    nlinarith
  have translationThird : translation 2 = 0 := by
    have thirdZero := third_eq_zero_of_mem_roundAxis targetRadius reflectedFirst
    rw [PiLp.sub_apply, PiLp.smul_apply] at thirdZero
    simp only [smul_eq_mul] at thirdZero
    change 2 * translation 2 - first 2 = 0 at thirdZero
    simp [first, axisPoint, vector] at thirdZero
    linarith
  have translationZero : translation = 0 := by
    ext coordinate
    fin_cases coordinate
    · exact translationFirst
    · exact translationSecond
    · exact translationThird
  refine ⟨?_, translationZero⟩
  let source := axisPoint sourceRadius 0
  have sourceMembership : source ∈ roundAxis sourceRadius :=
    axisPoint_mem sourceRadius 0
  have imageMembership :
      spatialScale • orthogonal source + translation ∈ roundAxis targetRadius := by
    rw [← axisEquality]
    exact ⟨source, sourceMembership, rfl⟩
  have imageNorm : ‖spatialScale • orthogonal source + translation‖ =
      targetRadius := by
    simpa [abs_of_pos targetPositive] using
      norm_eq_abs_radius_of_mem_roundAxis targetRadius imageMembership
  have sourceNorm : ‖source‖ = sourceRadius := by
    simpa [abs_of_pos sourcePositive] using
      norm_eq_abs_radius_of_mem_roundAxis sourceRadius sourceMembership
  rw [translationZero, add_zero, norm_smul, orthogonal.norm_map,
    sourceNorm, Real.norm_eq_abs, abs_of_pos scalePositive] at imageNorm
  exact imageNorm

/-- Equal-radius fixed-period consequence consumed by `NG_R17`. -/
theorem roundAxis_similarity_same_radius
    (radius spatialScale : ℝ) (orthogonal : Vec ≃ₗᵢ[ℝ] Vec)
    (translation : Vec) (radiusPositive : 0 < radius)
    (scalePositive : 0 < spatialScale)
    (axisEquality :
      (fun point : Vec => spatialScale • orthogonal point + translation) ''
          roundAxis radius = roundAxis radius) :
    spatialScale = 1 ∧ translation = 0 := by
  have conclusion := roundAxis_similarity_scale_translation radius radius
    spatialScale orthogonal translation radiusPositive radiusPositive
    scalePositive axisEquality
  constructor
  · nlinarith [conclusion.1]
  · exact conclusion.2

end Grad.MainAssembly.RoundAxisSimilarity

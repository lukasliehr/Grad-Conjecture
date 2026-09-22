import RoundAxisSimilarityProof
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section

open Set

namespace Grad.MainAssembly.CircleIsometryClassification

open Grad.MainTarget
open Grad.MainAssembly.RoundAxisSimilarity

/-- Radial unit vector in the plane of the distinguished round axis. -/
def axisRadial (angle : ℝ) : Vec :=
  vector (Real.cos angle) (Real.sin angle) 0

/-- Positively oriented tangent unit vector along the distinguished axis. -/
def axisTangent (angle : ℝ) : Vec :=
  vector (-Real.sin angle) (Real.cos angle) 0

/-- The constant second normal direction to the distinguished axis. -/
def axisVertical : Vec := vector 0 0 1

/-- Matrix of an ambient linear isometry in the literal target basis. -/
def coordinateMatrix (orthogonal : Vec ≃ₗᵢ[ℝ] Vec) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun row column => orthogonal (basisVector column) row

private theorem radius_smul_axisRadial_mem (radius angle : ℝ) :
    radius • axisRadial angle ∈ roundAxis radius := by
  refine ⟨angle, ?_⟩
  ext coordinate
  fin_cases coordinate <;> simp [axisRadial, vector]

private theorem axisRadial_norm (angle : ℝ) : ‖axisRadial angle‖ = 1 := by
  simpa [axisRadial, abs_one] using
    norm_eq_abs_radius_of_mem_roundAxis 1
      (radius_smul_axisRadial_mem 1 angle)

private theorem axisTangent_eq_radial (angle : ℝ) :
    axisTangent angle = axisRadial (angle + Real.pi / 2) := by
  ext coordinate
  fin_cases coordinate <;>
    simp [axisRadial, axisTangent, vector, Real.cos_add, Real.sin_add]

private theorem axisTangent_norm (angle : ℝ) : ‖axisTangent angle‖ = 1 := by
  rw [axisTangent_eq_radial, axisRadial_norm]

private theorem radial_inner_tangent (angle : ℝ) :
    inner ℝ (axisRadial angle) (axisTangent angle) = 0 := by
  rw [PiLp.inner_apply]
  norm_num [axisRadial, axisTangent, vector, Fin.sum_univ_succ]
  ring

private theorem radial_zero_eq_basis : axisRadial 0 = basisVector 0 := by
  ext coordinate
  fin_cases coordinate <;> simp [axisRadial, vector, basisVector]

private theorem tangent_zero_eq_basis : axisTangent 0 = basisVector 1 := by
  ext coordinate
  fin_cases coordinate <;> simp [axisTangent, vector, basisVector]

private theorem vertical_eq_basis : axisVertical = basisVector 2 := by
  ext coordinate
  fin_cases coordinate <;> simp [axisVertical, vector, basisVector]

private theorem axisVertical_norm : ‖axisVertical‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [← real_inner_self_eq_norm_sq (F := Vec), PiLp.inner_apply]
  norm_num [axisVertical, vector, Fin.sum_univ_succ]

private theorem plane_norm_coordinates {point : Vec} (thirdZero : point 2 = 0)
    (normOne : ‖point‖ = 1) : point 0 ^ 2 + point 1 ^ 2 = 1 := by
  have squared := congrArg (fun value : ℝ => value ^ 2) normOne
  rw [← real_inner_self_eq_norm_sq (F := Vec), PiLp.inner_apply] at squared
  norm_num [Fin.sum_univ_succ, thirdZero] at squared
  nlinarith

private theorem plane_inner_coordinates {first second : Vec}
    (firstThird : first 2 = 0) (secondThird : second 2 = 0)
    (orthogonal : inner ℝ first second = 0) :
    first 0 * second 0 + first 1 * second 1 = 0 := by
  rw [PiLp.inner_apply] at orthogonal
  norm_num [Fin.sum_univ_succ, firstThird, secondThird] at orthogonal
  nlinarith

private theorem radial_signed_combination (sign angle shift : ℝ)
    (signValue : sign = 1 ∨ sign = -1) :
    Real.cos angle • axisRadial shift +
        Real.sin angle • (sign • axisTangent shift) =
      axisRadial (sign * angle + shift) := by
  rcases signValue with signPositive | signNegative
  · subst sign
    ext coordinate
    fin_cases coordinate <;>
      simp [axisRadial, axisTangent, vector, Real.cos_add, Real.sin_add] <;>
      ring
  · subst sign
    rw [show (-1 : ℝ) * angle + shift = shift - angle by ring]
    ext coordinate
    fin_cases coordinate <;>
      simp [axisRadial, axisTangent, vector, Real.cos_sub, Real.sin_sub] <;>
      ring

private theorem tangent_signed_combination (sign angle shift : ℝ)
    (signValue : sign = 1 ∨ sign = -1) :
    -Real.sin angle • axisRadial shift +
        Real.cos angle • (sign • axisTangent shift) =
      sign • axisTangent (sign * angle + shift) := by
  rcases signValue with signPositive | signNegative
  · subst sign
    ext coordinate
    fin_cases coordinate <;>
      simp [axisRadial, axisTangent, vector, Real.cos_add, Real.sin_add] <;>
      ring
  · subst sign
    rw [show (-1 : ℝ) * angle + shift = shift - angle by ring]
    ext coordinate
    fin_cases coordinate <;>
      simp [axisRadial, axisTangent, vector, Real.cos_sub, Real.sin_sub] <;>
      ring

set_option maxHeartbeats 800000 in
/-- Exact `NG_R07`: an affine isometry preserving a positive round axis fixes
its center.  Its planar action has one orientation sign and angular shift,
its vertical action has an independent sign, and its determinant is their
product.  The tangent sign is kept separate from the radial normal direction. -/
theorem circlePreserving_isometry_classification
    (radius : ℝ) (orthogonal : Vec ≃ₗᵢ[ℝ] Vec) (translation : Vec)
    (radiusPositive : 0 < radius)
    (axisEquality :
      (fun point : Vec => orthogonal point + translation) '' roundAxis radius =
        roundAxis radius) :
    translation = 0 ∧
      ∃ tangentSign verticalSign angleShift : ℝ,
        (tangentSign = 1 ∨ tangentSign = -1) ∧
        (verticalSign = 1 ∨ verticalSign = -1) ∧
        (∀ angle,
          orthogonal (axisRadial angle) =
            axisRadial (tangentSign * angle + angleShift)) ∧
        (∀ angle,
          orthogonal (axisTangent angle) =
            tangentSign • axisTangent (tangentSign * angle + angleShift)) ∧
        orthogonal axisVertical = verticalSign • axisVertical ∧
        (coordinateMatrix orthogonal).det = tangentSign * verticalSign := by
  have fixed := roundAxis_similarity_same_radius radius 1 orthogonal translation
    radiusPositive zero_lt_one (by simpa using axisEquality)
  have translationZero : translation = 0 := fixed.2
  have mappedRadialThird (angle : ℝ) : (orthogonal (axisRadial angle)) 2 = 0 := by
    have imageMembership :
        orthogonal (radius • axisRadial angle) + translation ∈ roundAxis radius := by
      rw [← axisEquality]
      exact ⟨radius • axisRadial angle,
        radius_smul_axisRadial_mem radius angle, rfl⟩
    have thirdZero := third_eq_zero_of_mem_roundAxis radius imageMembership
    rw [translationZero, add_zero, map_smul, PiLp.smul_apply] at thirdZero
    simp only [smul_eq_mul] at thirdZero
    exact (mul_eq_zero.mp thirdZero).resolve_left radiusPositive.ne'
  let first := orthogonal (axisRadial 0)
  let second := orthogonal (axisTangent 0)
  have firstThird : first 2 = 0 := mappedRadialThird 0
  have secondThird : second 2 = 0 := by
    change (orthogonal (axisTangent 0)) 2 = 0
    rw [axisTangent_eq_radial]
    exact mappedRadialThird (0 + Real.pi / 2)
  have firstNorm : ‖first‖ = 1 := by
    rw [orthogonal.norm_map, axisRadial_norm]
  have secondNorm : ‖second‖ = 1 := by
    rw [orthogonal.norm_map, axisTangent_norm]
  have firstSquares : first 0 ^ 2 + first 1 ^ 2 = 1 :=
    plane_norm_coordinates firstThird firstNorm
  have secondSquares : second 0 ^ 2 + second 1 ^ 2 = 1 :=
    plane_norm_coordinates secondThird secondNorm
  have firstSecondInner : inner ℝ first second = 0 := by
    simpa [first, second] using orthogonal.inner_map_map
      (axisRadial 0) (axisTangent 0) |>.trans (radial_inner_tangent 0)
  have firstSecondCoordinates :
      first 0 * second 0 + first 1 * second 1 = 0 :=
    plane_inner_coordinates firstThird secondThird firstSecondInner
  let tangentSign : ℝ := first 0 * second 1 - first 1 * second 0
  have tangentSignSquare : tangentSign ^ 2 = 1 := by
    calc
      tangentSign ^ 2 =
          (first 0 ^ 2 + first 1 ^ 2) *
              (second 0 ^ 2 + second 1 ^ 2) -
            (first 0 * second 0 + first 1 * second 1) ^ 2 := by
              simp only [tangentSign]
              ring
      _ = 1 := by
        rw [firstSquares, secondSquares, firstSecondCoordinates]
        norm_num
  have tangentSignValue : tangentSign = 1 ∨ tangentSign = -1 :=
    sq_eq_one_iff.mp tangentSignSquare
  have secondFirstCoordinate : second 0 = -tangentSign * first 1 := by
    calc
      second 0 = (first 0 ^ 2 + first 1 ^ 2) * second 0 := by
        rw [firstSquares, one_mul]
      _ = first 0 *
            (first 0 * second 0 + first 1 * second 1) -
          tangentSign * first 1 := by
        simp only [tangentSign]
        ring
      _ = -tangentSign * first 1 := by
        rw [firstSecondCoordinates]
        ring
  have secondSecondCoordinate : second 1 = tangentSign * first 0 := by
    calc
      second 1 = (first 0 ^ 2 + first 1 ^ 2) * second 1 := by
        rw [firstSquares, one_mul]
      _ = first 1 *
            (first 0 * second 0 + first 1 * second 1) +
          tangentSign * first 0 := by
        simp only [tangentSign]
        ring
      _ = tangentSign * first 0 := by
        rw [firstSecondCoordinates]
        ring
  let planarComplex : ℂ := ⟨first 0, first 1⟩
  have planarComplexNorm : ‖planarComplex‖ = 1 := by
    rw [Complex.norm_def]
    simp only [Complex.normSq_apply, planarComplex]
    rw [show first 0 * first 0 + first 1 * first 1 = 1 by nlinarith [firstSquares]]
    norm_num
  have planarComplexNonzero : planarComplex ≠ 0 := by
    intro zero
    rw [zero, norm_zero] at planarComplexNorm
    norm_num at planarComplexNorm
  let angleShift : ℝ := Complex.arg planarComplex
  have firstCoordinateAngle : first 0 = Real.cos angleShift := by
    have cosine := Complex.cos_arg planarComplexNonzero
    rw [planarComplexNorm, div_one] at cosine
    exact cosine.symm
  have secondCoordinateAngle : first 1 = Real.sin angleShift := by
    have sine := Complex.sin_arg planarComplex
    rw [planarComplexNorm, div_one] at sine
    exact sine.symm
  have firstVector : first = axisRadial angleShift := by
    ext coordinate
    fin_cases coordinate
    · exact firstCoordinateAngle
    · exact secondCoordinateAngle
    · simpa [axisRadial, vector] using firstThird
  have secondVector : second = tangentSign • axisTangent angleShift := by
    ext coordinate
    fin_cases coordinate
    · simp [axisTangent, vector, secondFirstCoordinate, secondCoordinateAngle]
    · simp [axisTangent, vector, secondSecondCoordinate, firstCoordinateAngle]
    · simp [axisTangent, vector, secondThird]
  have radialExpansion (angle : ℝ) :
      axisRadial angle =
        Real.cos angle • axisRadial 0 + Real.sin angle • axisTangent 0 := by
    ext coordinate
    fin_cases coordinate <;> simp [axisRadial, axisTangent, vector]
  have tangentExpansion (angle : ℝ) :
      axisTangent angle =
        -Real.sin angle • axisRadial 0 + Real.cos angle • axisTangent 0 := by
    ext coordinate
    fin_cases coordinate <;> simp [axisRadial, axisTangent, vector]
  have radialAction (angle : ℝ) :
      orthogonal (axisRadial angle) =
        axisRadial (tangentSign * angle + angleShift) := by
    rw [radialExpansion, map_add, map_smul, map_smul]
    change Real.cos angle • first + Real.sin angle • second = _
    rw [firstVector, secondVector]
    exact radial_signed_combination tangentSign angle angleShift
      tangentSignValue
  have tangentAction (angle : ℝ) :
      orthogonal (axisTangent angle) =
        tangentSign • axisTangent (tangentSign * angle + angleShift) := by
    rw [tangentExpansion, map_add, map_smul, map_smul]
    change -Real.sin angle • first + Real.cos angle • second = _
    rw [firstVector, secondVector]
    exact tangent_signed_combination tangentSign angle angleShift
      tangentSignValue
  let verticalImage := orthogonal axisVertical
  have verticalFirstInner : inner ℝ verticalImage first = 0 := by
    calc
      inner ℝ verticalImage first =
          inner ℝ axisVertical (axisRadial 0) :=
        orthogonal.inner_map_map axisVertical (axisRadial 0)
      _ = 0 := by
        simp [axisVertical, axisRadial, vector, PiLp.inner_apply,
          Fin.sum_univ_succ]
  have verticalSecondInner : inner ℝ verticalImage second = 0 := by
    calc
      inner ℝ verticalImage second =
          inner ℝ axisVertical (axisTangent 0) :=
        orthogonal.inner_map_map axisVertical (axisTangent 0)
      _ = 0 := by
        simp [axisVertical, axisTangent, vector, PiLp.inner_apply,
          Fin.sum_univ_succ]
  have verticalFirstCoordinates :
      verticalImage 0 * first 0 + verticalImage 1 * first 1 = 0 := by
    rw [PiLp.inner_apply] at verticalFirstInner
    norm_num [Fin.sum_univ_succ, firstThird] at verticalFirstInner
    simpa [mul_comm] using verticalFirstInner
  have verticalSecondCoordinates :
      -first 1 * verticalImage 0 + first 0 * verticalImage 1 = 0 := by
    rw [PiLp.inner_apply] at verticalSecondInner
    norm_num [Fin.sum_univ_succ, secondThird] at verticalSecondInner
    have tangentSignNonzero : tangentSign ≠ 0 := by
      rcases tangentSignValue with signPositive | signNegative
      · rw [signPositive]
        norm_num
      · rw [signNegative]
        norm_num
    have factored :
        tangentSign *
          (-first 1 * verticalImage 0 + first 0 * verticalImage 1) = 0 := by
      calc
        tangentSign *
            (-first 1 * verticalImage 0 + first 0 * verticalImage 1) =
          second 0 * verticalImage 0 + second 1 * verticalImage 1 := by
            rw [secondFirstCoordinate, secondSecondCoordinate]
            ring
        _ = 0 := verticalSecondInner
    exact (mul_eq_zero.mp factored).resolve_left tangentSignNonzero
  have verticalFirst : verticalImage 0 = 0 := by
    calc
      verticalImage 0 =
          (first 0 ^ 2 + first 1 ^ 2) * verticalImage 0 := by
            rw [firstSquares]
            ring
      _ =
          first 0 * (verticalImage 0 * first 0 + verticalImage 1 * first 1) -
            first 1 * (-first 1 * verticalImage 0 + first 0 * verticalImage 1) := by
        ring
      _ = 0 := by
        rw [verticalFirstCoordinates, verticalSecondCoordinates]
        ring
  have verticalSecond : verticalImage 1 = 0 := by
    calc
      verticalImage 1 =
          (first 0 ^ 2 + first 1 ^ 2) * verticalImage 1 := by
            rw [firstSquares]
            ring
      _ =
          first 1 * (verticalImage 0 * first 0 + verticalImage 1 * first 1) +
            first 0 * (-first 1 * verticalImage 0 + first 0 * verticalImage 1) := by
        ring
      _ = 0 := by
        rw [verticalFirstCoordinates, verticalSecondCoordinates]
        ring
  have verticalNorm : ‖verticalImage‖ = 1 := by
    rw [orthogonal.norm_map, axisVertical_norm]
  have verticalThirdSquare : verticalImage 2 ^ 2 = 1 := by
    have squared : inner ℝ verticalImage verticalImage = 1 := by
      rw [real_inner_self_eq_norm_sq, verticalNorm]
      norm_num
    rw [PiLp.inner_apply] at squared
    norm_num [Fin.sum_univ_succ, verticalFirst, verticalSecond] at squared
    exact sq_eq_one_iff.mpr squared
  let verticalSign : ℝ := verticalImage 2
  have verticalSignValue : verticalSign = 1 ∨ verticalSign = -1 :=
    sq_eq_one_iff.mp verticalThirdSquare
  have verticalAction : orthogonal axisVertical = verticalSign • axisVertical := by
    change verticalImage = verticalSign • axisVertical
    ext coordinate
    fin_cases coordinate <;>
      simp [axisVertical, vector, verticalSign, verticalFirst, verticalSecond]
  have determinant :
      (coordinateMatrix orthogonal).det = tangentSign * verticalSign := by
    have mapFirstBasis : orthogonal (basisVector 0) = axisRadial angleShift := by
      rw [← radial_zero_eq_basis]
      simpa using radialAction 0
    have mapSecondBasis :
        orthogonal (basisVector 1) = tangentSign • axisTangent angleShift := by
      rw [← tangent_zero_eq_basis]
      simpa using tangentAction 0
    have mapThirdBasis :
        orthogonal (basisVector 2) = verticalSign • axisVertical := by
      rw [← vertical_eq_basis]
      exact verticalAction
    rw [Matrix.det_fin_three]
    simp only [coordinateMatrix]
    simp [mapFirstBasis, mapSecondBasis, mapThirdBasis, axisRadial,
      axisTangent, axisVertical, vector]
    calc
      Real.cos angleShift * (tangentSign * Real.cos angleShift) * verticalSign +
          tangentSign * Real.sin angleShift * Real.sin angleShift * verticalSign =
        tangentSign * verticalSign *
          (Real.sin angleShift ^ 2 + Real.cos angleShift ^ 2) := by ring
      _ = tangentSign * verticalSign := by
        rw [Real.sin_sq_add_cos_sq]
        ring
  exact ⟨translationZero, tangentSign, verticalSign, angleShift,
    tangentSignValue, verticalSignValue, radialAction, tangentAction,
    verticalAction, determinant⟩

end Grad.MainAssembly.CircleIsometryClassification

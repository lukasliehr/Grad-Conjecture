import BL8KernelBoundary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

noncomputable section

open Set Filter
open scoped BigOperators ContDiff Topology

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

def inverseCollarChart (point : SpatialPlane) : ℝ × ℝ :=
  (1 - ‖point‖, Real.arctan (point 1 / point 0))

def rightHalfPlane : Set SpatialPlane := {point | 0 < point 0}

theorem rightHalfPlane_open : IsOpen rightHalfPlane := by
  exact isOpen_lt continuous_const (by fun_prop)

theorem inverseCollarChart_smoothAt (point : SpatialPlane) (positive : 0 < point 0) :
    ContDiffAt ℝ ∞ inverseCollarChart point := by
  have nonzero : point ≠ 0 := by
    intro zeroPoint
    simp only [zeroPoint, PiLp.zero_apply, lt_self_iff_false] at positive
  have firstSmooth : ContDiff ℝ ∞ (fun source : SpatialPlane => source 0) := by fun_prop
  have secondSmooth : ContDiff ℝ ∞ (fun source : SpatialPlane => source 1) := by fun_prop
  exact (contDiffAt_const.sub (contDiffAt_norm ℝ nonzero)).prodMk
    (Real.contDiff_arctan.contDiffAt.comp point
      (secondSmooth.contDiffAt.div firstSmooth.contDiffAt positive.ne'))

theorem spatial_norm_sq_coordinates (point : SpatialPlane) :
    ‖point‖ ^ 2 = point 0 ^ 2 + point 1 ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  simp only [Real.norm_eq_abs, sq_abs]

theorem inverseCollarChart_sqrt (point : SpatialPlane) (positive : 0 < point 0) :
    Real.sqrt (1 + (point 1 / point 0) ^ 2) = ‖point‖ / point 0 := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (div_nonneg (norm_nonneg _) positive.le)).mp
  rw [Real.sq_sqrt (by positivity)]
  simp only [div_pow]
  rw [spatial_norm_sq_coordinates]
  field_simp [positive.ne']

theorem collarPlane_inverseCollarChart (point : SpatialPlane) (positive : 0 < point 0) :
    collarPlane (inverseCollarChart point) = point := by
  have normPositive : 0 < ‖point‖ := norm_pos_iff.mpr (by
    intro zeroPoint
    simp only [zeroPoint, PiLp.zero_apply, lt_self_iff_false] at positive)
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · change (1 - (1 - ‖point‖)) * Real.cos (Real.arctan (point 1 / point 0)) = point 0
    rw [sub_sub_cancel, Real.cos_arctan, inverseCollarChart_sqrt point positive]
    field_simp
  · change (1 - (1 - ‖point‖)) * Real.sin (Real.arctan (point 1 / point 0)) = point 1
    rw [sub_sub_cancel, Real.sin_arctan, inverseCollarChart_sqrt point positive]
    field_simp

def collarAxis (radius : ℝ) : SpatialPlane := WithLp.toLp 2 ![radius, 0]

theorem collarAxis_smooth : ContDiff ℝ ∞ collarAxis := by
  rw [contDiff_piLp]
  intro coordinate
  fin_cases coordinate <;> simp [collarAxis] <;> fun_prop

theorem collarAxis_norm (radius : ℝ) : ‖collarAxis radius‖ = |radius| := by
  rw [PiLp.norm_eq_of_L2, Fin.sum_univ_two]
  simpa [collarAxis] using Real.sqrt_sq_eq_abs radius

theorem inverseCollarChart_axis (radius : ℝ) (positive : 0 < radius) :
    inverseCollarChart (collarAxis radius) = (1 - radius, 0) := by
  unfold inverseCollarChart
  rw [collarAxis_norm, abs_of_pos positive]
  simp [collarAxis]

def inverseChartEnvelope (grade : ℕ) (point : SpatialPlane) : ℝ :=
  1 + ∑ order ∈ Finset.range (grade + 1), ‖iteratedFDeriv ℝ order inverseCollarChart point‖

theorem inverseChartEnvelope_continuousOn (grade : ℕ) :
    ContinuousOn (fun radius => inverseChartEnvelope grade (collarAxis radius))
      (Icc (3 / 4 : ℝ) 1) := by
  intro radius inside
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_const.add
  apply tendsto_finsetSum
  intro order _
  have positive : 0 < (collarAxis radius) 0 := by
    change 0 < radius
    linarith [inside.1]
  exact (((inverseCollarChart_smoothAt (collarAxis radius) positive).continuousAt_iteratedFDeriv
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).norm).comp
      collarAxis_smooth.continuous.continuousAt

theorem exists_inverseChart_bound (grade : ℕ) : ∃ bound : ℝ, 1 ≤ bound ∧
    ∀ radius ∈ Icc (3 / 4 : ℝ) 1, inverseChartEnvelope grade (collarAxis radius) ≤ bound := by
  obtain ⟨bound, property⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image (inverseChartEnvelope_continuousOn grade))
  refine ⟨max 1 bound, le_max_left _ _, ?_⟩
  intro radius inside
  exact (property _ ⟨radius, inside, rfl⟩).trans (le_max_right _ _)

def inverseChartBound (grade : ℕ) : ℝ := Classical.choose (exists_inverseChart_bound grade)

theorem inverseChartBound_one_le (grade : ℕ) : 1 ≤ inverseChartBound grade :=
  (Classical.choose_spec (exists_inverseChart_bound grade)).1

theorem inverseChart_derivative_bound (grade order : ℕ) (upper : order ≤ grade)
    (radius : ℝ) (inside : radius ∈ Icc (3 / 4 : ℝ) 1) :
    ‖iteratedFDeriv ℝ order inverseCollarChart (collarAxis radius)‖ ≤ inverseChartBound grade := by
  have term := Finset.single_le_sum (s := Finset.range (grade + 1))
    (f := fun index => ‖iteratedFDeriv ℝ index inverseCollarChart (collarAxis radius)‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (by omega : order < grade + 1))
  have aggregate := (Classical.choose_spec (exists_inverseChart_bound grade)).2 radius inside
  exact term.trans ((le_add_of_nonneg_left zero_le_one).trans aggregate)

end Grad.BoundaryLift

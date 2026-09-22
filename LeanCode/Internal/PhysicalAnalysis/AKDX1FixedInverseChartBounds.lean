import BL12TensorCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter
open scoped BigOperators ContDiff Topology
namespace Grad.OriginalCollarNorm
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints Grad.BoundaryLift

theorem inverseChartEnvelope_continuousOn (lower : ℝ) (positive : 0<lower) (grade : ℕ) :
    ContinuousOn (fun radius => inverseChartEnvelope grade (collarAxis radius))
      (Icc lower 1) := by
  intro radius inside
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_const.add
  apply tendsto_finsetSum
  intro order _
  have radiusPositive : 0 < (collarAxis radius) 0 := positive.trans_le inside.1
  exact (((inverseCollarChart_smoothAt (collarAxis radius) radiusPositive).continuousAt_iteratedFDeriv
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).norm).comp
      collarAxis_smooth.continuous.continuousAt

theorem exists_inverseChart_bound (lower : ℝ) (positive : 0<lower) (grade : ℕ) : ∃ bound : ℝ, 1 ≤ bound ∧
    ∀ radius ∈ Icc lower 1, inverseChartEnvelope grade (collarAxis radius) ≤ bound := by
  obtain ⟨bound, property⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image (inverseChartEnvelope_continuousOn lower positive grade))
  refine ⟨max 1 bound, le_max_left _ _, ?_⟩
  intro radius inside
  exact (property _ ⟨radius, inside, rfl⟩).trans (le_max_right _ _)

def inverseChartBound (lower : ℝ) (positive : 0<lower) (grade : ℕ) : ℝ := Classical.choose (exists_inverseChart_bound lower positive grade)

theorem inverseChartBound_one_le (lower : ℝ) (positive : 0<lower) (grade : ℕ) : 1 ≤ inverseChartBound lower positive grade :=
  (Classical.choose_spec (exists_inverseChart_bound lower positive grade)).1

theorem inverseChart_derivative_bound (lower : ℝ) (positive : 0<lower) (grade order : ℕ) (upper : order ≤ grade)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    ‖iteratedFDeriv ℝ order inverseCollarChart (collarAxis radius)‖ ≤ inverseChartBound lower positive grade := by
  have term := Finset.single_le_sum (s := Finset.range (grade + 1))
    (f := fun index => ‖iteratedFDeriv ℝ index inverseCollarChart (collarAxis radius)‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (by omega : order < grade + 1))
  have aggregate := (Classical.choose_spec (exists_inverseChart_bound lower positive grade)).2 radius inside
  exact term.trans ((le_add_of_nonneg_left zero_le_one).trans aggregate)

end Grad.OriginalCollarNorm

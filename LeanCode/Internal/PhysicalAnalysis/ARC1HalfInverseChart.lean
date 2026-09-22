import BL12TensorCoordinates

noncomputable section
open Set Filter
open scoped BigOperators ContDiff Topology
namespace Grad.CollarCartesian
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints Grad.BoundaryLift

theorem inverseChartEnvelope_continuousOn (grade : ℕ) :
    ContinuousOn (fun radius => inverseChartEnvelope grade (collarAxis radius))
      (Icc (1 / 2 : ℝ) 1) := by
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
    ∀ radius ∈ Icc (1 / 2 : ℝ) 1, inverseChartEnvelope grade (collarAxis radius) ≤ bound := by
  obtain ⟨bound, property⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image (inverseChartEnvelope_continuousOn grade))
  refine ⟨max 1 bound, le_max_left _ _, ?_⟩
  intro radius inside
  exact (property _ ⟨radius, inside, rfl⟩).trans (le_max_right _ _)

def inverseChartBound (grade : ℕ) : ℝ := Classical.choose (exists_inverseChart_bound grade)

theorem inverseChartBound_one_le (grade : ℕ) : 1 ≤ inverseChartBound grade :=
  (Classical.choose_spec (exists_inverseChart_bound grade)).1

theorem inverseChart_derivative_bound (grade order : ℕ) (upper : order ≤ grade)
    (radius : ℝ) (inside : radius ∈ Icc (1 / 2 : ℝ) 1) :
    ‖iteratedFDeriv ℝ order inverseCollarChart (collarAxis radius)‖ ≤ inverseChartBound grade := by
  have term := Finset.single_le_sum (s := Finset.range (grade + 1))
    (f := fun index => ‖iteratedFDeriv ℝ index inverseCollarChart (collarAxis radius)‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (by omega : order < grade + 1))
  have aggregate := (Classical.choose_spec (exists_inverseChart_bound grade)).2 radius inside
  exact term.trans ((le_add_of_nonneg_left zero_le_one).trans aggregate)

end Grad.CollarCartesian

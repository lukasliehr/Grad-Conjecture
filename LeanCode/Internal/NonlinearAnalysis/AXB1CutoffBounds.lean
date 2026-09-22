import AXL24LiftLinearity
import Q23CompletedMultiplier

noncomputable section

set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.NonlinearProduct Grad.ChartAxisSplit
open Grad.Constraints.Gauges Grad.Constraints.Multipliers

variable {parameters : PhaseParameters}

/-- The literal seed matrix is uniformly bounded at the same original grade
on every compact admissible seed patch.  This includes the identity summand;
no coefficient or spatial grade is shifted. -/
theorem seedMatrixCore_bound_on_patch (grade : ℕ)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ seed ∈ seedPatch, ∀ (inside : seed ∈ Seed.parameterDomain)
        (field : ACore parameters 2),
        originalGradeNorm grade (seedMatrixCore parameters seed inside field) ≤
          constant * originalGradeNorm grade field := by
  obtain ⟨seedConstant, seedNonnegative, seedBound⟩ :=
    completedSeedParameterDerivative_compact_bound parameters grade 0 seedPatch compact insidePatch
  refine ⟨1 + seedConstant, by linarith, ?_⟩
  intro seed member inside field
  have operatorBound := seedBound 0 seed member (fun position => position.elim0)
  rw [Fin.prod_univ_zero, mul_one] at operatorBound
  have evaluation :=
    (completedSeedParameterDerivative parameters grade 0 0 seed
      (fun position => position.elim0)).le_opNorm
        (aGradeEta parameters (GradeCore.ofCoreLinear field))
  rw [completedSeedParameterDerivative_core parameters grade 0 0 seed inside,
    aGradeEta_norm, aGradeEta_norm] at evaluation
  have deviation : originalGradeNorm grade (seedDeviationCore parameters seed inside 0 field) ≤
      seedConstant * originalGradeNorm grade field := by
    have bound := evaluation.trans
      (mul_le_mul_of_nonneg_right operatorBound (originalGradeNorm_nonnegative grade field))
    change originalGradeNorm grade
        (smoothMultiplier parameters (Seed.actualCells 0 seed)
          (seedCells_all_summable parameters seed inside 0) field) ≤
      seedConstant * originalGradeNorm grade field
    rw [← seedParameterMultiplier_zero parameters 0 seed inside field]
    exact bound
  change originalGradeNorm grade (field + seedDeviationCore parameters seed inside 0 field) ≤
    (1 + seedConstant) * originalGradeNorm grade field
  have triangle := originalGradeNorm_add_le grade field
    (seedDeviationCore parameters seed inside 0 field)
  nlinarith [originalGradeNorm_nonnegative grade field]

theorem capSeedField_difference_eq (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) :
    capSeedField parameters radius positive seed inside - tameSeedField parameters seed inside =
      valueMapCore parameters tamePlanarInclusion
        (seedMatrixCore parameters seed inside
          (capPlanarCoordinate parameters radius positive - tamePlanarCoordinateField parameters)) := by
  unfold capSeedField tameSeedField tameSeedPlanarField
  rw [map_sub, map_sub]

/-- The fixed radial cutoff error in the seed field is uniformly bounded on
a compact seed patch, still at exactly the requested original grade. -/
theorem capSeedField_difference_bound_on_patch (radius : ℝ) (positive : 0 < radius)
    (grade : ℕ) (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ seed ∈ seedPatch, ∀ (inside : seed ∈ Seed.parameterDomain),
        originalGradeNorm grade
          (capSeedField parameters radius positive seed inside - tameSeedField parameters seed inside) ≤
          constant := by
  obtain ⟨seedConstant, seedNonnegative, seedBound⟩ :=
    seedMatrixCore_bound_on_patch (parameters := parameters) grade seedPatch compact insidePatch
  let cutoffDifference : ACore parameters 2 :=
    capPlanarCoordinate parameters radius positive - tamePlanarCoordinateField parameters
  refine ⟨‖tamePlanarInclusion‖ * seedConstant * originalGradeNorm grade cutoffDifference,
    mul_nonneg (mul_nonneg (norm_nonneg _) seedNonnegative)
      (originalGradeNorm_nonnegative grade cutoffDifference), ?_⟩
  intro seed member inside
  rw [capSeedField_difference_eq radius positive seed inside]
  have matrixBound := seedBound seed member inside cutoffDifference
  have inclusionBound := valueMapCore_bound tamePlanarInclusion
    (seedMatrixCore parameters seed inside cutoffDifference) grade
  exact (inclusionBound.trans
    (mul_le_mul_of_nonneg_left matrixBound (norm_nonneg _))).trans_eq (by ring)

/-- Algebraic expansion of the cap chart remainder into one seed-cutoff
multiplier and the two fixed scalar-cutoff multipliers. -/
theorem capChartRemainder_expansion (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (tangent : TangentCoefficient parameters) :
    capChartRemainder parameters radius positive seed inside coefficient tangent =
      tameScalarMultiplier 3 coefficient
          (capSeedField parameters radius positive seed inside - tameSeedField parameters seed inside) +
        valueMapCore parameters tameTangentInclusion
          (tameScalarMultiplier 1 (tangentComponent tangent 0)
              (capScalarCoordinate parameters radius positive 0 -
                tameCoordinateScalarField parameters 0) +
            tameScalarMultiplier 1 (tangentComponent tangent 1)
              (capScalarCoordinate parameters radius positive 1 -
                tameCoordinateScalarField parameters 1)) := by
  unfold capChartRemainder capAffineField chartAffineField
  simp only [map_add, map_sub]
  abel

end Grad.ChartAxisLift

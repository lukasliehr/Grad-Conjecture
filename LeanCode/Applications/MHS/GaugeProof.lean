import GaugeInterface

noncomputable section

set_option maxHeartbeats 6400000

open scoped BigOperators

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers

/-- The triangular projection of the actual corrections is bounded at every
grade by one plus the two correction constants, composed in the written
order. -/
def triangularGradeConstant (phase : PhaseParameters) (parameter : Seed.Parameters)
    (grade : ℕ) : ℝ :=
  (1 + toroidalGradeConstant phase parameter grade) *
    (1 + poloidalGradeConstant phase parameter grade)

theorem triangularGradeConstant_nonneg (phase : PhaseParameters)
    (parameter : Seed.Parameters) (grade : ℕ) :
    0 ≤ triangularGradeConstant phase parameter grade :=
  mul_nonneg
    (add_nonneg zero_le_one (toroidalGradeConstant_nonneg phase parameter grade))
    (add_nonneg zero_le_one (poloidalGradeConstant_nonneg phase parameter grade))

theorem triangularGaugeProjection_apply (phase : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (field : ACore phase 3) :
    triangularGaugeProjection phase parameter inside field =
      (field - poloidalCorrection phase parameter inside field) -
        toroidalCorrection phase parameter inside
          (field - poloidalCorrection phase parameter inside field) := rfl

theorem triangularGaugeProjection_coordinates_bound (phase : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    {grade : ℕ} (field : ACore phase 3) :
    ‖cartesianGradeCoordinates phase grade
        (triangularGaugeProjection phase parameter inside field)‖ ≤
      triangularGradeConstant phase parameter grade *
        ‖cartesianGradeCoordinates phase grade field‖ := by
  have firstStage : ‖cartesianGradeCoordinates phase grade
      (field - poloidalCorrection phase parameter inside field)‖ ≤
      (1 + poloidalGradeConstant phase parameter grade) *
        ‖cartesianGradeCoordinates phase grade field‖ := by
    rw [map_sub]
    calc ‖cartesianGradeCoordinates phase grade field -
          cartesianGradeCoordinates phase grade
            (poloidalCorrection phase parameter inside field)‖
        ≤ ‖cartesianGradeCoordinates phase grade field‖ +
            ‖cartesianGradeCoordinates phase grade
              (poloidalCorrection phase parameter inside field)‖ := norm_sub_le _ _
      _ ≤ ‖cartesianGradeCoordinates phase grade field‖ +
            poloidalGradeConstant phase parameter grade *
              ‖cartesianGradeCoordinates phase grade field‖ :=
          add_le_add le_rfl (poloidalCorrection_coordinates_bound phase parameter inside field)
      _ = (1 + poloidalGradeConstant phase parameter grade) *
            ‖cartesianGradeCoordinates phase grade field‖ := by ring
  have secondStage : ‖cartesianGradeCoordinates phase grade
      (triangularGaugeProjection phase parameter inside field)‖ ≤
      (1 + toroidalGradeConstant phase parameter grade) *
        ‖cartesianGradeCoordinates phase grade
          (field - poloidalCorrection phase parameter inside field)‖ := by
    rw [triangularGaugeProjection_apply, map_sub]
    calc ‖cartesianGradeCoordinates phase grade
            (field - poloidalCorrection phase parameter inside field) -
          cartesianGradeCoordinates phase grade (toroidalCorrection phase parameter inside
            (field - poloidalCorrection phase parameter inside field))‖
        ≤ ‖cartesianGradeCoordinates phase grade
              (field - poloidalCorrection phase parameter inside field)‖ +
            ‖cartesianGradeCoordinates phase grade (toroidalCorrection phase parameter inside
              (field - poloidalCorrection phase parameter inside field))‖ := norm_sub_le _ _
      _ ≤ ‖cartesianGradeCoordinates phase grade
              (field - poloidalCorrection phase parameter inside field)‖ +
            toroidalGradeConstant phase parameter grade *
              ‖cartesianGradeCoordinates phase grade
                (field - poloidalCorrection phase parameter inside field)‖ :=
          add_le_add le_rfl (toroidalCorrection_coordinates_bound phase parameter inside _)
      _ = (1 + toroidalGradeConstant phase parameter grade) *
            ‖cartesianGradeCoordinates phase grade
              (field - poloidalCorrection phase parameter inside field)‖ := by ring
  calc ‖cartesianGradeCoordinates phase grade
        (triangularGaugeProjection phase parameter inside field)‖
      ≤ (1 + toroidalGradeConstant phase parameter grade) *
          ‖cartesianGradeCoordinates phase grade
            (field - poloidalCorrection phase parameter inside field)‖ := secondStage
    _ ≤ (1 + toroidalGradeConstant phase parameter grade) *
          ((1 + poloidalGradeConstant phase parameter grade) *
            ‖cartesianGradeCoordinates phase grade field‖) :=
        mul_le_mul_of_nonneg_left firstStage
          (add_nonneg zero_le_one (toroidalGradeConstant_nonneg phase parameter grade))
    _ = triangularGradeConstant phase parameter grade *
          ‖cartesianGradeCoordinates phase grade field‖ := by
        rw [triangularGradeConstant]
        ring

/-- The actual N12–N15 triangular two-gauge projection theorem. -/
theorem actualGauges : GaugesGoal := by
  intro phase parameter inside
  obtain ⟨killsPoloidal, killsToroidal, fixesKernel, idempotent, rangeLaw⟩ :=
    triangularGaugeProjection_algebra phase parameter inside
  refine ⟨poloidalCorrection phase parameter inside,
    toroidalCorrection phase parameter inside,
    poloidalCorrection_apply phase parameter inside,
    toroidalCorrection_apply phase parameter inside,
    derivativeDotCore_value phase parameter inside, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨triangularGradeConstant phase parameter, ?_, ?_⟩
    · intro grade
      exact triangularGradeConstant_nonneg phase parameter grade
    · intro grade field
      rw [ofCoreLinear_norm_coordinates, ofCoreLinear_norm_coordinates]
      exact triangularGaugeProjection_coordinates_bound phase parameter inside field
  · exact poloidalCorrection_idempotent phase parameter inside
  · exact toroidalCorrection_idempotent phase parameter inside
  · exact poloidal_toroidal_cross phase parameter inside
  · exact idempotent
  · exact rangeLaw
  · exact fun field zeroJets =>
      triangularGaugeProjection_zero_first_jets phase parameter inside field zeroJets
  · exact fun field cell radius bounded angle =>
      triangularGaugeProjection_radial_row phase parameter inside field cell radius
        bounded angle

end Grad.Constraints.Gauges

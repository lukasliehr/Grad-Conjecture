import AXB2LiftComponentBounds
import AXL26LiftConsumer

noncomputable section

set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.NonlinearProduct Grad.PhysicalCoordinates
open Grad.Q24Realization

variable {parameters : PhaseParameters}

/-- The core-to-grade norm is literally the three-component `X^q` sum.
This records the raw norm used by AL27 rather than replacing it by an
equivalent auxiliary norm. -/
theorem axb_stateToGrade_literal_norm (grade : ℕ)
    (state : Grad.SmoothingFamily.StateCore parameters) :
    ‖Grad.SmoothingFamily.stateToGrade parameters grade state‖ =
      tangentNorm (grade + 1) (smoothingToTangent parameters state.1) +
        originalGradeNorm grade state.2.1 + originalGradeNorm grade state.2.2 := by
  rw [Grad.AxisCore.stateToGrade_embedded_norm, aGradeEta_norm, aGradeEta_norm,
    ← tangentToGrade_smoothing, tangentToGrade_norm]
  rfl

/-- Exact `X^q` norm decomposition of the complex-linear axis lift.  The
physical-coordinate permutation is removed by its proved isometry. -/
theorem axisDataCapLiftLinear_literal_norm (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (base : TangentCoefficient parameters) (grade : ℕ) (data : AxisData parameters) :
    ‖Grad.SmoothingFamily.stateToGrade parameters grade
        (axisDataCapLiftLinear parameters radius positive seed inside base data)‖ =
      axisGradeNorm parameters (grade + 1) data.2 +
        originalGradeNorm grade
          (capChartRemainder parameters radius positive seed inside
            (rootDerivativeFamily 1 base (fun _ => axisToTangent parameters data.2))
            (axisToTangent parameters data.2)) +
        originalGradeNorm grade
          (capScalarAffine parameters radius positive (axisToTangent parameters data.1)) := by
  rw [axb_stateToGrade_literal_norm]
  change tangentNorm (grade + 1) (axisToTangent parameters data.2) +
      originalGradeNorm grade (toPhysicalCore parameters
        (capChartRemainder parameters radius positive seed inside
          (rootDerivativeFamily 1 base (fun _ => axisToTangent parameters data.2))
          (axisToTangent parameters data.2))) +
      originalGradeNorm grade
        (capScalarAffine parameters radius positive (axisToTangent parameters data.1)) = _
  rw [axisToTangent_norm, toPhysicalCore_norm]

/-- AL27: the actual axis lift has the original one-high estimate, uniformly
on a compact admissible seed patch.  The analytic width is unchanged and the
only shift is the literal `T^(q+1)` already present in `axisDataNorm` and the
base-axis factor. -/
theorem axisDataCapLiftLinear_bound_on_patch (radius : ℝ) (positive : 0 < radius)
    (grade : ℕ) (_gradeMin : 3 ≤ grade)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ seed ∈ seedPatch, ∀ (inside : seed ∈ Seed.parameterDomain)
        (base : TangentCoefficient parameters), RootAxisCondition base →
        ∀ data : AxisData parameters,
          ‖Grad.SmoothingFamily.stateToGrade parameters grade
              (axisDataCapLiftLinear parameters radius positive seed inside base data)‖ ≤
            constant * (axisDataNorm parameters grade data +
              (1 + tangentNorm (grade + 1) base) * axisDataNorm parameters 0 data) := by
  obtain ⟨rootConstant, rootNonnegative, rootBound⟩ :=
    rootDerivativeFamily_one_tangent_bound (parameters := parameters) grade
  obtain ⟨remainderConstant, remainderNonnegative, remainderBound⟩ :=
    capChartRemainder_bound_on_patch (parameters := parameters) radius positive grade
      seedPatch compact insidePatch
  obtain ⟨scalarConstant, scalarNonnegative, scalarBound⟩ :=
    capScalarAffine_bound (parameters := parameters) radius positive grade
  let bridge := Real.sqrt 2 ^ grade * axisConstant
  have bridgeNonnegative : 0 ≤ bridge := by
    dsimp [bridge]
    exact mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) grade) axisConstant_pos.le
  let constant := 1 + remainderConstant * (rootConstant + bridge) + scalarConstant * bridge
  have constantNonnegative : 0 ≤ constant := by
    dsimp [constant]
    positivity
  refine ⟨constant, constantNonnegative, ?_⟩
  intro seed member inside base axis data
  rw [axisDataCapLiftLinear_literal_norm radius positive seed inside base grade data]
  let sigma := axisToTangent parameters data.1
  let tangent := axisToTangent parameters data.2
  let coefficient := rootDerivativeFamily 1 base (fun _ : Fin 1 => tangent)
  have coefficientBound := rootBound base tangent axis
  have remainderEstimate := remainderBound seed member inside coefficient tangent
  have tangentEnvelope := tangentPlanarEnvelope_le grade tangent
  have sigmaEnvelope := tangentPlanarEnvelope_le grade sigma
  have tangentEnvelope' : tangentPlanarEnvelope grade tangent ≤
      bridge * tangentNorm (grade + 1) tangent := by
    simpa only [bridge, mul_assoc] using tangentEnvelope
  have sigmaEnvelope' : tangentPlanarEnvelope grade sigma ≤
      bridge * tangentNorm (grade + 1) sigma := by
    simpa only [bridge, mul_assoc] using sigmaEnvelope
  have remainderEstimate' : originalGradeNorm grade
      (capChartRemainder parameters radius positive seed inside coefficient tangent) ≤
      remainderConstant *
        (rootConstant * (tangentNorm (grade + 1) tangent +
          (1 + tangentNorm (grade + 1) base) * tangentNorm 1 tangent) +
          bridge * tangentNorm (grade + 1) tangent) := by
    have envelopeNonnegative := coefficientEnvelope_nonneg grade coefficient
    have planarNonnegative := tangentPlanarEnvelope_nonneg grade tangent
    exact remainderEstimate.trans
      (mul_le_mul_of_nonneg_left (add_le_add coefficientBound tangentEnvelope')
        remainderNonnegative)
  have scalarEstimate := scalarBound sigma
  have scalarEstimate' : originalGradeNorm grade
      (capScalarAffine parameters radius positive sigma) ≤
      scalarConstant * (bridge * tangentNorm (grade + 1) sigma) :=
    scalarEstimate.trans (mul_le_mul_of_nonneg_left sigmaEnvelope' scalarNonnegative)
  have highIdentity : axisDataNorm parameters grade data =
      tangentNorm (grade + 1) sigma + tangentNorm (grade + 1) tangent := by
    dsimp [sigma, tangent]
    rw [axisDataNorm, axisToTangent_norm, axisToTangent_norm]
  have lowIdentity : axisDataNorm parameters 0 data =
      tangentNorm 1 sigma + tangentNorm 1 tangent := by
    dsimp [sigma, tangent]
    rw [axisDataNorm, axisToTangent_norm, axisToTangent_norm]
  rw [highIdentity, lowIdentity]
  rw [← axisToTangent_norm (grade + 1) data.2]
  change tangentNorm (grade + 1) tangent +
      originalGradeNorm grade
        (capChartRemainder parameters radius positive seed inside coefficient tangent) +
      originalGradeNorm grade (capScalarAffine parameters radius positive sigma) ≤ _
  have sigmaHighNonnegative := tangentNorm_nonneg (grade + 1) sigma
  have tangentHighNonnegative := tangentNorm_nonneg (grade + 1) tangent
  have sigmaLowNonnegative := tangentNorm_nonneg 1 sigma
  have tangentLowNonnegative := tangentNorm_nonneg 1 tangent
  have baseNonnegative := tangentNorm_nonneg (grade + 1) base
  let bracket := tangentNorm (grade + 1) sigma + tangentNorm (grade + 1) tangent +
    (1 + tangentNorm (grade + 1) base) * (tangentNorm 1 sigma + tangentNorm 1 tangent)
  have lowProductNonnegative : 0 ≤
      (1 + tangentNorm (grade + 1) base) * (tangentNorm 1 sigma + tangentNorm 1 tangent) :=
    mul_nonneg (by linarith) (add_nonneg sigmaLowNonnegative tangentLowNonnegative)
  have bracketNonnegative : 0 ≤ bracket := by
    dsimp [bracket]
    positivity
  have tangentHighLe : tangentNorm (grade + 1) tangent ≤ bracket := by
    dsimp [bracket]
    linarith
  have rootBracketLe :
      tangentNorm (grade + 1) tangent +
          (1 + tangentNorm (grade + 1) base) * tangentNorm 1 tangent ≤ bracket := by
    dsimp [bracket]
    have omittedLow : 0 ≤
        (1 + tangentNorm (grade + 1) base) * tangentNorm 1 sigma :=
      mul_nonneg (by linarith) sigmaLowNonnegative
    nlinarith
  have rootAndLinearLe :
      rootConstant * (tangentNorm (grade + 1) tangent +
          (1 + tangentNorm (grade + 1) base) * tangentNorm 1 tangent) +
        bridge * tangentNorm (grade + 1) tangent ≤
      (rootConstant + bridge) * bracket := by
    have first := mul_le_mul_of_nonneg_left rootBracketLe rootNonnegative
    have second := mul_le_mul_of_nonneg_left tangentHighLe bridgeNonnegative
    nlinarith [mul_nonneg rootNonnegative bracketNonnegative,
      mul_nonneg bridgeNonnegative bracketNonnegative]
  have remainderFinal : originalGradeNorm grade
      (capChartRemainder parameters radius positive seed inside coefficient tangent) ≤
      remainderConstant * ((rootConstant + bridge) * bracket) :=
    remainderEstimate'.trans (mul_le_mul_of_nonneg_left rootAndLinearLe remainderNonnegative)
  have sigmaHighLe : tangentNorm (grade + 1) sigma ≤ bracket := by
    dsimp [bracket]
    linarith
  have scalarFinal : originalGradeNorm grade
      (capScalarAffine parameters radius positive sigma) ≤
      scalarConstant * (bridge * bracket) := by
    apply scalarEstimate'.trans
    apply mul_le_mul_of_nonneg_left _ scalarNonnegative
    exact mul_le_mul_of_nonneg_left sigmaHighLe bridgeNonnegative
  change tangentNorm (grade + 1) tangent +
      originalGradeNorm grade
        (capChartRemainder parameters radius positive seed inside coefficient tangent) +
      originalGradeNorm grade (capScalarAffine parameters radius positive sigma) ≤
    constant * bracket
  exact (add_le_add (add_le_add tangentHighLe remainderFinal) scalarFinal).trans_eq (by
    dsimp [constant]
    ring)

/-- The same estimate stated on the exact actual moving-seed lift from AXL26.
The reality and cutoff hypotheses certify its constrained realization; the
quantitative inequality is for the identical underlying linear lift. -/
theorem actualPhysicalAxisLift_bound_on_patch (radius : ℝ) (positive : 0 < radius)
    (bounded : radius ≤ 1) (grade : ℕ) (gradeMin : 3 ≤ grade)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ seed ∈ seedPatch, ∀ (inside : seed ∈ Seed.parameterDomain)
        (base : ChartState parameters) (_realBase : RealTangent base.1)
        (_axis : ChartAxisCondition base) (data : AxisData parameters) (_real : RealAxisData data),
        PhysicalAxisLiftRealization parameters radius positive seed inside base data ∧
          ‖Grad.SmoothingFamily.stateToGrade parameters grade
              (axisDataCapLiftLinear parameters radius positive seed inside base.1 data)‖ ≤
            constant * (axisDataNorm parameters grade data +
              (1 + tangentNorm (grade + 1) base.1) * axisDataNorm parameters 0 data) := by
  obtain ⟨constant, nonnegative, bound⟩ :=
    axisDataCapLiftLinear_bound_on_patch (parameters := parameters) radius positive grade gradeMin
      seedPatch compact insidePatch
  refine ⟨constant, nonnegative, ?_⟩
  intro seed member inside base realBase axis data real
  exact ⟨actualPhysicalAxisLift parameters radius positive bounded seed inside base realBase axis data real,
    bound seed member inside base.1 axis data⟩

end Grad.ChartAxisLift

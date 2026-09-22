import Q24FieldLinear

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1200000

namespace Grad.Q24Realization

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct
open Grad.Constraints.Multipliers

theorem coefficientFieldMap_bound (parameters : PhaseParameters) (dimension grade : ℕ)
    [Nontrivial (ComplexEuclidean dimension)] (field : ACore parameters dimension)
    (coefficient : Grad.Q8FixedGrade.Carrier parameters grade) :
    ‖coefficientFieldMap parameters dimension grade field coefficient‖ ≤
      (multiplierConstant grade parameters.gamma * originalGradeNorm grade field) * ‖coefficient‖ := by
  refine isClosed_property (Grad.Q8FixedGrade.embed_denseRange parameters grade)
    (isClosed_le (coefficientFieldMap parameters dimension grade field).continuous.norm
      (continuous_const.mul continuous_norm)) ?_ coefficient
  intro core
  simp only [Pi.mul_apply]
  rw [coefficientFieldMap_core, fieldEmbed_norm, Grad.Q8FixedGrade.embed_norm]
  exact (tameScalarMultiplier_bound dimension core field grade).trans_eq (by ring)

theorem coefficientFieldMap_add_field (parameters : PhaseParameters) (dimension grade : ℕ)
    [Nontrivial (ComplexEuclidean dimension)] (first second : ACore parameters dimension) :
    coefficientFieldMap parameters dimension grade (first + second) =
      coefficientFieldMap parameters dimension grade first + coefficientFieldMap parameters dimension grade second := by
  apply ContinuousLinearMap.ext
  intro coefficient
  refine isClosed_property (Grad.Q8FixedGrade.embed_denseRange parameters grade)
    (isClosed_eq (coefficientFieldMap parameters dimension grade (first + second)).continuous
      ((coefficientFieldMap parameters dimension grade first).continuous.add
        (coefficientFieldMap parameters dimension grade second).continuous)) ?_ coefficient
  intro core
  simp only [Pi.add_apply, coefficientFieldMap_core, map_add]

theorem coefficientFieldMap_smul_field (parameters : PhaseParameters) (dimension grade : ℕ)
    [Nontrivial (ComplexEuclidean dimension)] (scalar : ℂ) (field : ACore parameters dimension) :
    coefficientFieldMap parameters dimension grade (scalar • field) =
      scalar • coefficientFieldMap parameters dimension grade field := by
  apply ContinuousLinearMap.ext
  intro coefficient
  refine isClosed_property (Grad.Q8FixedGrade.embed_denseRange parameters grade)
    (isClosed_eq (coefficientFieldMap parameters dimension grade (scalar • field)).continuous
      ((coefficientFieldMap parameters dimension grade field).continuous.const_smul scalar)) ?_ coefficient
  intro core
  simp only [Pi.smul_apply, coefficientFieldMap_core, map_smul]

/-- The coefficient action is bounded linear in the original field as
well, with exactly its original grade norm. -/
def fieldToCoefficientOperatorsLinear (parameters : PhaseParameters) (dimension grade : ℕ)
    [Nontrivial (ComplexEuclidean dimension)] :
    GradeCore parameters dimension grade →ₗ[ℂ]
      (Grad.Q8FixedGrade.Carrier parameters grade →L[ℂ] AGrade parameters dimension grade) where
  toFun field := coefficientFieldMap parameters dimension grade field.toCore
  map_add' first second := coefficientFieldMap_add_field parameters dimension grade first.toCore second.toCore
  map_smul' scalar field := coefficientFieldMap_smul_field parameters dimension grade scalar field.toCore

theorem fieldToCoefficientOperators_bound (parameters : PhaseParameters) (dimension grade : ℕ)
    [Nontrivial (ComplexEuclidean dimension)] (field : GradeCore parameters dimension grade) :
    ‖fieldToCoefficientOperatorsLinear parameters dimension grade field‖ ≤
      multiplierConstant grade parameters.gamma * ‖field‖ := by
  change ‖coefficientFieldMap parameters dimension grade field.toCore‖ ≤ _
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (multiplierConstant_nonnegative grade parameters.gamma parameters.gamma_pos.le)
      (norm_nonneg field))
  intro coefficient
  exact (coefficientFieldMap_bound parameters dimension grade field.toCore coefficient).trans_eq (by
    simp only [originalGradeNorm, GradeCore.ofCore_toCore])

def fieldToCoefficientOperatorsCore (parameters : PhaseParameters) (dimension grade : ℕ)
    [Nontrivial (ComplexEuclidean dimension)] :
    GradeCore parameters dimension grade →L[ℂ]
      (Grad.Q8FixedGrade.Carrier parameters grade →L[ℂ] AGrade parameters dimension grade) where
  toLinearMap := fieldToCoefficientOperatorsLinear parameters dimension grade
  cont := by
    have bounded : LipschitzWith
        ⟨multiplierConstant grade parameters.gamma,
          multiplierConstant_nonnegative grade parameters.gamma parameters.gamma_pos.le⟩
        (fieldToCoefficientOperatorsLinear parameters dimension grade) := by
      apply LipschitzWith.of_dist_le_mul
      intro first second
      rw [dist_eq_norm, dist_eq_norm, ← map_sub]
      exact fieldToCoefficientOperators_bound parameters dimension grade (first - second)
    exact bounded.continuous

/-- The actual scalar-coefficient action on two completed original grades.
It is not a new norm or an assumed product extension. -/
def completedCoefficientField (parameters : PhaseParameters) (dimension grade : ℕ)
    [Nontrivial (ComplexEuclidean dimension)] :
    AGrade parameters dimension grade →L[ℂ]
      (Grad.Q8FixedGrade.Carrier parameters grade →L[ℂ] AGrade parameters dimension grade) :=
  (fieldToCoefficientOperatorsCore parameters dimension grade).fromCompletion

theorem completedCoefficientField_core (parameters : PhaseParameters) (dimension grade : ℕ)
    [Nontrivial (ComplexEuclidean dimension)] (field : ACore parameters dimension) :
    completedCoefficientField parameters dimension grade (fieldEmbed parameters dimension grade field) =
      coefficientFieldMap parameters dimension grade field :=
  ContinuousLinearMap.fromCompletion_apply_coe
    (fieldToCoefficientOperatorsCore parameters dimension grade) (GradeCore.ofCoreLinear field)

end Grad.Q24Realization

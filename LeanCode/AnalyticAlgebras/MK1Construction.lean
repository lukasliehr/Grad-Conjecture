import MK1Interface

noncomputable section

open MeasureTheory

namespace Grad.MatrixMultiplier

variable {Space ValueIn ValueOut : Type*} [MeasurableSpace Space]
  [NormedAddCommGroup ValueIn] [NormedSpace ℂ ValueIn]
  [NormedAddCommGroup ValueOut] [NormedSpace ℂ ValueOut]

theorem action_memLp (measure : Measure Space)
    (coefficients : Space → ValueIn →L[ℂ] ValueOut) (bound : ℝ)
    (coefficientMeasurable : AEStronglyMeasurable coefficients measure)
    (coefficientBound : ∀ᵐ point ∂measure, ‖coefficients point‖ ≤ bound)
    (representative : Space → ValueIn) (membership : MemLp representative 2 measure) :
    MemLp (fun point => coefficients point (representative point)) 2 measure := by
  refine membership.of_le_mul (c := bound)
    ((ContinuousLinearMap.id ℂ (ValueIn →L[ℂ] ValueOut)).aestronglyMeasurable_comp₂
      coefficientMeasurable membership.aestronglyMeasurable) ?_
  filter_upwards [coefficientBound] with point estimate
  exact ((coefficients point).le_opNorm (representative point)).trans
    (mul_le_mul_of_nonneg_right estimate (norm_nonneg _))

section Construction

variable (measure : Measure Space)
  (coefficients : Space → ValueIn →L[ℂ] ValueOut) (bound : ℝ)
  (coefficientMeasurable : AEStronglyMeasurable coefficients measure)
  (coefficientBound : ∀ᵐ point ∂measure, ‖coefficients point‖ ≤ bound)

def actionLp (field : Lp ValueIn 2 measure) : Lp ValueOut 2 measure :=
  (action_memLp measure coefficients bound coefficientMeasurable coefficientBound field
    (Lp.memLp field)).toLp (fun point => coefficients point (field point))

theorem actionLp_apply_ae (field : Lp ValueIn 2 measure) :
    ∀ᵐ point ∂measure,
      actionLp measure coefficients bound coefficientMeasurable coefficientBound field point =
        coefficients point (field point) :=
  (action_memLp measure coefficients bound coefficientMeasurable coefficientBound field
    (Lp.memLp field)).coeFn_toLp

theorem norm_actionLp_le (field : Lp ValueIn 2 measure) :
    ‖actionLp measure coefficients bound coefficientMeasurable coefficientBound field‖ ≤
      bound * ‖field‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [actionLp_apply_ae measure coefficients bound coefficientMeasurable
    coefficientBound field, coefficientBound] with point literal estimate
  rw [literal]
  exact ((coefficients point).le_opNorm (field point)).trans
    (mul_le_mul_of_nonneg_right estimate (norm_nonneg _))

theorem actionLp_add (first second : Lp ValueIn 2 measure) :
    actionLp measure coefficients bound coefficientMeasurable coefficientBound (first + second) =
      actionLp measure coefficients bound coefficientMeasurable coefficientBound first +
        actionLp measure coefficients bound coefficientMeasurable coefficientBound second := by
  apply Lp.ext
  filter_upwards [actionLp_apply_ae measure coefficients bound coefficientMeasurable
      coefficientBound (first + second),
    actionLp_apply_ae measure coefficients bound coefficientMeasurable coefficientBound first,
    actionLp_apply_ae measure coefficients bound coefficientMeasurable coefficientBound second,
    Lp.coeFn_add first second,
    Lp.coeFn_add (actionLp measure coefficients bound coefficientMeasurable coefficientBound first)
      (actionLp measure coefficients bound coefficientMeasurable coefficientBound second)]
    with point literal firstLiteral secondLiteral inputAddition outputAddition
  simp only [Pi.add_apply] at inputAddition outputAddition
  rw [literal, inputAddition, outputAddition, firstLiteral, secondLiteral, map_add]

theorem actionLp_smul (scalar : ℂ) (field : Lp ValueIn 2 measure) :
    actionLp measure coefficients bound coefficientMeasurable coefficientBound (scalar • field) =
      scalar • actionLp measure coefficients bound coefficientMeasurable coefficientBound field := by
  apply Lp.ext
  filter_upwards [actionLp_apply_ae measure coefficients bound coefficientMeasurable
      coefficientBound (scalar • field),
    actionLp_apply_ae measure coefficients bound coefficientMeasurable coefficientBound field,
    Lp.coeFn_smul scalar field,
    Lp.coeFn_smul scalar (actionLp measure coefficients bound coefficientMeasurable coefficientBound field)]
    with point literal fieldLiteral inputScalar outputScalar
  simp only [Pi.smul_apply] at inputScalar outputScalar
  rw [literal, inputScalar, outputScalar, fieldLiteral, map_smul]

def multiplierLinear : Lp ValueIn 2 measure →ₗ[ℂ] Lp ValueOut 2 measure where
  toFun := actionLp measure coefficients bound coefficientMeasurable coefficientBound
  map_add' := actionLp_add measure coefficients bound coefficientMeasurable coefficientBound
  map_smul' := actionLp_smul measure coefficients bound coefficientMeasurable coefficientBound

def matrixMultiplier : Lp ValueIn 2 measure →L[ℂ] Lp ValueOut 2 measure :=
  (multiplierLinear measure coefficients bound coefficientMeasurable coefficientBound).mkContinuous
    bound (norm_actionLp_le measure coefficients bound coefficientMeasurable coefficientBound)

theorem matrixMultiplier_apply (field : Lp ValueIn 2 measure) :
    matrixMultiplier measure coefficients bound coefficientMeasurable coefficientBound field =
      actionLp measure coefficients bound coefficientMeasurable coefficientBound field := rfl

theorem matrixMultiplier_apply_ae (field : Lp ValueIn 2 measure) :
    ∀ᵐ point ∂measure,
      matrixMultiplier measure coefficients bound coefficientMeasurable coefficientBound field point =
        coefficients point (field point) :=
  actionLp_apply_ae measure coefficients bound coefficientMeasurable coefficientBound field

theorem norm_matrixMultiplier_apply_le (field : Lp ValueIn 2 measure) :
    ‖matrixMultiplier measure coefficients bound coefficientMeasurable coefficientBound field‖ ≤
      bound * ‖field‖ :=
  norm_actionLp_le measure coefficients bound coefficientMeasurable coefficientBound field

theorem norm_matrixMultiplier_le (nonnegative : 0 ≤ bound) :
    ‖matrixMultiplier measure coefficients bound coefficientMeasurable coefficientBound‖ ≤ bound :=
  (multiplierLinear measure coefficients bound coefficientMeasurable coefficientBound).mkContinuous_norm_le
    nonnegative (norm_actionLp_le measure coefficients bound coefficientMeasurable coefficientBound)

theorem matrixMultiplier_toLp_ae (representative : Space → ValueIn)
    (membership : MemLp representative 2 measure) :
    ∀ᵐ point ∂measure,
      matrixMultiplier measure coefficients bound coefficientMeasurable coefficientBound
        (membership.toLp representative) point = coefficients point (representative point) := by
  filter_upwards [matrixMultiplier_apply_ae measure coefficients bound coefficientMeasurable
    coefficientBound (membership.toLp representative), membership.coeFn_toLp]
    with point literal representativeEquality
  rw [literal, representativeEquality]

theorem matrixMultiplier_toLp (representative : Space → ValueIn)
    (membership : MemLp representative 2 measure) :
    matrixMultiplier measure coefficients bound coefficientMeasurable coefficientBound
      (membership.toLp representative) =
        (action_memLp measure coefficients bound coefficientMeasurable coefficientBound
          representative membership).toLp (fun point => coefficients point (representative point)) := by
  apply Lp.ext
  exact Filter.EventuallyEq.trans
    (matrixMultiplier_toLp_ae measure coefficients bound coefficientMeasurable
      coefficientBound representative membership)
    (action_memLp measure coefficients bound coefficientMeasurable coefficientBound
      representative membership).coeFn_toLp.symm

theorem matrixMultiplier_representative_independent (first second : Space → ValueIn)
    (firstMembership : MemLp first 2 measure) (secondMembership : MemLp second 2 measure)
    (equality : first =ᵐ[measure] second) :
    matrixMultiplier measure coefficients bound coefficientMeasurable coefficientBound
      (firstMembership.toLp first) =
        matrixMultiplier measure coefficients bound coefficientMeasurable coefficientBound
          (secondMembership.toLp second) :=
  congrArg (matrixMultiplier measure coefficients bound coefficientMeasurable coefficientBound)
    (MemLp.toLp_congr firstMembership secondMembership equality)

theorem matrixMultiplier_add (first second : Lp ValueIn 2 measure) :
    matrixMultiplier measure coefficients bound coefficientMeasurable coefficientBound (first + second) =
      matrixMultiplier measure coefficients bound coefficientMeasurable coefficientBound first +
        matrixMultiplier measure coefficients bound coefficientMeasurable coefficientBound second :=
  map_add _ _ _

theorem matrixMultiplier_smul (scalar : ℂ) (field : Lp ValueIn 2 measure) :
    matrixMultiplier measure coefficients bound coefficientMeasurable coefficientBound (scalar • field) =
      scalar • matrixMultiplier measure coefficients bound coefficientMeasurable coefficientBound field :=
  map_smul _ _ _

end Construction
end Grad.MatrixMultiplier

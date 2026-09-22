import AKCV15OriginalBranchInverseTaylor
import SM19SmoothConvergence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3500

namespace Grad.NashMoser.OriginalIteration
open Grad.CartesianState Grad.Constraints Grad.SmoothingFamily Grad.Cor18
open Grad.RealFixedRanges Grad.CompletedReality

variable (parameters : PhaseParameters) (reference : Seed.Parameters)
    (inside : reference ∈ Seed.parameterDomain)

theorem stateReality_iff (state : StateCore parameters) :
    StateReality state ↔ xCoreConjugation parameters state = state := by
  constructor
  · rintro ⟨axis, vector, scalar⟩
    apply Prod.ext
    · apply Subtype.ext
      funext cell
      apply PiLp.ext
      intro coordinate
      exact axis cell coordinate
    · exact Prod.ext vector scalar
  · intro real
    refine ⟨?_, congrArg (fun value : StateCore parameters => value.2.1) real,
      congrArg (fun value : StateCore parameters => value.2.2) real⟩
    intro cell coordinate
    exact congrArg (fun value : StateCore parameters => value.1.1 cell coordinate) real

/-- The actual full COR18 projection, including the free affine axis. -/
def originalProjectionConstant (grade : ℕ) : ℝ :=
  if large : 3 ≤ grade then
    (fullProjection_norm_le parameters reference inside grade large).choose else 0

theorem originalProjectionConstant_nonnegative (grade : ℕ) :
    0 ≤ originalProjectionConstant parameters reference inside grade := by
  unfold originalProjectionConstant
  split
  · rename_i large
    exact (fullProjection_norm_le parameters reference inside grade large).choose_spec.1
  · exact le_refl 0

theorem originalProjection_norm_le (grade : ℕ) (large : 3 ≤ grade)
    (state : StateCore parameters) :
    ‖stateToGrade parameters grade (fullProjection parameters reference inside state)‖ ≤
      originalProjectionConstant parameters reference inside grade *
        ‖stateToGrade parameters grade state‖ := by
  unfold originalProjectionConstant
  rw [dif_pos large]
  exact (fullProjection_norm_le parameters reference inside grade large).choose_spec.2 state

def originalSmoothingProjection : SameGradeStateProjection parameters where
  map := (fullProjection parameters reference inside).restrictScalars ℝ
  idempotent := fullProjection_idempotent parameters reference inside
  bound := originalProjectionConstant parameters reference inside
  boundNonnegative := originalProjectionConstant_nonnegative parameters reference inside
  bounded := originalProjection_norm_le parameters reference inside
  real state real := (stateReality_iff parameters _).2 (by
    change xCoreConjugation parameters (fullProjection parameters reference inside state) = _
    rw [fullProjection_conjugate, (stateReality_iff parameters state).1 real]
    rfl)

/-- SAME-width full real constrained smoothing, with no flattening of the
axis and no postulated projection. -/
def originalStateSmoothing (scale : ℝ) :
    stateSmoothRange parameters reference inside →ₗ[ℝ]
      stateSmoothRange parameters reference inside where
  toFun state := ⟨fullProjection parameters reference inside
    (stateSmoothing parameters scale state.val), by
    rw [mem_stateSmoothRange]
    refine ⟨fullProjection_idempotent parameters reference inside _, ?_⟩
    rw [fullProjection_conjugate]
    rw [(stateReality_iff parameters _).1
      (stateSmoothing_reality parameters scale state.val
        ((stateReality_iff parameters _).2
          ((mem_stateSmoothRange parameters reference inside state.val).1 state.property).2))]⟩
  map_add' first second := by
    apply Subtype.ext
    exact ((fullProjection parameters reference inside).comp
      (stateSmoothing parameters scale)).map_add first.val second.val
  map_smul' scalar state := by
    apply Subtype.ext
    exact (((fullProjection parameters reference inside).comp
      (stateSmoothing parameters scale)).restrictScalars ℝ).map_smul scalar state.val

theorem originalStateSmoothing_apply (scale : ℝ)
    (state : stateSmoothRange parameters reference inside) :
    (originalStateSmoothing parameters reference inside scale state).val =
      fullProjection parameters reference inside (stateSmoothing parameters scale state.val) := rfl

def originalSmoothingGain (lower upper : ℕ) : ℝ :=
  originalProjectionConstant parameters reference inside upper * stateSmoothingConstant lower upper

def originalSmoothingTail (lower upper : ℕ) : ℝ :=
  originalProjectionConstant parameters reference inside lower * stateRemainderConstant lower upper

theorem originalStateSmoothing_norm_le (scale : ℝ) (positive : 0 < scale)
    (lower upper : ℕ) (ordered : lower ≤ upper) (large : 3 ≤ upper)
    (state : stateSmoothRange parameters reference inside) :
    ‖stateToGrade parameters upper
      (originalStateSmoothing parameters reference inside scale state).val‖ ≤
      originalSmoothingGain parameters reference inside lower upper * scale ^ (upper-lower) *
        ‖stateToGrade parameters lower state.val‖ := by
  let projected : (originalSmoothingProjection parameters reference inside).map.range :=
    ⟨state.val, ⟨state.val,
      ((mem_stateSmoothRange parameters reference inside state.val).1 state.property).1⟩⟩
  have bound := projectedStateSmoothing_norm_le
    (originalSmoothingProjection parameters reference inside) scale positive lower upper ordered large projected
  rw [projectedStateSmoothing_apply] at bound
  exact bound

theorem originalStateRemainder_norm_le (scale : ℝ) (positive : 0 < scale)
    (lower upper : ℕ) (ordered : lower ≤ upper) (large : 3 ≤ lower)
    (state : stateSmoothRange parameters reference inside) :
    ‖stateToGrade parameters lower
      (state - originalStateSmoothing parameters reference inside scale state).val‖ ≤
      originalSmoothingTail parameters reference inside lower upper *
        scale ^ ((lower:ℝ)-(upper:ℝ)) * ‖stateToGrade parameters upper state.val‖ := by
  let projected : (originalSmoothingProjection parameters reference inside).map.range :=
    ⟨state.val, ⟨state.val,
      ((mem_stateSmoothRange parameters reference inside state.val).1 state.property).1⟩⟩
  have bound := projectedStateRemainder_norm_le
    (originalSmoothingProjection parameters reference inside) scale positive lower upper ordered large projected
  rw [projectedStateSmoothing_apply] at bound
  exact bound

end Grad.NashMoser.OriginalIteration

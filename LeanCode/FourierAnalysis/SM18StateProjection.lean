import SM17StateCalculus

noncomputable section

open scoped Topology

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace Grad.SmoothingFamily

open Grad.CartesianState

/-- A specified actual real-linear projection on the literal three-block
smooth product. Existence of the project's full N8 projection is not assumed. -/
structure SameGradeStateProjection (parameters : PhaseParameters) where
  map : StateCore parameters →ₗ[ℝ] StateCore parameters
  idempotent : ∀ state, map (map state) = map state
  bound : ℕ → ℝ
  boundNonnegative : ∀ grade, 0 ≤ bound grade
  bounded : ∀ grade, 3 ≤ grade → ∀ state,
    ‖stateToGrade parameters grade (map state)‖ ≤ bound grade * ‖stateToGrade parameters grade state‖
  real : ∀ state, StateReality state → StateReality (map state)

namespace SameGradeStateProjection

variable {parameters : PhaseParameters}

def identity (parameters : PhaseParameters) : SameGradeStateProjection parameters where
  map := LinearMap.id
  idempotent _ := rfl
  bound _ := 1
  boundNonnegative _ := zero_le_one
  bounded _ _ _ := by simp
  real _ real := real

theorem fixed (projection : SameGradeStateProjection parameters) (state : projection.map.range) :
    projection.map state = state := by
  obtain ⟨source, equality⟩ := state.property
  rw [← equality, projection.idempotent]

def gradeMap (projection : SameGradeStateProjection parameters) (grade : ℕ) (admissible : 3 ≤ grade) :
    StateGradeCore parameters grade →L[ℝ] StateGradeCore parameters grade :=
  (((stateGradeEquiv parameters grade).restrictScalars ℝ).toLinearMap.comp
    (projection.map.comp ((stateGradeEquiv parameters grade).symm.restrictScalars ℝ).toLinearMap)).mkContinuous
      (projection.bound grade) (by
        intro state
        change ‖stateGradeEquiv parameters grade (projection.map ((stateGradeEquiv parameters grade).symm state))‖ ≤ _
        have estimate := projection.bounded grade admissible ((stateGradeEquiv parameters grade).symm state)
        simpa only [← stateGradeEquiv_norm, LinearEquiv.apply_symm_apply] using estimate)

end SameGradeStateProjection

def projectedStateDerivative {parameters : PhaseParameters} (projection : SameGradeStateProjection parameters)
    (order : ℕ) (scale : ℝ) : projection.map.range →ₗ[ℝ] projection.map.range where
  toFun state := ⟨projection.map (stateScaleDerivative parameters order scale state),
    ⟨stateScaleDerivative parameters order scale state, rfl⟩⟩
  map_add' first second := by
    apply Subtype.ext
    exact (projection.map.comp ((stateScaleDerivative parameters order scale).restrictScalars ℝ)).map_add first second
  map_smul' scalar state := by
    apply Subtype.ext
    exact (projection.map.comp ((stateScaleDerivative parameters order scale).restrictScalars ℝ)).map_smul scalar state

def projectedStateSmoothing {parameters : PhaseParameters} (projection : SameGradeStateProjection parameters)
    (scale : ℝ) : projection.map.range →ₗ[ℝ] projection.map.range := projectedStateDerivative projection 0 scale

theorem projectedStateSmoothing_apply {parameters : PhaseParameters} (projection : SameGradeStateProjection parameters)
    (scale : ℝ) (state : projection.map.range) :
    (projectedStateSmoothing projection scale state).1 = projection.map (stateSmoothing parameters scale state) := by
  change projection.map (stateScaleDerivative parameters 0 scale state) = _
  rw [stateScaleDerivative_zero]

theorem projectedStateRemainder_apply {parameters : PhaseParameters} (projection : SameGradeStateProjection parameters)
    (scale : ℝ) (state : projection.map.range) :
    state.1 - (projectedStateSmoothing projection scale state).1 =
      projection.map (state.1 - stateSmoothing parameters scale state.1) := by
  rw [map_sub, projection.fixed, projectedStateSmoothing_apply]

theorem projectedStateSmoothing_norm_le {parameters : PhaseParameters} (projection : SameGradeStateProjection parameters)
    (scale : ℝ) (positive : 0 < scale) (lower upper : ℕ) (ordered : lower ≤ upper) (admissible : 3 ≤ upper)
    (state : projection.map.range) :
    ‖stateToGrade parameters upper (projectedStateSmoothing projection scale state).1‖ ≤
      (projection.bound upper * stateSmoothingConstant lower upper) * scale ^ (upper - lower) *
        ‖stateToGrade parameters lower state.1‖ := by
  rw [projectedStateSmoothing_apply]
  calc
    _ ≤ projection.bound upper * ‖stateToGrade parameters upper (stateSmoothing parameters scale state.1)‖ :=
      projection.bounded upper admissible _
    _ ≤ projection.bound upper * (stateSmoothingConstant lower upper * scale ^ (upper - lower) *
        ‖stateToGrade parameters lower state.1‖) :=
      mul_le_mul_of_nonneg_left (stateSmoothing_norm_le parameters scale positive lower upper ordered state.1)
        (projection.boundNonnegative upper)
    _ = _ := by ring

theorem projectedStateRemainder_norm_le {parameters : PhaseParameters} (projection : SameGradeStateProjection parameters)
    (scale : ℝ) (positive : 0 < scale) (lower upper : ℕ) (ordered : lower ≤ upper) (admissible : 3 ≤ lower)
    (state : projection.map.range) :
    ‖stateToGrade parameters lower (state.1 - (projectedStateSmoothing projection scale state).1)‖ ≤
      (projection.bound lower * stateRemainderConstant lower upper) * scale ^ ((lower : ℝ) - (upper : ℝ)) *
        ‖stateToGrade parameters upper state.1‖ := by
  rw [projectedStateRemainder_apply]
  calc
    _ ≤ projection.bound lower * ‖stateToGrade parameters lower (state.1 - stateSmoothing parameters scale state.1)‖ :=
      projection.bounded lower admissible _
    _ ≤ projection.bound lower * (stateRemainderConstant lower upper * scale ^ ((lower : ℝ) - (upper : ℝ)) *
        ‖stateToGrade parameters upper state.1‖) :=
      mul_le_mul_of_nonneg_left (stateRemainder_norm_le parameters scale positive lower upper ordered state.1)
        (projection.boundNonnegative lower)
    _ = _ := by ring

theorem projectedStateDerivative_norm_le {parameters : PhaseParameters} (projection : SameGradeStateProjection parameters)
    (scale : ℝ) (positive : 0 < scale) (lower upper order : ℕ) (positiveOrder : 0 < order) (admissible : 3 ≤ upper)
    (state : projection.map.range) :
    ‖stateToGrade parameters upper (projectedStateDerivative projection order scale state).1‖ ≤
      (projection.bound upper * stateDerivativeConstant lower upper order) *
        scale ^ ((upper : ℝ) - (lower : ℝ) - (order : ℝ)) * ‖stateToGrade parameters lower state.1‖ := by
  calc
    _ ≤ projection.bound upper * ‖stateToGrade parameters upper (stateScaleDerivative parameters order scale state.1)‖ :=
      projection.bounded upper admissible _
    _ ≤ projection.bound upper * (stateDerivativeConstant lower upper order *
        scale ^ ((upper : ℝ) - (lower : ℝ) - (order : ℝ)) * ‖stateToGrade parameters lower state.1‖) :=
      mul_le_mul_of_nonneg_left (stateScaleDerivative_norm_le parameters scale positive lower upper order positiveOrder state.1)
        (projection.boundNonnegative upper)
    _ = _ := by ring

theorem projectedStateDerivative_hasDerivAt_grade {parameters : PhaseParameters}
    (projection : SameGradeStateProjection parameters) (order grade : ℕ) (admissible : 3 ≤ grade)
    (scale : ℝ) (positive : 0 < scale) (state : projection.map.range) :
    HasDerivAt (fun parameter => stateGradeEquiv parameters grade (projectedStateDerivative projection order parameter state).1)
      (stateGradeEquiv parameters grade (projectedStateDerivative projection (order + 1) scale state).1) scale := by
  change HasDerivAt (fun parameter => stateGradeEquiv parameters grade
      (projection.map (stateScaleDerivative parameters order parameter state.1)))
    (stateGradeEquiv parameters grade (projection.map (stateScaleDerivative parameters (order + 1) scale state.1))) scale
  have derivative := (projection.gradeMap grade admissible).hasFDerivAt.comp_hasDerivAt scale
    (stateScaleDerivative_hasDerivAt_grade parameters order grade scale positive state.1)
  simpa only [SameGradeStateProjection.gradeMap, LinearMap.mkContinuous_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply, Function.comp_def,
    LinearEquiv.symm_apply_apply] using derivative

theorem iteratedDeriv_projectedStateSmoothing_grade {parameters : PhaseParameters}
    (projection : SameGradeStateProjection parameters) (order grade : ℕ) (admissible : 3 ≤ grade)
    (scale : ℝ) (positive : 0 < scale) (state : projection.map.range) :
    iteratedDeriv order (fun parameter => stateGradeEquiv parameters grade (projectedStateSmoothing projection parameter state).1) scale =
      stateGradeEquiv parameters grade (projectedStateDerivative projection order scale state).1 := by
  induction order generalizing scale with
  | zero => rfl
  | succ order inductionHypothesis =>
    rw [iteratedDeriv_succ]
    have locallyEqual : iteratedDeriv order (fun parameter => stateGradeEquiv parameters grade
        (projectedStateSmoothing projection parameter state).1) =ᶠ[nhds scale]
        fun parameter => stateGradeEquiv parameters grade (projectedStateDerivative projection order parameter state).1 := by
      filter_upwards [isOpen_Ioi.mem_nhds positive] with parameter parameterPositive
      exact inductionHypothesis parameter parameterPositive
    rw [locallyEqual.deriv_eq]
    exact (projectedStateDerivative_hasDerivAt_grade projection order grade admissible scale positive state).deriv

theorem projectedStateDerivative_reality {parameters : PhaseParameters} (projection : SameGradeStateProjection parameters)
    (order : ℕ) (scale : ℝ) (state : projection.map.range) (real : StateReality state.1) :
    StateReality (projectedStateDerivative projection order scale state).1 :=
  projection.real _ (stateScaleDerivative_reality parameters order scale state.1 real)

end Grad.SmoothingFamily

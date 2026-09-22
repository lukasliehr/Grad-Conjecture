import SM18StateProjection

noncomputable section

open Set Filter
open scoped Topology ContDiff

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace Grad.SmoothingFamily

open Grad.CartesianState Grad.COR12Extension

theorem smooth_positive_of_derivatives {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (curve : ℝ → Value) (derivatives : ℕ → ℝ → Value)
    (iterated : ∀ order scale, 0 < scale → iteratedDeriv order curve scale = derivatives order scale)
    (checked : ∀ order scale, 0 < scale → HasDerivAt (derivatives order) (derivatives (order + 1) scale) scale) :
    ContDiffOn ℝ ∞ curve (Ioi 0) := by
  apply contDiffOn_of_differentiableOn_deriv
  intro order _
  apply DifferentiableOn.congr (f := derivatives order)
    (fun scale positive => (checked order scale positive).differentiableAt.differentiableWithinAt)
  intro scale positive
  rw [iteratedDerivWithin_of_isOpen isOpen_Ioi positive, iterated order scale positive]

theorem constrainedScaleDerivative_zero {dimension : ℕ} {parameters : PhaseParameters}
    (projection : SameGradeRealProjection parameters dimension) (scale : ℝ) :
    constrainedScaleDerivative projection 0 scale = constrainedSmoothing projection scale := by
  apply LinearMap.ext
  intro field
  apply Subtype.ext
  exact congrArg projection.map (DFunLike.congr_fun (ambientScaleDerivative_zero parameters scale) field.1)

theorem iteratedDeriv_constrainedSmoothing_grade {dimension : ℕ} {parameters : PhaseParameters}
    (projection : SameGradeRealProjection parameters dimension) (order grade : ℕ) (admissible : 3 ≤ grade)
    (scale : ℝ) (positive : 0 < scale) (field : projection.map.range) :
    iteratedDeriv order (fun parameter => GradeCore.ofCoreLinear (grade := grade)
      (constrainedSmoothing projection parameter field).1) scale =
      GradeCore.ofCoreLinear (grade := grade) (constrainedScaleDerivative projection order scale field).1 := by
  induction order generalizing scale with
  | zero => simp only [iteratedDeriv_zero, constrainedScaleDerivative_zero]
  | succ order inductionHypothesis =>
    rw [iteratedDeriv_succ]
    have locallyEqual : iteratedDeriv order (fun parameter => GradeCore.ofCoreLinear (grade := grade)
        (constrainedSmoothing projection parameter field).1) =ᶠ[nhds scale]
        fun parameter => GradeCore.ofCoreLinear (grade := grade) (constrainedScaleDerivative projection order parameter field).1 := by
      filter_upwards [isOpen_Ioi.mem_nhds positive] with parameter parameterPositive
      exact inductionHypothesis parameter parameterPositive
    rw [locallyEqual.deriv_eq]
    exact (constrainedScaleDerivative_hasDerivAt_grade projection order grade admissible scale positive field).deriv

theorem ambientSmoothing_contDiffOn_grade {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (field : ACore parameters dimension) :
    ContDiffOn ℝ ∞ (fun scale => GradeCore.ofCoreLinear (grade := grade) (ambientSmoothing parameters scale field)) (Ioi 0) :=
  smooth_positive_of_derivatives _ _
    (fun order scale positive => iteratedDeriv_ambientSmoothing_grade parameters order grade scale positive field)
    (fun order scale positive => ambientScaleDerivative_hasDerivAt_grade parameters order grade scale positive field)

theorem constrainedSmoothing_contDiffOn_grade {dimension : ℕ} {parameters : PhaseParameters}
    (projection : SameGradeRealProjection parameters dimension) (grade : ℕ) (admissible : 3 ≤ grade)
    (field : projection.map.range) :
    ContDiffOn ℝ ∞ (fun scale => GradeCore.ofCoreLinear (grade := grade) (constrainedSmoothing projection scale field).1) (Ioi 0) :=
  smooth_positive_of_derivatives _ _
    (fun order scale positive => iteratedDeriv_constrainedSmoothing_grade projection order grade admissible scale positive field)
    (fun order scale positive => constrainedScaleDerivative_hasDerivAt_grade projection order grade admissible scale positive field)

theorem stateSmoothing_contDiffOn_grade (parameters : PhaseParameters) (grade : ℕ) (state : StateCore parameters) :
    ContDiffOn ℝ ∞ (fun scale => stateGradeEquiv parameters grade (stateSmoothing parameters scale state)) (Ioi 0) :=
  smooth_positive_of_derivatives _ _
    (fun order scale positive => iteratedDeriv_stateSmoothing_grade parameters order grade scale positive state)
    (fun order scale positive => stateScaleDerivative_hasDerivAt_grade parameters order grade scale positive state)

theorem projectedStateSmoothing_contDiffOn_grade {parameters : PhaseParameters}
    (projection : SameGradeStateProjection parameters) (grade : ℕ) (admissible : 3 ≤ grade)
    (state : projection.map.range) :
    ContDiffOn ℝ ∞ (fun scale => stateGradeEquiv parameters grade (projectedStateSmoothing projection scale state).1) (Ioi 0) :=
  smooth_positive_of_derivatives _ _
    (fun order scale positive => iteratedDeriv_projectedStateSmoothing_grade projection order grade admissible scale positive state)
    (fun order scale positive => projectedStateDerivative_hasDerivAt_grade projection order grade admissible scale positive state)

theorem tendsto_of_inverse_norm_bound {Value : Type*} [NormedAddCommGroup Value]
    (curve : ℝ → Value) (target : Value) (constant : ℝ)
    (bound : ∀ scale, 0 < scale → ‖curve scale - target‖ ≤ constant * scale⁻¹) :
    Tendsto curve atTop (nhds target) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun scale => norm_nonneg _))
    (by filter_upwards [eventually_gt_atTop 0] with scale positive; exact bound scale positive)
  simpa only [mul_zero] using tendsto_const_nhds.mul (tendsto_inv_atTop_zero : Tendsto (fun scale : ℝ => scale⁻¹) atTop (nhds 0))

theorem adjacent_grade_rpow (scale : ℝ) (positive : 0 < scale) (grade : ℕ) :
    scale ^ ((grade : ℝ) - ((grade + 1 : ℕ) : ℝ)) = scale⁻¹ := by
  rw [rpow_grade_difference scale positive.le grade (grade + 1) (Nat.le_succ grade)]
  simp

theorem ambientSmoothing_tendsto_grade {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (field : ACore parameters dimension) :
    Tendsto (fun scale => GradeCore.ofCoreLinear (grade := grade) (ambientSmoothing parameters scale field)) atTop
      (nhds (GradeCore.ofCoreLinear (grade := grade) field)) := by
  apply tendsto_of_inverse_norm_bound _ _
    ((sameGradeConstant grade * sameGradeConstant (grade + 1)) * ‖GradeCore.ofCoreLinear (grade := grade + 1) field‖)
  intro scale positive
  have estimate := ambientRemainder_norm_le parameters scale positive grade (grade + 1) (Nat.le_succ grade) field
  rw [adjacent_grade_rpow scale positive grade, map_sub, norm_sub_rev] at estimate
  exact estimate.trans_eq (by ring)

theorem constrainedSmoothing_tendsto_grade {dimension : ℕ} {parameters : PhaseParameters}
    (projection : SameGradeRealProjection parameters dimension) (grade : ℕ) (admissible : 3 ≤ grade)
    (field : projection.map.range) :
    Tendsto (fun scale => GradeCore.ofCoreLinear (grade := grade) (constrainedSmoothing projection scale field).1) atTop
      (nhds (GradeCore.ofCoreLinear (grade := grade) field.1)) := by
  apply tendsto_of_inverse_norm_bound _ _
    ((projection.bound grade * (sameGradeConstant grade * sameGradeConstant (grade + 1))) *
      ‖GradeCore.ofCoreLinear (grade := grade + 1) field.1‖)
  intro scale positive
  have estimate := constrainedRemainder_norm_le projection scale positive grade (grade + 1) (Nat.le_succ grade) admissible field
  rw [adjacent_grade_rpow scale positive grade, map_sub, norm_sub_rev] at estimate
  exact estimate.trans_eq (by ring)

theorem stateSmoothing_tendsto_grade (parameters : PhaseParameters) (grade : ℕ) (state : StateCore parameters) :
    Tendsto (fun scale => stateGradeEquiv parameters grade (stateSmoothing parameters scale state)) atTop
      (nhds (stateGradeEquiv parameters grade state)) := by
  apply tendsto_of_inverse_norm_bound _ _
    (stateRemainderConstant grade (grade + 1) * ‖stateToGrade parameters (grade + 1) state‖)
  intro scale positive
  have estimate := stateRemainder_norm_le parameters scale positive grade (grade + 1) (Nat.le_succ grade) state
  rw [adjacent_grade_rpow scale positive grade, ← stateGradeEquiv_norm, map_sub, norm_sub_rev] at estimate
  exact estimate.trans_eq (by ring)

theorem projectedStateSmoothing_tendsto_grade {parameters : PhaseParameters}
    (projection : SameGradeStateProjection parameters) (grade : ℕ) (admissible : 3 ≤ grade)
    (state : projection.map.range) :
    Tendsto (fun scale => stateGradeEquiv parameters grade (projectedStateSmoothing projection scale state).1) atTop
      (nhds (stateGradeEquiv parameters grade state.1)) := by
  apply tendsto_of_inverse_norm_bound _ _
    ((projection.bound grade * stateRemainderConstant grade (grade + 1)) * ‖stateToGrade parameters (grade + 1) state.1‖)
  intro scale positive
  have estimate := projectedStateRemainder_norm_le projection scale positive grade (grade + 1) (Nat.le_succ grade) admissible state
  rw [adjacent_grade_rpow scale positive grade, ← stateGradeEquiv_norm, map_sub, norm_sub_rev] at estimate
  exact estimate.trans_eq (by ring)

end Grad.SmoothingFamily

import AKCY12EnrichedOriginalNewtonStages
import AKCR1OriginalSmoothStateLimit
import Mathlib.Analysis.Normed.Group.FunctionSeries

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3500
open Filter
open scoped Topology BigOperators

namespace Grad.NashMoser.OriginalIteration
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.SmoothingFamily Grad.Q24Realization Grad.NashMoser.OriginalLimit Grad.NashMoser.Numeric

variable {parameters : PhaseParameters} {reference : Seed.Parameters}
    {inside : reference ∈ Seed.parameterDomain} {base loss : ℕ} {cellLength : ℝ}
    {neighborhood : OriginalNewtonNeighborhood parameters reference inside base}
    {inverse : OriginalNewtonInverse neighborhood cellLength loss}

namespace OriginalNewtonScale
variable (scale : OriginalNewtonScale inverse)

def gradeCorrection (grade : AdmissibleGrade) (point : scale.parameterDomain) (index : ℕ) :
    stateRange parameters reference inside grade.val grade.property :=
  stateSmoothEmbedding parameters reference inside grade.val grade.property
    (inverse.correction point.val (scale.iterate point.val point.property index) (newtonTime scale.initial index))

def gradeLimit (grade : AdmissibleGrade) (point : scale.parameterDomain) :
    stateRange parameters reference inside grade.val grade.property :=
  ∑' index, scale.gradeCorrection grade point index

theorem grade_iterate_sum (grade : AdmissibleGrade) (point : scale.parameterDomain) (index : ℕ) :
    stateSmoothEmbedding parameters reference inside grade.val grade.property
      (scale.iterate point.val point.property index) =
    ∑ stage ∈ Finset.range index, scale.gradeCorrection grade point stage := by
  induction index with
  | zero => simp only [scale.iterate_zero,map_zero,Finset.range_zero,Finset.sum_empty]
  | succ index inductionHypothesis =>
    rw [scale.iterate_step,map_add,inductionHypothesis,Finset.sum_range_succ]
    rfl

theorem grade_correction_bound (grade : AdmissibleGrade) (point : scale.parameterDomain) (index : ℕ) :
    ‖scale.gradeCorrection grade point index‖ ≤ inverse.correctionConstant grade.val *
      newtonTime scale.initial index ^ (grade.val:ℝ) *
        inverse.residualSize point.val (scale.iterate point.val point.property index) :=
  (originalStateNorm_le_size parameters reference inside base grade.val grade.val grade.property (by omega) _).trans
    (inverse.correction_bound point.val point.property.1 _
      ((scale.iterate_low point.val point.property index).trans (by linarith [neighborhood.radiusPositive]))
      _ (newtonTime_pos (by linarith [scale.initialLarge]) index) grade.val)

/-- All complete grades receive uniform convergence of the SAME actual
original iteration on the one fixed parameter set. This consumes the
accepted numeric bootstrap without the stronger guarded-data interface. -/
theorem grade_uniform (grade : AdmissibleGrade) :
    TendstoUniformly (fun index (point : scale.parameterDomain) =>
      stateSmoothEmbedding parameters reference inside grade.val grade.property
        (scale.iterate point.val point.property index)) (scale.gradeLimit grade) atTop := by
  have lossReal : (1:ℝ) ≤ loss := by exact_mod_cast (show 1 ≤ loss by have := scale.lossLarge; omega)
  obtain ⟨order,gap⟩ := ((tendsto_atTop.1 (bootstrapExponent_tendsto lossReal)) ((grade.val:ℝ)+2)).exists
  let decay := bootstrapConstant scale.initial loss (inverse.quadraticConstant scale.lossLarge)
    (inverse.defectConstant scale.lossLarge) order
  let exponent := bootstrapExponent loss order-(grade.val:ℝ)
  let constant := inverse.correctionConstant grade.val
  have exponentLarge : 2 ≤ exponent := by dsimp [exponent]; linarith
  have majorant : Summable (fun index : ℕ => constant*decay*newtonTime scale.initial index^(-exponent)) := by
    simpa only [zero_add] using (newtonTime_tail scale.initialLarge exponentLarge 0).1.mul_left (constant*decay)
  have paid (index : ℕ) (point : scale.parameterDomain) :
      ‖scale.gradeCorrection grade point index‖ ≤ constant*decay*newtonTime scale.initial index^(-exponent) := by
    have positive := newtonTime_pos (by linarith [scale.initialLarge] : 0 < scale.initial) index
    have bound := scale.grade_correction_bound grade point index
    have residual := scale.iterate_allOrdersDecay point.val point.property order index
    have result := mul_le_mul_of_nonneg_left residual
      (mul_nonneg ((by norm_num : (0:ℝ) ≤ 1).trans (inverse.correctionConstant_one_le grade.val))
        (Real.rpow_nonneg positive.le (grade.val:ℝ)))
    exact bound.trans (result.trans_eq (by
      dsimp only [exponent,constant,decay]
      rw [show -(bootstrapExponent (loss:ℝ) order-(grade.val:ℝ)) =
        (grade.val:ℝ)+ -bootstrapExponent loss order by ring,Real.rpow_add positive]
      ring))
  simp only [scale.grade_iterate_sum]
  exact tendstoUniformly_tsum_nat majorant paid

theorem gradeConverges (point : scale.parameterDomain) :
    ∀ grade : AdmissibleGrade,
      ∃ limit : stateRange parameters reference inside grade.val grade.property,
      Tendsto (fun index => stateSmoothEmbedding parameters reference inside grade.val grade.property
        (scale.iterate point.val point.property index)) atTop (𝓝 limit) :=
  fun grade => ⟨scale.gradeLimit grade point,(scale.grade_uniform grade).tendsto_at point⟩

/-- Accepted COR26 reconstructs ONE original-width real constrained smooth
core from these actual finite stages, not a new state at each grade. -/
def originalLimit (point : scale.parameterDomain) : stateSmoothRange parameters reference inside :=
  convergentStateLimit parameters reference inside (scale.iterate point.val point.property) (scale.gradeConverges point)

theorem originalLimit_tendsto (point : scale.parameterDomain) (grade : AdmissibleGrade) :
    Tendsto (fun index => stateSmoothEmbedding parameters reference inside grade.val grade.property
      (scale.iterate point.val point.property index)) atTop
        (𝓝 (stateSmoothEmbedding parameters reference inside grade.val grade.property (scale.originalLimit point))) :=
  convergentStateLimit_tendsto parameters reference inside (scale.iterate point.val point.property)
    (scale.gradeConverges point) grade

theorem originalLimit_grade (point : scale.parameterDomain) (grade : AdmissibleGrade) :
    stateSmoothEmbedding parameters reference inside grade.val grade.property (scale.originalLimit point) =
      scale.gradeLimit grade point :=
  tendsto_nhds_unique (scale.originalLimit_tendsto point grade) ((scale.grade_uniform grade).tendsto_at point)

theorem originalLimit_low (point : scale.parameterDomain) :
    stateSize parameters reference inside base loss (scale.originalLimit point) ≤ neighborhood.radius/2 :=
  convergentStateLimit_norm_le parameters reference inside (scale.iterate point.val point.property)
    (scale.gradeConverges point) ⟨base+loss,by have := neighborhood.baseLarge; omega⟩
      (neighborhood.radius/2) (scale.iterate_low point.val point.property)

theorem originalLimit_uniform (grade : AdmissibleGrade) :
    TendstoUniformly (fun index (point : scale.parameterDomain) =>
      stateSmoothEmbedding parameters reference inside grade.val grade.property
        (scale.iterate point.val point.property index))
      (fun point => stateSmoothEmbedding parameters reference inside grade.val grade.property
        (scale.originalLimit point)) atTop := by
  simpa only [scale.originalLimit_grade] using scale.grade_uniform grade

/-- The actual branch is continuous whenever its finite original iterates
are continuous. No differentiability of the limit is assumed here. -/
theorem originalLimit_continuous (grade : AdmissibleGrade)
    (finiteContinuous : ∀ index, Continuous (fun point : scale.parameterDomain =>
      stateSmoothEmbedding parameters reference inside grade.val grade.property
        (scale.iterate point.val point.property index))) :
    Continuous (fun point : scale.parameterDomain =>
      stateSmoothEmbedding parameters reference inside grade.val grade.property (scale.originalLimit point)) := by
  apply continuousOn_univ.mp
  apply (tendstoUniformlyOn_univ.mpr (scale.originalLimit_uniform grade)).continuousOn
  exact Filter.Frequently.of_forall (fun index => (finiteContinuous index).continuousOn)

end OriginalNewtonScale
end Grad.NashMoser.OriginalIteration

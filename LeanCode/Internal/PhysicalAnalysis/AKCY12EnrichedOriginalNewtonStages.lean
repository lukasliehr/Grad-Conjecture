import AKCY11ActualFiniteStageRecurrence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3500
open Set

namespace Grad.NashMoser.OriginalIteration
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.SmoothingFamily Grad.Q24Realization Grad.NashMoser.OriginalLimit Grad.NashMoser.Numeric

variable {parameters : PhaseParameters} {reference : Seed.Parameters}
    {inside : reference ∈ Seed.parameterDomain} {base loss : ℕ} {cellLength : ℝ}
    {neighborhood : OriginalNewtonNeighborhood parameters reference inside base}
    (inverse : OriginalNewtonInverse neighborhood cellLength loss)

/-- Three finite numerical smallness conditions, fixed before iteration.
The residual neighborhood below is then chosen once at this initial scale. -/
structure OriginalNewtonScale where
  lossLarge : 6 ≤ loss
  initial : ℝ
  initialLarge : 4 ≤ initial
  budgetSmall : 2*inverse.correctionConstant loss * initial ^ (-(initialDecay loss-(loss:ℝ))) ≤ neighborhood.radius/2
  quadraticSmall : inverse.quadraticConstant lossLarge * initial ^ (-(2*(loss:ℝ)+4)) ≤ 1/2
  defectSmall : inverse.defectConstant lossLarge (initialCutoff loss) * initial ^ (-2:ℝ) ≤ 1/2

namespace OriginalNewtonScale
variable {inverse} (scale : OriginalNewtonScale inverse)

/-- This single residual sublevel set is shared by every Newton stage and
every higher-order bootstrap. No grade-dependent neighborhood is introduced. -/
def parameterDomain : Set OriginalFiniteParameter :=
  neighborhood.parameterDomain ∩ {finite | inverse.residualSize finite 0 ≤ scale.initial ^ (-initialDecay loss)}

/-- Enriched stages retain the accumulated bound in EVERY original grade.
The written NM06 high bounds are derived from these finite budgets. -/
def Stage (finite : OriginalFiniteParameter) (index : ℕ) :=
  {state : stateSmoothRange parameters reference inside //
    (∀ grade, stateSize parameters reference inside base grade state ≤
      stageGradeBudget scale.initial loss (inverse.correctionConstant grade) grade index) ∧
    inverse.residualSize finite state ≤ newtonTime scale.initial index ^ (-initialDecay loss)}

theorem budget_le_half (index : ℕ) :
    stageGradeBudget scale.initial loss (inverse.correctionConstant loss) loss index ≤ neighborhood.radius/2 := by
  rw [stageGradeBudget_at_loss scale.initial _ (by linarith [scale.initialLarge])]
  exact (finiteCorrectionBudget_le scale.initial loss (inverse.correctionConstant loss) index scale.initialLarge
    (by exact_mod_cast (show 1 ≤ loss by have := scale.lossLarge; omega))
    ((by norm_num : (0:ℝ) ≤ 1).trans (inverse.correctionConstant_one_le loss))).trans scale.budgetSmall

def initialStage (finite : OriginalFiniteParameter) (member : finite ∈ scale.parameterDomain) :
    scale.Stage finite 0 :=
  ⟨0, fun grade => by rw [map_zero,stageGradeBudget_zero], by
    simpa only [Set.mem_ofPred_eq,newtonTime,pow_zero,Real.rpow_one] using member.2⟩

theorem stage_low {finite : OriginalFiniteParameter} {index : ℕ} (stage : scale.Stage finite index) :
    stateSize parameters reference inside base loss stage.val ≤ neighborhood.radius/2 :=
  (stage.property.1 loss).trans (scale.budget_le_half index)

theorem stage_coarse {finite : OriginalFiniteParameter} {index : ℕ} (stage : scale.Stage finite index) (grade : ℕ) :
    stateSize parameters reference inside base grade stage.val ≤
      inverse.correctionConstant grade * previousStageTime scale.initial index ^ (grade:ℝ) :=
  (stage.property.1 grade).trans (stageGradeBudget_coarse scale.initial loss (inverse.correctionConstant grade)
    scale.initialLarge (by exact_mod_cast (show 1 ≤ loss by have := scale.lossLarge; omega))
    ((by norm_num : (0:ℝ) ≤ 1).trans (inverse.correctionConstant_one_le grade)) grade index)

theorem stage_residual_le_one {finite : OriginalFiniteParameter} {index : ℕ} (stage : scale.Stage finite index) :
    inverse.residualSize finite stage.val ≤ 1 := by
  have timeLarge : 1 ≤ newtonTime scale.initial index :=
    (by linarith [scale.initialLarge] : 1 ≤ scale.initial).trans
      (newtonTime_lower (by linarith [scale.initialLarge]) index)
  have power := Real.rpow_le_rpow_of_exponent_le timeLarge
    (show -initialDecay (loss:ℝ) ≤ 0 by unfold initialDecay; nlinarith [Nat.cast_nonneg (α := ℝ) loss])
  exact stage.property.2.trans (by simpa only [Real.rpow_zero] using power)

theorem stageCorrection_bound (finite : OriginalFiniteParameter) (member : finite ∈ scale.parameterDomain)
    {index : ℕ} (stage : scale.Stage finite index) (grade : ℕ) :
    stateSize parameters reference inside base grade
      (inverse.correction finite stage.val (newtonTime scale.initial index)) ≤
    inverse.correctionConstant grade * newtonTime scale.initial index ^ (grade:ℝ) *
      newtonTime scale.initial index ^ (-initialDecay loss) := by
  have positive := newtonTime_pos (by linarith [scale.initialLarge] : 0 < scale.initial) index
  exact (inverse.correction_bound finite member.1 stage.val
    ((scale.stage_low stage).trans (by linarith [neighborhood.radiusPositive])) _ positive grade).trans
      (mul_le_mul_of_nonneg_left stage.property.2
        (mul_nonneg ((by norm_num : (0:ℝ) ≤ 1).trans (inverse.correctionConstant_one_le grade))
          (Real.rpow_nonneg positive.le (grade:ℝ))))

theorem next_budget (finite : OriginalFiniteParameter) (member : finite ∈ scale.parameterDomain)
    {index : ℕ} (stage : scale.Stage finite index) (grade : ℕ) :
    stateSize parameters reference inside base grade
      (stage.val+inverse.correction finite stage.val (newtonTime scale.initial index)) ≤
    stageGradeBudget scale.initial loss (inverse.correctionConstant grade) grade (index+1) := by
  rw [stageGradeBudget_succ]
  exact (map_add_le_add (stateSize parameters reference inside base grade) _ _).trans
    (add_le_add (stage.property.1 grade) (scale.stageCorrection_bound finite member stage grade))

theorem stage_chord (finite : OriginalFiniteParameter) (member : finite ∈ scale.parameterDomain)
    {index : ℕ} (stage : scale.Stage finite index) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    stateSize parameters reference inside base 0
      (stage.val+t•inverse.correction finite stage.val (newtonTime scale.initial index)) ≤ 2*neighborhood.radius := by
  have triangle := (map_add_le_add (stateSize parameters reference inside base loss) stage.val
    (t•inverse.correction finite stage.val (newtonTime scale.initial index))).trans
      (add_le_add (stage.property.1 loss)
        ((seminorm_unit_smul _ _ t ht).trans (scale.stageCorrection_bound finite member stage loss)))
  rw [← stageGradeBudget_succ] at triangle
  exact ((stateSize_mono parameters reference inside base (Nat.zero_le loss) _).trans triangle).trans
    ((scale.budget_le_half (index+1)).trans (by linarith [neighborhood.radiusPositive]))

def nextStage (finite : OriginalFiniteParameter) (member : finite ∈ scale.parameterDomain)
    {index : ℕ} (stage : scale.Stage finite index) : scale.Stage finite (index+1) :=
  ⟨stage.val+inverse.correction finite stage.val (newtonTime scale.initial index),
    scale.next_budget finite member stage,
    next_residual_decay scale.initial (inverse.quadraticConstant scale.lossLarge)
      (inverse.defectConstant scale.lossLarge (initialCutoff loss))
      (inverse.residualSize finite stage.val)
      (inverse.residualSize finite (stage.val+inverse.correction finite stage.val (newtonTime scale.initial index)))
      loss index scale.initialLarge
      ((by norm_num : (0:ℝ) ≤ 1).trans (inverse.quadraticConstant_one_le scale.lossLarge))
      ((by norm_num : (0:ℝ) ≤ 1).trans (inverse.defectConstant_one_le scale.lossLarge _))
      (apply_nonneg _ _) scale.quadraticSmall scale.defectSmall stage.property.2
      (inverse.actual_stage_recurrence scale.lossLarge scale.initial scale.initialLarge finite member.1 stage.val
        ((scale.stage_low stage).trans (by linarith [neighborhood.radiusPositive])) index (scale.stage_coarse stage)
        (scale.stage_residual_le_one stage) (scale.stage_chord finite member stage) (initialCutoff loss))⟩

/-- Primitive recursion evaluates the literal original smoothed Newton step
only after the current stage's low and high bounds have been proved. -/
def stages (finite : OriginalFiniteParameter) (member : finite ∈ scale.parameterDomain) :
    (index : ℕ) → scale.Stage finite index :=
  Nat.rec (scale.initialStage finite member) (fun _ stage => scale.nextStage finite member stage)

def iterate (finite : OriginalFiniteParameter) (member : finite ∈ scale.parameterDomain)
    (index : ℕ) : stateSmoothRange parameters reference inside := (scale.stages finite member index).val

theorem iterate_zero (finite : OriginalFiniteParameter) (member : finite ∈ scale.parameterDomain) :
    scale.iterate finite member 0 = 0 := rfl

theorem iterate_step (finite : OriginalFiniteParameter) (member : finite ∈ scale.parameterDomain) (index : ℕ) :
    scale.iterate finite member (index+1) = scale.iterate finite member index+
      inverse.correction finite (scale.iterate finite member index) (newtonTime scale.initial index) := rfl

theorem iterate_low (finite : OriginalFiniteParameter) (member : finite ∈ scale.parameterDomain) (index : ℕ) :
    stateSize parameters reference inside base loss (scale.iterate finite member index) ≤ neighborhood.radius/2 :=
  scale.stage_low (scale.stages finite member index)

theorem iterate_decay (finite : OriginalFiniteParameter) (member : finite ∈ scale.parameterDomain) (index : ℕ) :
    inverse.residualSize finite (scale.iterate finite member index) ≤ newtonTime scale.initial index ^ (-initialDecay loss) :=
  (scale.stages finite member index).property.2

theorem iterate_recurrence (finite : OriginalFiniteParameter) (member : finite ∈ scale.parameterDomain)
    (index cutoff : ℕ) :
    inverse.residualSize finite (scale.iterate finite member (index+1)) ≤
      inverse.quadraticConstant scale.lossLarge * newtonTime scale.initial index ^ (2*(loss:ℝ)) *
        (inverse.residualSize finite (scale.iterate finite member index))^2 +
      inverse.defectConstant scale.lossLarge cutoff * newtonTime scale.initial index ^ (-(((cutoff:ℝ)-8*loss)/3)) := by
  rw [scale.iterate_step]
  exact inverse.actual_stage_recurrence scale.lossLarge scale.initial scale.initialLarge finite member.1
    (scale.iterate finite member index) ((scale.iterate_low finite member index).trans (by linarith [neighborhood.radiusPositive]))
    index (scale.stage_coarse (scale.stages finite member index))
    (scale.stage_residual_le_one (scale.stages finite member index))
    (scale.stage_chord finite member (scale.stages finite member index)) cutoff

theorem iterate_allOrdersDecay (finite : OriginalFiniteParameter) (member : finite ∈ scale.parameterDomain)
    (order index : ℕ) :
    inverse.residualSize finite (scale.iterate finite member index) ≤
      bootstrapConstant scale.initial loss (inverse.quadraticConstant scale.lossLarge)
        (inverse.defectConstant scale.lossLarge) order *
          newtonTime scale.initial index ^ (-bootstrapExponent loss order) :=
  same_sequence_bootstrap_decay scale.initial loss (inverse.quadraticConstant scale.lossLarge)
    (inverse.defectConstant scale.lossLarge) (fun index => inverse.residualSize finite (scale.iterate finite member index))
    scale.initialLarge (by exact_mod_cast (show 1 ≤ loss by have := scale.lossLarge; omega))
    ((by norm_num : (0:ℝ) ≤ 1).trans (inverse.quadraticConstant_one_le scale.lossLarge))
    (fun cutoff => (by norm_num : (0:ℝ) ≤ 1).trans (inverse.defectConstant_one_le scale.lossLarge cutoff))
    (fun _ => apply_nonneg _ _) (scale.iterate_decay finite member) (scale.iterate_recurrence finite member) order index

end OriginalNewtonScale
end Grad.NashMoser.OriginalIteration

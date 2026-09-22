import NewtonFiniteStage

noncomputable section

namespace Grad.NashMoser.Numeric

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [SeminormedAddCommGroup F]

/-- Inputs to the finite-stage construction. These are the explicit
quantitative hypotheses of the abstract Newton argument, not assertions
that the project's still-missing nonlinear map and inverse have been built.
The correction is evaluated only at a state already inside the low ball;
the residual estimate is invoked only after the entire chord is admissible. -/
structure GuardedNewtonData (initial radius highConstant quadratic : ℝ)
    (smoothing : ℕ → ℝ) (loss : ℕ) where
  mapping : E → F
  correction : ℕ → {state : E // ‖state‖ ≤ radius} → E
  initialLarge : 4 ≤ initial
  lossLarge : 1 ≤ loss
  radiusPositive : 0 < radius
  highNonnegative : 0 ≤ highConstant
  quadraticNonnegative : 0 ≤ quadratic
  smoothingNonnegative : ∀ cutoff, 0 ≤ smoothing cutoff
  lowBudget : 2 * highConstant * initial ^ (-(initialDecay loss - loss)) ≤ radius / 2
  quadraticSmall : quadratic * initial ^ (-(2 * (loss : ℝ) + 4)) ≤ 1 / 2
  smoothingSmall : smoothing (initialCutoff loss) * initial ^ (-2 : ℝ) ≤ 1 / 2
  initialResidual : ‖mapping 0‖ ≤ initial ^ (-initialDecay loss)
  correctionBound : ∀ index state,
    ‖correction index state‖ ≤ highConstant *
      newtonTime initial index ^ (loss : ℝ) * ‖mapping state.val‖
  residualRecurrence : ∀ index state,
    (∀ time ∈ Set.Icc (0 : ℝ) 1,
      ‖state.val + time • correction index state‖ ≤ radius) →
    ∀ cutoff : ℕ,
    ‖mapping (state.val + correction index state)‖ ≤
      quadratic * newtonTime initial index ^ (2 * (loss : ℝ)) *
          ‖mapping state.val‖ ^ 2 +
        smoothing cutoff * newtonTime initial index ^
          (-(((cutoff : ℝ) - 8 * loss) / 3))

variable {E F}

namespace GuardedNewtonData

variable {initial radius highConstant quadratic : ℝ} {smoothing : ℕ → ℝ} {loss : ℕ}
  (data : GuardedNewtonData E F initial radius highConstant quadratic smoothing loss)

include data in
theorem budget_le_half (index : ℕ) :
    finiteCorrectionBudget initial loss highConstant index ≤ radius / 2 := by
  exact (finiteCorrectionBudget_le initial loss highConstant index
    data.initialLarge (by exact_mod_cast data.lossLarge) data.highNonnegative).trans
    data.lowBudget

/-- A stage contains a real state and both estimates proved at that stage. -/
def Stage (index : ℕ) :=
  {state : E //
    ‖state‖ ≤ finiteCorrectionBudget initial loss highConstant index ∧
      ‖data.mapping state‖ ≤ newtonTime initial index ^ (-initialDecay loss)}

def initialStage : data.Stage 0 :=
  ⟨0, by simp [finiteCorrectionBudget], by
    simpa only [newtonTime, pow_zero, Real.rpow_one] using data.initialResidual⟩

def admissibleState {index : ℕ} (stage : data.Stage index) :
    {state : E // ‖state‖ ≤ radius} :=
  ⟨stage.val, stage.property.1.trans
    ((data.budget_le_half index).trans (by linarith [data.radiusPositive]))⟩

theorem stageCorrection_bound {index : ℕ} (stage : data.Stage index) :
    ‖data.correction index (data.admissibleState stage)‖ ≤
      highConstant * newtonTime initial index ^ (-(initialDecay loss - loss)) := by
  have timePositive := newtonTime_pos (by linarith [data.initialLarge] : 0 < initial) index
  calc
    _ ≤ highConstant * newtonTime initial index ^ (loss : ℝ) *
        ‖data.mapping stage.val‖ := data.correctionBound index (data.admissibleState stage)
    _ ≤ highConstant * newtonTime initial index ^ (loss : ℝ) *
        newtonTime initial index ^ (-initialDecay loss) :=
      mul_le_mul_of_nonneg_left stage.property.2
        (mul_nonneg data.highNonnegative (Real.rpow_nonneg timePositive.le _))
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add timePositive]
      congr 2
      ring

theorem next_norm_budget {index : ℕ} (stage : data.Stage index) :
    ‖stage.val + data.correction index (data.admissibleState stage)‖ ≤
      finiteCorrectionBudget initial loss highConstant (index + 1) := by
  rw [finiteCorrectionBudget_succ]
  exact (norm_add_le _ _).trans
    (add_le_add stage.property.1 (data.stageCorrection_bound stage))

theorem chord_admissible {index : ℕ} (stage : data.Stage index)
    (time : ℝ) (timeIn : time ∈ Set.Icc (0 : ℝ) 1) :
    ‖stage.val + time • data.correction index (data.admissibleState stage)‖ ≤ radius := by
  have scalarBound :
      ‖time • data.correction index (data.admissibleState stage)‖ ≤
        ‖data.correction index (data.admissibleState stage)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg timeIn.1]
    exact mul_le_of_le_one_left (norm_nonneg _) timeIn.2
  calc
    _ ≤ ‖stage.val‖ + ‖time • data.correction index (data.admissibleState stage)‖ :=
      norm_add_le _ _
    _ ≤ finiteCorrectionBudget initial loss highConstant index +
        highConstant * newtonTime initial index ^ (-(initialDecay loss - loss)) :=
      add_le_add stage.property.1 (scalarBound.trans (data.stageCorrection_bound stage))
    _ = finiteCorrectionBudget initial loss highConstant (index + 1) :=
      (finiteCorrectionBudget_succ _ _ _ _).symm
    _ ≤ radius / 2 := data.budget_le_half (index + 1)
    _ ≤ radius := by linarith [data.radiusPositive]

def nextStage {index : ℕ} (stage : data.Stage index) : data.Stage (index + 1) :=
  ⟨stage.val + data.correction index (data.admissibleState stage),
    data.next_norm_budget stage,
    next_residual_decay initial quadratic (smoothing (initialCutoff loss))
      ‖data.mapping stage.val‖
      ‖data.mapping (stage.val + data.correction index (data.admissibleState stage))‖
      loss index data.initialLarge data.quadraticNonnegative
      (data.smoothingNonnegative _) (norm_nonneg _) data.quadraticSmall
      data.smoothingSmall stage.property.2
      (data.residualRecurrence index (data.admissibleState stage)
        (data.chord_admissible stage) (initialCutoff loss))⟩

/-- Dependent primitive recursion constructs each admissible finite stage.
There is no evaluation of an inverse at a prospective or unproved state. -/
def stages : (index : ℕ) → data.Stage index :=
  Nat.rec data.initialStage (fun _ stage => data.nextStage stage)

def iterate (index : ℕ) : E := (data.stages index).val

theorem iterate_zero : data.iterate 0 = 0 := rfl

theorem iterate_step (index : ℕ) :
    data.iterate (index + 1) = data.iterate index +
      data.correction index (data.admissibleState (data.stages index)) := rfl

theorem iterate_norm_le_half (index : ℕ) : ‖data.iterate index‖ ≤ radius / 2 :=
  (data.stages index).property.1.trans (data.budget_le_half index)

theorem iterate_residual_decay (index : ℕ) :
    ‖data.mapping (data.iterate index)‖ ≤
      newtonTime initial index ^ (-initialDecay loss) :=
  (data.stages index).property.2

theorem iterate_allCutoffRecurrence (index cutoff : ℕ) :
    ‖data.mapping (data.iterate (index + 1))‖ ≤
      quadratic * newtonTime initial index ^ (2 * (loss : ℝ)) *
        ‖data.mapping (data.iterate index)‖ ^ 2 +
      smoothing cutoff * newtonTime initial index ^
        (-(((cutoff : ℝ) - 8 * loss) / 3)) := by
  rw [data.iterate_step]
  exact data.residualRecurrence index (data.admissibleState (data.stages index))
    (data.chord_admissible (data.stages index)) cutoff

/-- All bootstrap orders apply to the very same constructed sequence. -/
theorem iterate_allOrdersDecay (order index : ℕ) :
    ‖data.mapping (data.iterate index)‖ ≤
      bootstrapConstant initial loss quadratic smoothing order *
        newtonTime initial index ^ (-bootstrapExponent loss order) :=
  same_sequence_bootstrap_decay initial loss quadratic smoothing
    (fun stage => ‖data.mapping (data.iterate stage)‖)
    data.initialLarge (by exact_mod_cast data.lossLarge)
    data.quadraticNonnegative data.smoothingNonnegative
    (fun _ => norm_nonneg _) data.iterate_residual_decay
    data.iterate_allCutoffRecurrence order index

/-- A zero initial residual produces the identical zero sequence, not merely
a small nearby branch. -/
theorem iterate_of_zero_seed (seedZero : data.mapping 0 = 0) (index : ℕ) :
    data.iterate index = 0 := by
  induction index with
  | zero => exact data.iterate_zero
  | succ index inductionHypothesis =>
    have bound := data.correctionBound index
      (data.admissibleState (data.stages index))
    change ‖data.correction index (data.admissibleState (data.stages index))‖ ≤
      highConstant * newtonTime initial index ^ (loss : ℝ) *
        ‖data.mapping (data.iterate index)‖ at bound
    rw [inductionHypothesis, seedZero, norm_zero, mul_zero] at bound
    have correctionZero := norm_eq_zero.mp (le_antisymm bound (norm_nonneg _))
    rw [data.iterate_step, inductionHypothesis, correctionZero, add_zero]

end GuardedNewtonData

end Grad.NashMoser.Numeric

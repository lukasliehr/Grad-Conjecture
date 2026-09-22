import AxisExtraction

noncomputable section

open scoped BigOperators ENNReal

namespace Grad.AxisSplit

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds

/-- The literal axis weight `exp(sigma0 lambda_n) lambda_n^q` of the
`T^q` grade, the exact phase weight at the axis. -/
def axisWeight (parameters : PhaseParameters) (grade : ℕ) (cell : ℤ) : ℝ :=
  Real.exp (parameters.sigma0 * cellFrequency cell) * cellFrequency cell ^ grade

theorem axisWeight_pos (parameters : PhaseParameters) (grade : ℕ) (cell : ℤ) :
    0 < axisWeight parameters grade cell :=
  mul_pos (Real.exp_pos _) (pow_pos (cellFrequency_pos cell) grade)

theorem axisWeight_mono (parameters : PhaseParameters) {lower upper : ℕ}
    (gradeLe : lower ≤ upper) (cell : ℤ) :
    axisWeight parameters lower cell ≤ axisWeight parameters upper cell := by
  unfold axisWeight
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact pow_le_pow_right₀ (cellFrequency_one_le cell) gradeLe

theorem axisWeight_eq_weight_origin (parameters : PhaseParameters) (grade : ℕ)
    (cell : ℤ) :
    axisWeight parameters grade cell =
      cartesianWeight parameters cell originPoint.val * cellFrequency cell ^ grade := by
  rw [cartesianWeight_origin]
  rfl

/-- The weighted `T^q` coordinates of a planar axis sequence. -/
def axisCoordinates (parameters : PhaseParameters) (grade : ℕ)
    (sequence : ℤ → ComplexEuclidean 2) : ℤ → ComplexEuclidean 2 :=
  fun cell => axisWeight parameters grade cell • sequence cell

theorem axisCoordinates_add (parameters : PhaseParameters) (grade : ℕ)
    (first second : ℤ → ComplexEuclidean 2) :
    axisCoordinates parameters grade (first + second) =
      axisCoordinates parameters grade first + axisCoordinates parameters grade second := by
  funext cell
  exact smul_add _ _ _

theorem axisCoordinates_smul (parameters : PhaseParameters) (grade : ℕ) (scalar : ℂ)
    (sequence : ℤ → ComplexEuclidean 2) :
    axisCoordinates parameters grade (scalar • sequence) =
      scalar • axisCoordinates parameters grade sequence := by
  funext cell
  exact smul_comm (axisWeight parameters grade cell) scalar (sequence cell)

/-- `T^∞`: the all-grade axis coefficient core, the exact COR08 carrier
condition at every grade. -/
def axisCoreSubmodule (parameters : PhaseParameters) :
    Submodule ℂ (ℤ → ComplexEuclidean 2) where
  carrier sequence := ∀ grade : ℕ, Memℓp (axisCoordinates parameters grade sequence) 2
  zero_mem' := by
    intro grade
    have coordinatesZero : axisCoordinates parameters grade 0 = 0 := by
      funext cell
      exact smul_zero _
    rw [coordinatesZero]
    exact zero_memℓp
  add_mem' := by
    intro first second firstMember secondMember grade
    rw [axisCoordinates_add]
    exact (firstMember grade).add (secondMember grade)
  smul_mem' := by
    intro scalar sequence member grade
    rw [axisCoordinates_smul]
    exact (member grade).const_smul scalar

/-- The all-grade axis data core `T^∞` for one planar component. -/
abbrev TCore (parameters : PhaseParameters) := axisCoreSubmodule parameters

/-- The literal `T^q` norm on the all-grade core. -/
def axisGradeNorm (parameters : PhaseParameters) (grade : ℕ)
    (sequence : TCore parameters) : ℝ :=
  ‖(⟨axisCoordinates parameters grade sequence.val, sequence.property grade⟩ :
    lp (fun _ : ℤ => ComplexEuclidean 2) 2)‖

theorem axisGradeNorm_nonneg (parameters : PhaseParameters) (grade : ℕ)
    (sequence : TCore parameters) : 0 ≤ axisGradeNorm parameters grade sequence :=
  norm_nonneg _

theorem axisGradeNorm_add_le (parameters : PhaseParameters) (grade : ℕ)
    (first second : TCore parameters) :
    axisGradeNorm parameters grade (first + second) ≤
      axisGradeNorm parameters grade first + axisGradeNorm parameters grade second := by
  unfold axisGradeNorm
  have packAdd : (⟨axisCoordinates parameters grade (first + second).val,
      (first + second).property grade⟩ : lp (fun _ : ℤ => ComplexEuclidean 2) 2) =
      ⟨axisCoordinates parameters grade first.val, first.property grade⟩ +
        ⟨axisCoordinates parameters grade second.val, second.property grade⟩ := by
    apply Subtype.ext
    change axisCoordinates parameters grade (first.val + second.val) = _
    rw [axisCoordinates_add]
    rfl
  rw [packAdd]
  exact norm_add_le _ _

theorem axisGradeNorm_smul (parameters : PhaseParameters) (grade : ℕ) (scalar : ℂ)
    (sequence : TCore parameters) :
    axisGradeNorm parameters grade (scalar • sequence) =
      ‖scalar‖ * axisGradeNorm parameters grade sequence := by
  unfold axisGradeNorm
  have packSmul : (⟨axisCoordinates parameters grade (scalar • sequence).val,
      (scalar • sequence).property grade⟩ : lp (fun _ : ℤ => ComplexEuclidean 2) 2) =
      scalar • ⟨axisCoordinates parameters grade sequence.val, sequence.property grade⟩ := by
    apply Subtype.ext
    change axisCoordinates parameters grade (scalar • sequence.val) = _
    rw [axisCoordinates_smul]
    rfl
  rw [packSmul]
  exact norm_smul scalar _

/-- Every single weighted coordinate is dominated by the full norm. -/
theorem axisWeight_le_axisGradeNorm (parameters : PhaseParameters) (grade : ℕ)
    (sequence : TCore parameters) (cell : ℤ) :
    axisWeight parameters grade cell * ‖sequence.val cell‖ ≤
      axisGradeNorm parameters grade sequence := by
  have coordinateBound := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (⟨axisCoordinates parameters grade sequence.val, sequence.property grade⟩ :
      lp (fun _ : ℤ => ComplexEuclidean 2) 2) cell
  have coordinateNorm : ‖axisCoordinates parameters grade sequence.val cell‖ =
      axisWeight parameters grade cell * ‖sequence.val cell‖ := by
    unfold axisCoordinates
    rw [norm_smul, Real.norm_of_nonneg (axisWeight_pos parameters grade cell).le]
  rw [← coordinateNorm]
  exact coordinateBound

theorem axisGradeNorm_mono (parameters : PhaseParameters) {lower upper : ℕ}
    (gradeLe : lower ≤ upper) (sequence : TCore parameters) :
    axisGradeNorm parameters lower sequence ≤ axisGradeNorm parameters upper sequence := by
  unfold axisGradeNorm
  apply lp.norm_mono (by norm_num)
  intro cell
  change ‖axisCoordinates parameters lower sequence.val cell‖ ≤
    ‖axisCoordinates parameters upper sequence.val cell‖
  unfold axisCoordinates
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (axisWeight_pos parameters lower cell).le,
    Real.norm_of_nonneg (axisWeight_pos parameters upper cell).le]
  exact mul_le_mul_of_nonneg_right (axisWeight_mono parameters gradeLe cell) (norm_nonneg _)

/-- AL12: the axis data carrier and its literal grade-`q` norm
`|d|_q = ‖sigma‖_{T^{q+1}} + ‖eta‖_{T^{q+1}}`. -/
abbrev AxisData (parameters : PhaseParameters) :=
  TCore parameters × TCore parameters

def axisDataNorm (parameters : PhaseParameters) (grade : ℕ)
    (data : AxisData parameters) : ℝ :=
  axisGradeNorm parameters (grade + 1) data.1 + axisGradeNorm parameters (grade + 1) data.2

theorem axisDataNorm_nonneg (parameters : PhaseParameters) (grade : ℕ)
    (data : AxisData parameters) : 0 ≤ axisDataNorm parameters grade data :=
  add_nonneg (axisGradeNorm_nonneg _ _ _) (axisGradeNorm_nonneg _ _ _)

/-- One weighted coordinate of the cell derivative against the shifted grade. -/
theorem axisDerivative_coordinate_le (parameters : PhaseParameters) (grade : ℕ)
    (sequence : ℤ → ComplexEuclidean 2) (cell : ℤ) :
    ‖axisCoordinates parameters grade
        (fun innerCell => ((innerCell : ℂ) * Complex.I) • sequence innerCell) cell‖ ≤
      ‖axisCoordinates parameters (grade + 1) sequence cell‖ := by
  unfold axisCoordinates
  rw [norm_smul, norm_smul, norm_smul,
    Real.norm_of_nonneg (axisWeight_pos parameters grade cell).le,
    Real.norm_of_nonneg (axisWeight_pos parameters (grade + 1) cell).le]
  have frequencyBound : ‖(cell : ℂ) * Complex.I‖ ≤ cellFrequency cell :=
    timeScalar_norm_bound cell
  have weightShift : axisWeight parameters grade cell * cellFrequency cell =
      axisWeight parameters (grade + 1) cell := by
    unfold axisWeight
    ring
  rw [← weightShift]
  calc axisWeight parameters grade cell *
      (‖(cell : ℂ) * Complex.I‖ * ‖sequence cell‖) ≤
      axisWeight parameters grade cell * (cellFrequency cell * ‖sequence cell‖) := by
        apply mul_le_mul_of_nonneg_left _ (axisWeight_pos parameters grade cell).le
        exact mul_le_mul_of_nonneg_right frequencyBound (norm_nonneg _)
    _ = axisWeight parameters grade cell * cellFrequency cell * ‖sequence cell‖ := by
        ring

/-- The literal cell derivative `i n` on axis sequences. -/
def axisCellDerivative (parameters : PhaseParameters) :
    TCore parameters →ₗ[ℂ] TCore parameters where
  toFun sequence := ⟨fun cell => ((cell : ℂ) * Complex.I) • sequence.val cell, by
    intro grade
    apply (sequence.property (grade + 1)).mono'
    intro cell
    exact axisDerivative_coordinate_le parameters grade sequence.val cell⟩
  map_add' first second := by
    apply Subtype.ext
    funext cell
    exact smul_add _ _ _
  map_smul' scalar sequence := by
    apply Subtype.ext
    funext cell
    exact smul_comm ((cell : ℂ) * Complex.I) scalar (sequence.val cell)

theorem axisCellDerivative_val (parameters : PhaseParameters)
    (sequence : TCore parameters) (cell : ℤ) :
    (axisCellDerivative parameters sequence).val cell =
      ((cell : ℂ) * Complex.I) • sequence.val cell := rfl

/-- The exact constant-one cell-derivative estimate `‖∂_ζ c‖_{T^q} ≤ ‖c‖_{T^{q+1}}`. -/
theorem axisCellDerivative_bound (parameters : PhaseParameters) (grade : ℕ)
    (sequence : TCore parameters) :
    axisGradeNorm parameters grade (axisCellDerivative parameters sequence) ≤
      axisGradeNorm parameters (grade + 1) sequence := by
  unfold axisGradeNorm
  apply lp.norm_mono (by norm_num)
  intro cell
  exact axisDerivative_coordinate_le parameters grade sequence.val cell

end Grad.AxisSplit

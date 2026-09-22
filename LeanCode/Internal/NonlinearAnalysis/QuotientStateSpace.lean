import QuotientLaplacianConsumer
import QuotientTimeDerivative

noncomputable section

open Filter
open scoped BigOperators Topology

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct

/-- The Q4 state `b = (epsilon, v, w)`: the scalar, the three-dimensional
state and the scalar potential, all in the one original coefficient core. -/
abbrev QuotientState (parameters : PhaseParameters) : Type :=
  ℂ × ACore parameters 3 × ACore parameters 1

/-- The four O14 quotient rows in the original scalar coefficient core. -/
abbrev QuotientRows (parameters : PhaseParameters) : Type :=
  Fin 4 → ACore parameters 1

variable {parameters : PhaseParameters}

def stateScalar : QuotientState parameters →ₗ[ℂ] ℂ :=
  LinearMap.fst ℂ ℂ (ACore parameters 3 × ACore parameters 1)

def stateField : QuotientState parameters →ₗ[ℂ] ACore parameters 3 :=
  (LinearMap.fst ℂ (ACore parameters 3) (ACore parameters 1)).comp
    (LinearMap.snd ℂ ℂ (ACore parameters 3 × ACore parameters 1))

def statePotential : QuotientState parameters →ₗ[ℂ] ACore parameters 1 :=
  (LinearMap.snd ℂ (ACore parameters 3) (ACore parameters 1)).comp
    (LinearMap.snd ℂ ℂ (ACore parameters 3 × ACore parameters 1))

@[simp] theorem stateScalar_apply (state : QuotientState parameters) :
    stateScalar state = state.1 := rfl

@[simp] theorem stateField_apply (state : QuotientState parameters) :
    stateField state = state.2.1 := rfl

@[simp] theorem statePotential_apply (state : QuotientState parameters) :
    statePotential state = state.2.2 := rfl

/-- `|epsilon| + ‖v‖_grade + ‖w‖_grade`, the literal Q4 state norm. -/
def stateNorm (grade : ℕ) (state : QuotientState parameters) : ℝ :=
  ‖state.1‖ + originalGradeNorm grade state.2.1 + originalGradeNorm grade state.2.2

theorem stateNorm_nonneg (grade : ℕ) (state : QuotientState parameters) :
    0 ≤ stateNorm grade state :=
  add_nonneg (add_nonneg (norm_nonneg _) (originalGradeNorm_nonnegative _ _))
    (originalGradeNorm_nonnegative _ _)

theorem originalGradeNorm_mono {dimension : ℕ} {lower upper : ℕ} (gradeLe : lower ≤ upper)
    (field : ACore parameters dimension) :
    originalGradeNorm lower field ≤ originalGradeNorm upper field :=
  cartesianGrade_norm_mono parameters gradeLe field

theorem stateNorm_mono {lower upper : ℕ} (gradeLe : lower ≤ upper)
    (state : QuotientState parameters) :
    stateNorm lower state ≤ stateNorm upper state :=
  add_le_add (add_le_add le_rfl (originalGradeNorm_mono gradeLe _))
    (originalGradeNorm_mono gradeLe _)

theorem norm_stateScalar_le (grade : ℕ) (state : QuotientState parameters) :
    ‖stateScalar state‖ ≤ stateNorm grade state := by
  have first := originalGradeNorm_nonnegative grade state.2.1
  have second := originalGradeNorm_nonnegative grade state.2.2
  unfold stateNorm
  rw [stateScalar_apply]
  linarith

theorem originalGradeNorm_stateField_le (grade : ℕ) (state : QuotientState parameters) :
    originalGradeNorm grade (stateField state) ≤ stateNorm grade state := by
  have first := norm_nonneg state.1
  have second := originalGradeNorm_nonnegative grade state.2.2
  unfold stateNorm
  rw [stateField_apply]
  linarith

theorem originalGradeNorm_statePotential_le (grade : ℕ) (state : QuotientState parameters) :
    originalGradeNorm grade (statePotential state) ≤ stateNorm grade state := by
  have first := norm_nonneg state.1
  have second := originalGradeNorm_nonnegative grade state.2.1
  unfold stateNorm
  rw [statePotential_apply]
  linarith

theorem originalGradeNorm_zero {dimension : ℕ} (grade : ℕ) :
    originalGradeNorm grade (0 : ACore parameters dimension) = 0 := by
  unfold originalGradeNorm
  rw [map_zero, norm_zero]

theorem originalGradeNorm_smul {dimension : ℕ} (grade : ℕ) (scalar : ℂ)
    (field : ACore parameters dimension) :
    originalGradeNorm grade (scalar • field) = ‖scalar‖ * originalGradeNorm grade field := by
  unfold originalGradeNorm
  rw [map_smul, gradeCore_norm_eq_cartesianGradeSeminorm,
    gradeCore_norm_eq_cartesianGradeSeminorm, cartesianGradeSeminorm_smul]

theorem originalGradeNorm_sum_le {dimension : ℕ} {Index : Type} (grade : ℕ)
    (indices : Finset Index) (fields : Index → ACore parameters dimension) :
    originalGradeNorm grade (∑ index ∈ indices, fields index) ≤
      ∑ index ∈ indices, originalGradeNorm grade (fields index) := by
  unfold originalGradeNorm
  rw [map_sum]
  exact norm_sum_le _ _

/-- The combined norm of the four rows at one grade. -/
def rowsGradeNorm (grade : ℕ) (rows : QuotientRows parameters) : ℝ :=
  ∑ row, originalGradeNorm grade (rows row)

theorem rowsGradeNorm_nonneg (grade : ℕ) (rows : QuotientRows parameters) :
    0 ≤ rowsGradeNorm grade rows :=
  Finset.sum_nonneg (fun _ _ => originalGradeNorm_nonnegative _ _)

theorem rowsGradeNorm_zero (grade : ℕ) :
    rowsGradeNorm grade (0 : QuotientRows parameters) = 0 := by
  unfold rowsGradeNorm
  simp only [Pi.zero_apply, originalGradeNorm_zero, Finset.sum_const_zero]

theorem rowsGradeNorm_add_le (grade : ℕ) (first second : QuotientRows parameters) :
    rowsGradeNorm grade (first + second) ≤
      rowsGradeNorm grade first + rowsGradeNorm grade second := by
  unfold rowsGradeNorm
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun row _ => originalGradeNorm_add_le grade _ _)

theorem rowsGradeNorm_smul (grade : ℕ) (scalar : ℂ) (rows : QuotientRows parameters) :
    rowsGradeNorm grade (scalar • rows) = ‖scalar‖ * rowsGradeNorm grade rows := by
  unfold rowsGradeNorm
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun row _ => originalGradeNorm_smul grade scalar (rows row))

theorem rowsGradeNorm_sum_le {Index : Type} (grade : ℕ) (indices : Finset Index)
    (rows : Index → QuotientRows parameters) :
    rowsGradeNorm grade (∑ index ∈ indices, rows index) ≤
      ∑ index ∈ indices, rowsGradeNorm grade (rows index) := by
  unfold rowsGradeNorm
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro row _
  simp only [Finset.sum_apply]
  exact originalGradeNorm_sum_le grade indices (fun index => rows index row)

theorem rowsGradeNorm_single (grade : ℕ) (row : Fin 4) (field : ACore parameters 1) :
    rowsGradeNorm grade (Pi.single row field) = originalGradeNorm grade field := by
  unfold rowsGradeNorm
  rw [Finset.sum_eq_single row]
  · rw [Pi.single_eq_same]
  · intro other _ otherNe
    rw [Pi.single_eq_of_ne otherNe, originalGradeNorm_zero]
  · intro absent
    exact absurd (Finset.mem_univ row) absent

/-- Genuine directional differentiability of a rows-valued map along a real
parameter, stated in every original grade norm at once. -/
def IsRowsDirectionalDerivative (mapping : QuotientState parameters → QuotientRows parameters)
    (base direction : QuotientState parameters) (derivative : QuotientRows parameters) : Prop :=
  ∀ grade : ℕ, Tendsto (fun t : ℝ => rowsGradeNorm grade
      (((t : ℂ))⁻¹ • (mapping (base + (t : ℂ) • direction) - mapping base) - derivative))
    (𝓝[≠] (0 : ℝ)) (𝓝 0)

/-- The one derivative lemma used for every order: a map whose shifted values
form a literal polynomial in the real parameter has the degree-one coefficient
as genuine directional derivative, in every grade norm. -/
theorem polynomial_rows_directional (degree : ℕ)
    (coefficients : ℕ → QuotientRows parameters)
    (mapping : QuotientState parameters → QuotientRows parameters)
    (base direction : QuotientState parameters)
    (expansion : ∀ t : ℝ, mapping (base + (t : ℂ) • direction) =
      ∑ j ∈ Finset.range (degree + 2), ((t : ℂ) ^ j) • coefficients j) :
    IsRowsDirectionalDerivative mapping base direction (coefficients 1) := by
  have baseValue : mapping base = coefficients 0 := by
    have zeroShift : base + ((0 : ℝ) : ℂ) • direction = base := by
      rw [Complex.ofReal_zero, zero_smul, add_zero]
    have expanded := expansion 0
    rw [zeroShift] at expanded
    rw [expanded, Finset.sum_eq_single 0]
    · rw [pow_zero, one_smul]
    · intro j _ jPositive
      rw [Complex.ofReal_zero, zero_pow jPositive, zero_smul]
    · intro absent
      exact absurd (Finset.mem_range.mpr (by omega)) absent
  have shifted (t : ℝ) (nonzero : (t : ℂ) ≠ 0) :
      ((t : ℂ))⁻¹ • (mapping (base + (t : ℂ) • direction) - mapping base) - coefficients 1 =
        ∑ j ∈ Finset.range degree, ((t : ℂ) ^ (j + 1)) • coefficients (j + 2) := by
    rw [expansion t, baseValue, Finset.sum_range_succ', Finset.sum_range_succ']
    have firstPower : ((t : ℂ) ^ (0 + 1)) • coefficients (0 + 1) = (t : ℂ) • coefficients 1 := by
      rw [pow_one]
    have zeroPower : ((t : ℂ) ^ 0) • coefficients 0 = coefficients 0 := by
      rw [pow_zero, one_smul]
    rw [firstPower, zeroPower]
    have cancel : ((t : ℂ))⁻¹ • ((∑ j ∈ Finset.range degree,
        ((t : ℂ) ^ (j + 1 + 1)) • coefficients (j + 1 + 1)) + (t : ℂ) • coefficients 1 +
          coefficients 0 - coefficients 0) =
        (∑ j ∈ Finset.range degree, ((t : ℂ) ^ (j + 1)) • coefficients (j + 2)) +
          coefficients 1 := by
      rw [add_sub_cancel_right, smul_add, Finset.smul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro j _
        rw [smul_smul]
        congr 1
        rw [pow_succ']
        rw [← mul_assoc, inv_mul_cancel₀ nonzero, one_mul]
      · rw [smul_smul, inv_mul_cancel₀ nonzero, one_smul]
    rw [cancel, add_sub_cancel_right]
  intro grade
  have majorTendsto : Tendsto (fun t : ℝ => ∑ j ∈ Finset.range degree,
      |t| ^ (j + 1) * rowsGradeNorm grade (coefficients (j + 2))) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have full : Tendsto (fun t : ℝ => ∑ j ∈ Finset.range degree,
        |t| ^ (j + 1) * rowsGradeNorm grade (coefficients (j + 2))) (𝓝 (0 : ℝ)) (𝓝 0) := by
      have value : (∑ j ∈ Finset.range degree,
          |(0 : ℝ)| ^ (j + 1) * rowsGradeNorm grade (coefficients (j + 2))) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [abs_zero, zero_pow (by omega), zero_mul]
      have continuous : Continuous (fun t : ℝ => ∑ j ∈ Finset.range degree,
          |t| ^ (j + 1) * rowsGradeNorm grade (coefficients (j + 2))) := by
        apply continuous_finsetSum
        intro j _
        exact (continuous_abs.pow (j + 1)).mul continuous_const
      exact continuous.tendsto' 0 0 value
    exact full.mono_left nhdsWithin_le_nhds
  apply squeeze_zero' (Filter.Eventually.of_forall (fun t => rowsGradeNorm_nonneg _ _)) _ majorTendsto
  apply eventually_nhdsWithin_of_forall
  intro t membership
  have nonzero : (t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by simpa using membership)
  rw [shifted t nonzero]
  apply (rowsGradeNorm_sum_le grade _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [rowsGradeNorm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs]

end Grad.NonlinearQuotientBounds

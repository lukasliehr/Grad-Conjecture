import QT8Consumer
import COR16Consumer

noncomputable section

namespace Grad.ConstrainedGrades

open Grad.ClosedJets Grad.CartesianState Grad.AxisCore

theorem axisWeight_mono (parameters : PhaseParameters) {lower upper : ℕ}
    (ordered : lower ≤ upper) (cell : ℤ) :
    axisWeight parameters lower cell ≤ axisWeight parameters upper cell := by
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (cellFrequency_one_le cell) ordered) (Real.exp_pos _).le

theorem axisLowering_pointwise {dimension lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (field : AxisGrade parameters dimension upper) (cell : ℤ) :
    ‖(axisWeight parameters lower cell : ℂ) • axisCoefficient parameters upper field cell‖ ≤
      ‖field cell‖ := by
  have factorLe : axisWeight parameters lower cell / axisWeight parameters upper cell ≤ 1 :=
    div_le_one_of_le₀ (axisWeight_mono parameters ordered cell) (axisWeight_pos parameters upper cell).le
  have formula : ‖(axisWeight parameters lower cell : ℂ) • axisCoefficient parameters upper field cell‖ =
      (axisWeight parameters lower cell / axisWeight parameters upper cell) * ‖field cell‖ := by
    unfold axisCoefficient
    rw [norm_smul, norm_smul, norm_inv, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (axisWeight_pos parameters lower cell),
      abs_of_pos (axisWeight_pos parameters upper cell)]
    ring
  rw [formula]
  exact mul_le_of_le_one_left (norm_nonneg _) factorLe

/-- Literal same-coefficient axis inclusion for any ordered grades. -/
def axisLoweringLinear {dimension lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) :
    AxisGrade parameters dimension upper →ₗ[ℂ] AxisGrade parameters dimension lower where
  toFun field := ⟨fun cell => (axisWeight parameters lower cell : ℂ) •
    axisCoefficient parameters upper field cell,
    (lp.memℓp field).mono' (axisLowering_pointwise parameters ordered field)⟩
  map_add' first second := by
    apply lp.ext
    funext cell
    change (axisWeight parameters lower cell : ℂ) •
      (axisWeight parameters upper cell : ℂ)⁻¹ • (first cell + second cell) = _
    rw [smul_add, smul_add]
    rfl
  map_smul' scalar field := by
    apply lp.ext
    funext cell
    change (axisWeight parameters lower cell : ℂ) •
      (axisWeight parameters upper cell : ℂ)⁻¹ • (scalar • field cell) = _
    rw [smul_comm (axisWeight parameters upper cell : ℂ)⁻¹ scalar,
      smul_comm (axisWeight parameters lower cell : ℂ) scalar]
    rfl

theorem axisLoweringLinear_norm_le {dimension lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (field : AxisGrade parameters dimension upper) :
    ‖axisLoweringLinear parameters ordered field‖ ≤ ‖field‖ :=
  lp.norm_mono (p := 2) (by norm_num) (axisLowering_pointwise parameters ordered field)

def axisLowering {dimension lower upper : ℕ} (parameters : PhaseParameters) (ordered : lower ≤ upper) :
    AxisGrade parameters dimension upper →L[ℂ] AxisGrade parameters dimension lower :=
  (axisLoweringLinear parameters ordered).mkContinuous 1
    (fun field => by simpa only [one_mul] using axisLoweringLinear_norm_le parameters ordered field)

theorem axisLowering_norm_le {dimension lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (field : AxisGrade parameters dimension upper) :
    ‖axisLowering parameters ordered field‖ ≤ ‖field‖ :=
  axisLoweringLinear_norm_le parameters ordered field

theorem axisLowering_coefficient {dimension lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (field : AxisGrade parameters dimension upper) (cell : ℤ) :
    axisCoefficient parameters lower (axisLowering parameters ordered field) cell =
      axisCoefficient parameters upper field cell := by
  change (axisWeight parameters lower cell : ℂ)⁻¹ •
    (axisWeight parameters lower cell : ℂ) • axisCoefficient parameters upper field cell = _
  rw [inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (axisWeight_pos parameters lower cell).ne')]

theorem axisCoefficient_ext {dimension grade : ℕ} (parameters : PhaseParameters)
    {first second : AxisGrade parameters dimension grade}
    (equal : ∀ cell, axisCoefficient parameters grade first cell = axisCoefficient parameters grade second cell) :
    first = second := by
  apply lp.ext
  funext cell
  rw [← axis_weighted_coefficient parameters grade first cell,
    ← axis_weighted_coefficient parameters grade second cell, equal cell]

theorem axisLowering_injective {dimension lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) : Function.Injective (axisLowering (dimension := dimension) parameters ordered) := by
  intro first second equal
  apply axisCoefficient_ext parameters
  intro cell
  rw [← axisLowering_coefficient parameters ordered first cell,
    ← axisLowering_coefficient parameters ordered second cell, equal]

theorem axisLowering_core {dimension lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper)
    (field : Grad.SmoothingFamily.AxisCore parameters.sigma0 (ComplexEuclidean dimension)) :
    axisLowering parameters ordered (Grad.SmoothingFamily.axisToGrade parameters.sigma0 upper field) =
      Grad.SmoothingFamily.axisToGrade parameters.sigma0 lower field := by
  apply lp.ext
  funext cell
  change (axisWeight parameters lower cell : ℂ) •
    (axisWeight parameters upper cell : ℂ)⁻¹ • (axisWeight parameters upper cell : ℂ) • field.val cell = _
  rw [inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (axisWeight_pos parameters upper cell).ne')]
  rfl

theorem axisLowering_self {dimension grade : ℕ} (parameters : PhaseParameters)
    (field : AxisGrade parameters dimension grade) : axisLowering parameters (le_refl grade) field = field := by
  apply axisCoefficient_ext parameters
  exact axisLowering_coefficient parameters (le_refl grade) field

theorem axisLowering_trans {dimension lower middle upper : ℕ} (parameters : PhaseParameters)
    (first : lower ≤ middle) (second : middle ≤ upper) (field : AxisGrade parameters dimension upper) :
    axisLowering parameters first (axisLowering parameters second field) =
      axisLowering parameters (first.trans second) field := by
  apply axisCoefficient_ext parameters
  intro cell
  rw [axisLowering_coefficient, axisLowering_coefficient, axisLowering_coefficient]

end Grad.ConstrainedGrades

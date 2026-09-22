import AX1AxisGrade

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.AxisCore

open Grad.ClosedJets Grad.CartesianState

variable (parameters : PhaseParameters) (valueDimension : ℕ)

/-- The all-grade axis smooth core: one coefficient family with every M16
sum finite. -/
def axisCoreSubmodule : Submodule ℂ (ℤ → ComplexEuclidean valueDimension) where
  carrier := {family | ∀ grade : ℕ,
    Summable (fun cell => axisWeight parameters grade cell ^ 2 * ‖family cell‖ ^ 2)}
  zero_mem' := by
    intro grade
    simp
  add_mem' := by
    intro first second firstMember secondMember grade
    apply Summable.of_nonneg_of_le
      (fun cell => mul_nonneg (sq_nonneg _) (sq_nonneg _)) (fun cell => ?_)
      (((firstMember grade).mul_left 2).add ((secondMember grade).mul_left 2))
    have applyAdd : (first + second) cell = first cell + second cell := rfl
    rw [applyAdd]
    have triangle : ‖first cell + second cell‖ ^ 2 ≤
        2 * ‖first cell‖ ^ 2 + 2 * ‖second cell‖ ^ 2 := by
      have expand := norm_add_le (first cell) (second cell)
      have square := pow_le_pow_left₀ (norm_nonneg _) expand 2
      nlinarith [sq_nonneg (‖first cell‖ - ‖second cell‖), norm_nonneg (first cell),
        norm_nonneg (second cell)]
    have weightNonneg := sq_nonneg (axisWeight parameters grade cell)
    calc axisWeight parameters grade cell ^ 2 * ‖first cell + second cell‖ ^ 2
        ≤ axisWeight parameters grade cell ^ 2 *
            (2 * ‖first cell‖ ^ 2 + 2 * ‖second cell‖ ^ 2) :=
          mul_le_mul_of_nonneg_left triangle weightNonneg
      _ = 2 * (axisWeight parameters grade cell ^ 2 * ‖first cell‖ ^ 2) +
            2 * (axisWeight parameters grade cell ^ 2 * ‖second cell‖ ^ 2) := by ring
  smul_mem' := by
    intro scalar family familyMember grade
    have rewrite : (fun cell => axisWeight parameters grade cell ^ 2 *
        ‖(scalar • family) cell‖ ^ 2) =
        fun cell => ‖scalar‖ ^ 2 *
          (axisWeight parameters grade cell ^ 2 * ‖family cell‖ ^ 2) := by
      funext cell
      simp only [Pi.smul_apply, norm_smul]
      ring
    rw [rewrite]
    exact (familyMember grade).mul_left _

/-- The all-grade axis core as a carrier type. -/
abbrev AxisSmoothCore := ↥(axisCoreSubmodule parameters valueDimension)

/-- The same-coefficient embedding of the axis core into each M16 grade. -/
def axisEta (grade : ℕ) : AxisSmoothCore parameters valueDimension →ₗ[ℂ]
    AxisGrade parameters valueDimension grade where
  toFun family := ⟨fun cell => (axisWeight parameters grade cell : ℂ) • family.1 cell, by
    show Memℓp _ 2
    rw [memlp_iff_summable_sq]
    apply ((family.2 grade).congr)
    intro cell
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (axisWeight_pos parameters grade cell), mul_pow]⟩
  map_add' first second := by
    apply lp.ext
    funext cell
    change (axisWeight parameters grade cell : ℂ) • (first.1 cell + second.1 cell) = _
    rw [smul_add]
    rfl
  map_smul' scalar family := by
    apply lp.ext
    funext cell
    change (axisWeight parameters grade cell : ℂ) • (scalar • family.1 cell) = _
    rw [smul_comm]
    rfl

theorem axisEta_apply (grade : ℕ) (family : AxisSmoothCore parameters valueDimension) (cell : ℤ) :
    axisEta parameters valueDimension grade family cell =
      (axisWeight parameters grade cell : ℂ) • family.1 cell := rfl

theorem axisEta_coefficient (grade : ℕ) (family : AxisSmoothCore parameters valueDimension)
    (cell : ℤ) :
    axisCoefficient parameters grade (axisEta parameters valueDimension grade family) cell =
      family.1 cell := by
  unfold axisCoefficient
  rw [axisEta_apply]
  exact inv_smul_smul₀
    (Complex.ofReal_ne_zero.mpr (axisWeight_pos parameters grade cell).ne') _

theorem axisEta_injective (grade : ℕ)
    (first second : AxisSmoothCore parameters valueDimension)
    (equal : axisEta parameters valueDimension grade first =
      axisEta parameters valueDimension grade second) : first = second := by
  apply Subtype.ext
  funext cell
  rw [← axisEta_coefficient parameters valueDimension grade first cell,
    ← axisEta_coefficient parameters valueDimension grade second cell, equal]

/-- The exact M16 norm of the embedded core element. -/
theorem axisEta_norm_sq (grade : ℕ) (family : AxisSmoothCore parameters valueDimension) :
    ‖axisEta parameters valueDimension grade family‖ ^ 2 =
      ∑' cell : ℤ, axisWeight parameters grade cell ^ 2 * ‖family.1 cell‖ ^ 2 := by
  have normFormula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    (axisEta parameters valueDimension grade family)
  norm_num at normFormula
  rw [normFormula]
  congr 1
  funext cell
  rw [axisEta_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (axisWeight_pos parameters grade cell), mul_pow]

/-- The literal same-coefficient inclusion of grade `q+1` into grade `q`. -/
def axisInclusion (grade : ℕ) :
    AxisGrade parameters valueDimension (grade + 1) →ₗ[ℂ]
      AxisGrade parameters valueDimension grade where
  toFun field := ⟨fun cell => (axisWeight parameters grade cell : ℂ) •
      axisCoefficient parameters (grade + 1) field cell, by
    show Memℓp _ 2
    rw [memlp_iff_summable_sq]
    have fieldSummable : Summable (fun cell => ‖field cell‖ ^ 2) :=
      (memlp_iff_summable_sq _).mp (lp.memℓp field)
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun cell => ?_) fieldSummable
    have coefficientNorm : ‖(axisWeight parameters grade cell : ℂ) •
        axisCoefficient parameters (grade + 1) field cell‖ =
        axisWeight parameters grade cell / axisWeight parameters (grade + 1) cell *
          ‖field cell‖ := by
      unfold axisCoefficient
      rw [norm_smul, norm_smul, Complex.norm_real, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (axisWeight_pos parameters grade cell),
        abs_of_pos (axisWeight_pos parameters (grade + 1) cell)]
      ring
    rw [coefficientNorm]
    have ratioLe : axisWeight parameters grade cell /
        axisWeight parameters (grade + 1) cell ≤ 1 :=
      div_le_one_of_le₀ (axisWeight_grade_le parameters grade cell)
        (axisWeight_pos parameters (grade + 1) cell).le
    have ratioNonneg : 0 ≤ axisWeight parameters grade cell /
        axisWeight parameters (grade + 1) cell :=
      div_nonneg (axisWeight_pos parameters grade cell).le
        (axisWeight_pos parameters (grade + 1) cell).le
    have normNonneg := norm_nonneg (field cell)
    have ratioSqLe : (axisWeight parameters grade cell /
        axisWeight parameters (grade + 1) cell) ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right ratioSqLe (sq_nonneg ‖field cell‖)]⟩
  map_add' first second := by
    apply lp.ext
    funext cell
    change (axisWeight parameters grade cell : ℂ) •
        ((axisWeight parameters (grade + 1) cell : ℂ))⁻¹ • (first + second) cell = _
    rw [lp.coeFn_add, Pi.add_apply, smul_add, smul_add]
    rfl
  map_smul' scalar field := by
    apply lp.ext
    funext cell
    show (axisWeight parameters grade cell : ℂ) •
        ((axisWeight parameters (grade + 1) cell : ℂ))⁻¹ • (scalar • field) cell =
      scalar • (axisWeight parameters grade cell : ℂ) •
        ((axisWeight parameters (grade + 1) cell : ℂ))⁻¹ • field cell
    rw [lp.coeFn_smul, Pi.smul_apply,
      smul_comm ((axisWeight parameters (grade + 1) cell : ℂ))⁻¹ scalar,
      smul_comm (axisWeight parameters grade cell : ℂ) scalar]

theorem axisInclusion_coefficient (grade : ℕ)
    (field : AxisGrade parameters valueDimension (grade + 1)) (cell : ℤ) :
    axisCoefficient parameters grade
        (axisInclusion parameters valueDimension grade field) cell =
      axisCoefficient parameters (grade + 1) field cell := by
  unfold axisCoefficient
  change ((axisWeight parameters grade cell : ℂ))⁻¹ •
    (axisWeight parameters grade cell : ℂ) •
      ((axisWeight parameters (grade + 1) cell : ℂ))⁻¹ • field cell = _
  rw [inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (axisWeight_pos parameters grade cell).ne')]

theorem axisInclusion_injective (grade : ℕ)
    (first second : AxisGrade parameters valueDimension (grade + 1))
    (equal : axisInclusion parameters valueDimension grade first =
      axisInclusion parameters valueDimension grade second) : first = second := by
  apply lp.ext
  funext cell
  rw [← axis_weighted_coefficient parameters (grade + 1) first cell,
    ← axis_weighted_coefficient parameters (grade + 1) second cell,
    ← axisInclusion_coefficient parameters valueDimension grade first cell,
    ← axisInclusion_coefficient parameters valueDimension grade second cell, equal]

/-- The inclusion is contractive for the exact M16 norms. -/
theorem axisInclusion_contractive (grade : ℕ)
    (field : AxisGrade parameters valueDimension (grade + 1)) :
    ‖axisInclusion parameters valueDimension grade field‖ ≤ ‖field‖ := by
  have includedFormula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    (axisInclusion parameters valueDimension grade field)
  have fieldFormula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at includedFormula fieldFormula
  have termBound (cell : ℤ) :
      ‖axisInclusion parameters valueDimension grade field cell‖ ^ 2 ≤
        ‖field cell‖ ^ 2 := by
    change ‖(axisWeight parameters grade cell : ℂ) •
      axisCoefficient parameters (grade + 1) field cell‖ ^ 2 ≤ _
    have coefficientNorm : ‖(axisWeight parameters grade cell : ℂ) •
        axisCoefficient parameters (grade + 1) field cell‖ =
        axisWeight parameters grade cell / axisWeight parameters (grade + 1) cell *
          ‖field cell‖ := by
      unfold axisCoefficient
      rw [norm_smul, norm_smul, Complex.norm_real, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (axisWeight_pos parameters grade cell),
        abs_of_pos (axisWeight_pos parameters (grade + 1) cell)]
      ring
    rw [coefficientNorm]
    have ratioLe : axisWeight parameters grade cell /
        axisWeight parameters (grade + 1) cell ≤ 1 :=
      div_le_one_of_le₀ (axisWeight_grade_le parameters grade cell)
        (axisWeight_pos parameters (grade + 1) cell).le
    have ratioNonneg : 0 ≤ axisWeight parameters grade cell /
        axisWeight parameters (grade + 1) cell :=
      div_nonneg (axisWeight_pos parameters grade cell).le
        (axisWeight_pos parameters (grade + 1) cell).le
    have normNonneg := norm_nonneg (field cell)
    have ratioSqLe : (axisWeight parameters grade cell /
        axisWeight parameters (grade + 1) cell) ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right ratioSqLe (sq_nonneg ‖field cell‖)]
  have sumBound : (∑' cell : ℤ,
      ‖axisInclusion parameters valueDimension grade field cell‖ ^ 2) ≤
      ∑' cell : ℤ, ‖field cell‖ ^ 2 :=
    Summable.tsum_le_tsum termBound
      ((memlp_iff_summable_sq _).mp (lp.memℓp _))
      ((memlp_iff_summable_sq _).mp (lp.memℓp field))
  calc ‖axisInclusion parameters valueDimension grade field‖
      = Real.sqrt (‖axisInclusion parameters valueDimension grade field‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖field‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [includedFormula, fieldFormula]
        exact sumBound
    _ = ‖field‖ := Real.sqrt_sq (norm_nonneg _)

end Grad.AxisCore

import AxisJetRowBounds

noncomputable section

open scoped BigOperators ContDiff

namespace Grad.AxisJet

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.AxisSplit

variable {parameters : PhaseParameters}

/-! ### The axis-weight shift identities -/

theorem axisWeight_shift_one (parameters : PhaseParameters) (grade : ℕ) (cell : ℤ) :
    axisWeight parameters (grade + 1) cell * (cellFrequency cell)⁻¹ =
      axisWeight parameters grade cell := by
  show Real.exp (parameters.sigma0 * cellFrequency cell) *
      cellFrequency cell ^ (grade + 1) * (cellFrequency cell)⁻¹ =
    Real.exp (parameters.sigma0 * cellFrequency cell) * cellFrequency cell ^ grade
  rw [pow_succ, show Real.exp (parameters.sigma0 * cellFrequency cell) *
      (cellFrequency cell ^ grade * cellFrequency cell) * (cellFrequency cell)⁻¹ =
    Real.exp (parameters.sigma0 * cellFrequency cell) * cellFrequency cell ^ grade *
      (cellFrequency cell * (cellFrequency cell)⁻¹) from by ring,
    mul_inv_cancel₀ (cellFrequency_pos cell).ne', mul_one]

theorem axisWeight_shift_two (parameters : PhaseParameters) (grade : ℕ) (cell : ℤ) :
    axisWeight parameters (grade + 2) cell *
        ((cellFrequency cell)⁻¹ * (cellFrequency cell)⁻¹) =
      axisWeight parameters grade cell := by
  rw [show grade + 2 = grade + 1 + 1 from rfl]
  calc axisWeight parameters (grade + 1 + 1) cell *
      ((cellFrequency cell)⁻¹ * (cellFrequency cell)⁻¹) =
      axisWeight parameters (grade + 1 + 1) cell * (cellFrequency cell)⁻¹ *
        (cellFrequency cell)⁻¹ := by ring
    _ = axisWeight parameters (grade + 1) cell * (cellFrequency cell)⁻¹ := by
        rw [axisWeight_shift_one parameters (grade + 1) cell]
    _ = axisWeight parameters grade cell := axisWeight_shift_one parameters grade cell

/-! ### M28's `E0`: the literal scaled value-profile insertion -/

/-- The raw value-profile insertion `cell ↦ φ(λ_cell ·) a_cell`. -/
def insertZeroCoefficients {dimension : ℕ}
    (family : Grad.AxisCore.AxisSmoothCore parameters dimension) :
    ℤ → ClosedJet dimension :=
  fun cell => profileJetZero cell (family.val cell)

/-- The weighted coordinate family of an accepted axis-core element is
square summable at every grade. -/
theorem weighted_family_memlp {dimension : ℕ}
    (family : Grad.AxisCore.AxisSmoothCore parameters dimension) (grade : ℕ) :
    Memℓp (fun cell => axisWeight parameters grade cell * ‖family.val cell‖) 2 := by
  rw [memlp_iff_summable_sq]
  apply (family.2 grade).congr
  intro cell
  show Grad.AxisCore.axisWeight parameters grade cell ^ 2 * ‖family.val cell‖ ^ 2 =
    ‖axisWeight parameters grade cell * ‖family.val cell‖‖ ^ 2
  rw [axisCoreWeight_eq, Real.norm_of_nonneg
    (mul_nonneg (axisWeight_pos parameters grade cell).le (norm_nonneg _)), mul_pow]

theorem insertZero_mem {dimension : ℕ}
    (family : Grad.AxisCore.AxisSmoothCore parameters dimension) :
    insertZeroCoefficients family ∈ originalCoreSubmodule parameters dimension := by
  intro grade
  obtain ⟨bound, boundNonneg, rowBound⟩ := profileZero_row_bound parameters grade
  apply ((weighted_family_memlp family grade).const_smul (bound : ℝ)).mono'
  intro cell
  change ‖cellGradeRowLinear (grade := grade) parameters cell
    (profileJetZero cell (family.val cell))‖ ≤ _
  have rowEstimate := rowBound cell dimension (family.val cell)
  have relax : bound * (axisWeight parameters grade cell *
      (cellFrequency cell)⁻¹ * ‖family.val cell‖) ≤
      bound * (axisWeight parameters grade cell * ‖family.val cell‖) := by
    apply mul_le_mul_of_nonneg_left _ boundNonneg
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc axisWeight parameters grade cell * (cellFrequency cell)⁻¹ ≤
        axisWeight parameters grade cell * 1 := by
          apply mul_le_mul_of_nonneg_left _ (axisWeight_pos parameters grade cell).le
          exact inv_le_one_of_one_le₀ (cellFrequency_one_le cell)
      _ = axisWeight parameters grade cell := mul_one _
  apply le_trans (rowEstimate.trans relax)
  apply le_of_eq
  rw [Pi.smul_apply, smul_eq_mul, Real.norm_of_nonneg (mul_nonneg boundNonneg
    (mul_nonneg (axisWeight_pos parameters grade cell).le (norm_nonneg _)))]

/-- M28's `E0`, linear from the accepted axis core into the state core. -/
def insertZero {dimension : ℕ} :
    Grad.AxisCore.AxisSmoothCore parameters dimension →ₗ[ℂ]
      ACore parameters dimension where
  toFun family := ⟨insertZeroCoefficients family, insertZero_mem family⟩
  map_add' first second := by
    apply Subtype.ext
    funext cell
    change profileJetZero cell ((first.val + second.val) cell) = _
    rw [Pi.add_apply, profileJetZero_add]
    rfl
  map_smul' scalar family := by
    apply Subtype.ext
    funext cell
    change profileJetZero cell ((scalar • family.val) cell) = _
    rw [Pi.smul_apply, profileJetZero_smul]
    rfl

theorem insertZero_val {dimension : ℕ}
    (family : Grad.AxisCore.AxisSmoothCore parameters dimension) (cell : ℤ) :
    (insertZero family).val cell = profileJetZero cell (family.val cell) := rfl

/-! ### M28's `E_i`: the literal scaled coordinate-profile insertions -/

/-- The raw coordinate-profile insertion `cell ↦ y_i φ(λ_cell ·) a_cell`. -/
def insertOneCoefficients {dimension : ℕ} (coordinate : Fin 2)
    (family : Grad.AxisCore.AxisSmoothCore parameters dimension) :
    ℤ → ClosedJet dimension :=
  fun cell => profileJetOne coordinate cell (family.val cell)

theorem insertOne_mem {dimension : ℕ} (coordinate : Fin 2)
    (family : Grad.AxisCore.AxisSmoothCore parameters dimension) :
    insertOneCoefficients coordinate family ∈
      originalCoreSubmodule parameters dimension := by
  intro grade
  obtain ⟨bound, boundNonneg, rowBound⟩ :=
    profileOne_row_bound parameters coordinate grade
  apply ((weighted_family_memlp family grade).const_smul (bound : ℝ)).mono'
  intro cell
  change ‖cellGradeRowLinear (grade := grade) parameters cell
    (profileJetOne coordinate cell (family.val cell))‖ ≤ _
  have rowEstimate := rowBound cell dimension (family.val cell)
  have inverseLe : (cellFrequency cell)⁻¹ * (cellFrequency cell)⁻¹ ≤ 1 := by
    have singleLe : (cellFrequency cell)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (cellFrequency_one_le cell)
    have singleNonneg : (0 : ℝ) ≤ (cellFrequency cell)⁻¹ :=
      inv_nonneg.mpr (cellFrequency_pos cell).le
    calc (cellFrequency cell)⁻¹ * (cellFrequency cell)⁻¹ ≤ 1 * 1 :=
        mul_le_mul singleLe singleLe singleNonneg zero_le_one
      _ = 1 := mul_one _
  have relax : bound * (axisWeight parameters grade cell *
      ((cellFrequency cell)⁻¹ * (cellFrequency cell)⁻¹) * ‖family.val cell‖) ≤
      bound * (axisWeight parameters grade cell * ‖family.val cell‖) := by
    apply mul_le_mul_of_nonneg_left _ boundNonneg
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc axisWeight parameters grade cell *
        ((cellFrequency cell)⁻¹ * (cellFrequency cell)⁻¹) ≤
        axisWeight parameters grade cell * 1 :=
          mul_le_mul_of_nonneg_left inverseLe (axisWeight_pos parameters grade cell).le
      _ = axisWeight parameters grade cell := mul_one _
  apply le_trans (rowEstimate.trans relax)
  apply le_of_eq
  rw [Pi.smul_apply, smul_eq_mul, Real.norm_of_nonneg (mul_nonneg boundNonneg
    (mul_nonneg (axisWeight_pos parameters grade cell).le (norm_nonneg _)))]

/-- M28's `E_i`, linear from the accepted axis core into the state core. -/
def insertOne {dimension : ℕ} (coordinate : Fin 2) :
    Grad.AxisCore.AxisSmoothCore parameters dimension →ₗ[ℂ]
      ACore parameters dimension where
  toFun family := ⟨insertOneCoefficients coordinate family,
    insertOne_mem coordinate family⟩
  map_add' first second := by
    apply Subtype.ext
    funext cell
    change profileJetOne coordinate cell ((first.val + second.val) cell) = _
    rw [Pi.add_apply, profileJetOne_add]
    rfl
  map_smul' scalar family := by
    apply Subtype.ext
    funext cell
    change profileJetOne coordinate cell ((scalar • family.val) cell) = _
    rw [Pi.smul_apply, profileJetOne_smul]
    rfl

theorem insertOne_val {dimension : ℕ} (coordinate : Fin 2)
    (family : Grad.AxisCore.AxisSmoothCore parameters dimension) (cell : ℤ) :
    (insertOne coordinate family).val cell =
      profileJetOne coordinate cell (family.val cell) := rfl

/-! ### M30: the literal profile bounds -/

/-- M30's first bound: `‖E0 a‖_{A^{q+1}} ≤ C ‖a‖_{T^q}`, the literal
`E0 : T^{s-1} → A^s` boundedness for every `s = q + 1 ≥ 1`. -/
theorem insertZero_bound {dimension : ℕ} (grade : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      ∀ family : Grad.AxisCore.AxisSmoothCore parameters dimension,
      originalGradeNorm (grade + 1) (insertZero family) ≤
        bound * ‖Grad.AxisCore.axisEta parameters dimension grade family‖ := by
  obtain ⟨rowConstant, rowNonneg, rowBound⟩ :=
    profileZero_row_bound parameters (grade + 1)
  refine ⟨rowConstant, rowNonneg, ?_⟩
  intro family
  apply originalGradeNorm_le_of_axis_row (insertZero family) (grade + 1)
    rowConstant rowNonneg family grade
  intro cell
  have rowEstimate := rowBound cell dimension (family.val cell)
  apply le_trans rowEstimate
  apply le_of_eq
  rw [axisWeight_shift_one]

/-- M30's second bound: `‖E_i a‖_{A^{q+2}} ≤ C ‖a‖_{T^q}`, the literal
`E_i : T^{s-2} → A^s` boundedness for every `s = q + 2 ≥ 2`. -/
theorem insertOne_bound {dimension : ℕ} (coordinate : Fin 2) (grade : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      ∀ family : Grad.AxisCore.AxisSmoothCore parameters dimension,
      originalGradeNorm (grade + 2) (insertOne coordinate family) ≤
        bound * ‖Grad.AxisCore.axisEta parameters dimension grade family‖ := by
  obtain ⟨rowConstant, rowNonneg, rowBound⟩ :=
    profileOne_row_bound parameters coordinate (grade + 2)
  refine ⟨rowConstant, rowNonneg, ?_⟩
  intro family
  apply originalGradeNorm_le_of_axis_row (insertOne coordinate family) (grade + 2)
    rowConstant rowNonneg family grade
  intro cell
  have rowEstimate := rowBound cell dimension (family.val cell)
  apply le_trans rowEstimate
  apply le_of_eq
  rw [axisWeight_shift_two]

end Grad.AxisJet

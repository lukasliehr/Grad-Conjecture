import CellWeightsInterface

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue Cells FieldL2 cellProjection fieldCellProjection)
open scoped Topology BigOperators

namespace Grad.CellWeights

theorem cellWeight_one_le (cell : ℤ) : 1 ≤ cellWeight cell := by
  have bound : (1 : ℝ) ≤ 1 + (cell : ℝ) ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
  simpa only [cellWeight, Real.sqrt_one] using Real.sqrt_le_sqrt bound

theorem cellWeight_pos (cell : ℤ) : 0 < cellWeight cell := lt_of_lt_of_le zero_lt_one (cellWeight_one_le cell)

theorem inverseFactor_norm_le (order : ℕ) (cell : ℤ) : ‖inverseFactor order cell‖ ≤ 1 := by
  rw [inverseFactor, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (cellWeight_pos cell).le]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (cellWeight_one_le cell))

theorem inverseFactor_ne_zero (order : ℕ) (cell : ℤ) : inverseFactor order cell ≠ 0 :=
  inv_ne_zero (pow_ne_zero order (Complex.ofReal_ne_zero.mpr (cellWeight_pos cell).ne'))

theorem inverseFactor_zero (cell : ℤ) : inverseFactor 0 cell = 1 := by simp [inverseFactor]

theorem inverseFactor_mul (first second : ℕ) (cell : ℤ) :
    inverseFactor first cell * inverseFactor second cell = inverseFactor (first + second) cell := by
  simp only [inverseFactor, pow_add, mul_inv_rev, mul_comm]

section Cells

variable (Value : Type*) [NormedAddCommGroup Value] [NormedSpace ℂ Value]

theorem cellProjection_norm_le (cell : ℤ) : ‖cellProjection Value cell‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro cells
  change ‖cells cell‖ ≤ 1 * ‖cells‖
  simpa only [one_mul] using lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) cells cell

theorem cells_ext {first second : Cells Value}
    (equality : ∀ cell, cellProjection Value cell first = cellProjection Value cell second) : first = second :=
  lp.ext (funext equality)

theorem inverse_coordinate_norm (order : ℕ) (cell : ℤ) (value : Value) :
    ‖inverseFactor order cell • value‖ ≤ ‖value‖ := by
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_right (inverseFactor_norm_le order cell) (norm_nonneg value)).trans_eq (one_mul _)

def inverseCells (order : ℕ) (cells : Cells Value) : Cells Value :=
  ⟨fun cell => inverseFactor order cell • cells cell,
    (lp.memℓp cells).mono' (fun cell => inverse_coordinate_norm Value order cell (cells cell))⟩

theorem inverseCells_norm (order : ℕ) (cells : Cells Value) : ‖inverseCells Value order cells‖ ≤ ‖cells‖ :=
  lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
    (fun cell => inverse_coordinate_norm Value order cell (cells cell))

def inverseLinear (order : ℕ) : Cells Value →ₗ[ℂ] Cells Value where
  toFun := inverseCells Value order
  map_add' first second := by
    apply lp.ext
    funext cell
    exact smul_add (inverseFactor order cell) (first cell) (second cell)
  map_smul' scalar cells := by
    apply lp.ext
    funext cell
    exact smul_comm (inverseFactor order cell) scalar (cells cell)

def inverseCellCLM (order : ℕ) : Cells Value →L[ℂ] Cells Value :=
  (inverseLinear Value order).mkContinuous 1 (fun cells => by
    change ‖inverseCells Value order cells‖ ≤ 1 * ‖cells‖
    simpa only [one_mul] using inverseCells_norm Value order cells)

theorem inverseCellCLM_apply (order : ℕ) (cells : Cells Value) (cell : ℤ) :
    inverseCellCLM Value order cells cell = inverseFactor order cell • cells cell := rfl

theorem inverseCellCLM_norm_le (order : ℕ) : ‖inverseCellCLM Value order‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun cells => by
    change ‖inverseCells Value order cells‖ ≤ 1 * ‖cells‖
    simpa only [one_mul] using inverseCells_norm Value order cells)

theorem inverseCellCLM_injective (order : ℕ) : Function.Injective (inverseCellCLM Value order) := by
  intro first second equality
  apply lp.ext
  funext cell
  have coordinate := congrArg (fun cells : Cells Value => cells cell) equality
  change inverseFactor order cell • first cell = inverseFactor order cell • second cell at coordinate
  have cancelled := congrArg (fun value : Value => (inverseFactor order cell)⁻¹ • value) coordinate
  simpa only [smul_smul, inv_mul_cancel₀ (inverseFactor_ne_zero order cell), one_smul] using cancelled

theorem inverseCellCLM_zero : inverseCellCLM Value 0 = ContinuousLinearMap.id ℂ (Cells Value) := by
  apply ContinuousLinearMap.ext
  intro cells
  apply lp.ext
  funext cell
  simp only [inverseCellCLM_apply, inverseFactor_zero, one_smul, ContinuousLinearMap.id_apply]

theorem inverseCellCLM_comp (first second : ℕ) :
    (inverseCellCLM Value first).comp (inverseCellCLM Value second) = inverseCellCLM Value (first + second) := by
  apply ContinuousLinearMap.ext
  intro cells
  apply lp.ext
  funext cell
  change inverseFactor first cell • (inverseFactor second cell • cells cell) =
    inverseFactor (first + second) cell • cells cell
  rw [smul_smul, inverseFactor_mul]

end Cells

section Fields

variable (dimension : ℕ) (domain : Set Spatial)

theorem fieldCellProjection_norm_le (cell : ℤ) : ‖fieldCellProjection dimension domain cell‖ ≤ 1 :=
  (ContinuousLinearMap.norm_compLpL_le (p := 2) (μ := volume.restrict domain)
    (cellProjection (PhysicalValue dimension) cell)).trans (cellProjection_norm_le (PhysicalValue dimension) cell)

theorem fields_ext {first second : FieldL2 dimension domain}
    (equality : ∀ cell, fieldCellProjection dimension domain cell first =
      fieldCellProjection dimension domain cell second) : first = second := by
  apply Lp.ext
  filter_upwards [Grad.GenericCarriers.fieldCellProjection_ae dimension domain first,
    Grad.GenericCarriers.fieldCellProjection_ae dimension domain second] with point firstCoordinates secondCoordinates
  apply lp.ext
  funext cell
  rw [← firstCoordinates cell, equality cell, secondCoordinates cell]

def inverseFieldCLM (order : ℕ) : FieldL2 dimension domain →L[ℂ] FieldL2 dimension domain :=
  (inverseCellCLM (PhysicalValue dimension) order).compLpL 2 (volume.restrict domain)

theorem inverseFieldCLM_ae (order : ℕ) (field : FieldL2 dimension domain) :
    inverseFieldCLM dimension domain order field =ᵐ[volume.restrict domain]
      fun point => inverseCellCLM (PhysicalValue dimension) order (field point) :=
  (inverseCellCLM (PhysicalValue dimension) order).coeFn_compLpL field

theorem inverseFieldCLM_coordinate (order : ℕ) (field : FieldL2 dimension domain) :
    ∀ᵐ point ∂volume.restrict domain, ∀ cell,
      inverseFieldCLM dimension domain order field point cell = inverseFactor order cell • field point cell := by
  filter_upwards [inverseFieldCLM_ae dimension domain order field] with point literal
  intro cell
  rw [literal, inverseCellCLM_apply]

theorem inverseFieldCLM_norm_le (order : ℕ) : ‖inverseFieldCLM dimension domain order‖ ≤ 1 :=
  (ContinuousLinearMap.norm_compLpL_le (p := 2) (μ := volume.restrict domain)
    (inverseCellCLM (PhysicalValue dimension) order)).trans (inverseCellCLM_norm_le (PhysicalValue dimension) order)

theorem inverseFieldCLM_injective (order : ℕ) : Function.Injective (inverseFieldCLM dimension domain order) := by
  intro first second equality
  apply Lp.ext
  filter_upwards [inverseFieldCLM_ae dimension domain order first,
    inverseFieldCLM_ae dimension domain order second] with point firstLiteral secondLiteral
  apply inverseCellCLM_injective (PhysicalValue dimension) order
  rw [← firstLiteral, equality, secondLiteral]

theorem inverseFieldCLM_zero : inverseFieldCLM dimension domain 0 = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro field
  apply Lp.ext
  filter_upwards [inverseFieldCLM_ae dimension domain 0 field] with point literal
  simpa only [inverseCellCLM_zero, ContinuousLinearMap.id_apply] using literal

theorem inverseFieldCLM_comp (first second : ℕ) :
    (inverseFieldCLM dimension domain first).comp (inverseFieldCLM dimension domain second) =
      inverseFieldCLM dimension domain (first + second) := by
  apply ContinuousLinearMap.ext
  intro field
  apply Lp.ext
  filter_upwards [inverseFieldCLM_coordinate dimension domain first (inverseFieldCLM dimension domain second field),
    inverseFieldCLM_coordinate dimension domain second field,
    inverseFieldCLM_coordinate dimension domain (first + second) field] with point firstLiteral secondLiteral sumLiteral
  apply lp.ext
  funext cell
  change inverseFieldCLM dimension domain first (inverseFieldCLM dimension domain second field) point cell = _
  rw [firstLiteral cell, secondLiteral cell, sumLiteral cell, smul_smul, inverseFactor_mul]

end Fields

theorem evaluation_consumer : EvaluationGoal := by
  intro dimension domain
  exact ⟨fun cell => ⟨cellProjection_norm_le (PhysicalValue dimension) cell,
    fieldCellProjection_norm_le dimension domain cell⟩,
    Grad.GenericCarriers.fieldCellProjection_ae dimension domain,
    fun _ _ => cells_ext (PhysicalValue dimension), fun _ _ => fields_ext dimension domain⟩

theorem recovery_consumer : RecoveryGoal := by
  intro dimension domain
  exact ⟨inverseCellCLM (PhysicalValue dimension), inverseFieldCLM dimension domain,
    fun order => ⟨inverseCellCLM_norm_le (PhysicalValue dimension) order,
      inverseCellCLM_injective (PhysicalValue dimension) order⟩,
    fun order => ⟨inverseFieldCLM_norm_le dimension domain order, inverseFieldCLM_injective dimension domain order⟩,
    inverseCellCLM_apply (PhysicalValue dimension), inverseFieldCLM_coordinate dimension domain,
    inverseCellCLM_zero (PhysicalValue dimension), inverseFieldCLM_zero dimension domain,
    inverseCellCLM_comp (PhysicalValue dimension), inverseFieldCLM_comp dimension domain⟩

end Grad.CellWeights

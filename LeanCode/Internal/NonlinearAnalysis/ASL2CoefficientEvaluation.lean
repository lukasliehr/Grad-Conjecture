import ASL1RawPointwise

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

open scoped Topology BigOperators ENNReal
open Filter

namespace Grad.AxisSourceLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct Grad.AxisSplit

variable {parameters : PhaseParameters}

theorem coefficientValue_bound {dimension : ℕ} (field : ACore parameters dimension)
    (cell : ℤ) (point : ClosedDisk) :
    ‖coefficientValue cell point field‖ ≤ diskSupConstant * originalGradeNorm 2 field := by
  have pointBound := diskSup_bound (phaseWeightedJet parameters cell (field.val cell)) point
  rw [phaseWeightedJet_value, norm_smul,
    Real.norm_of_nonneg (cartesianWeight_pos parameters cell point.val).le] at pointBound
  have energyBound := supEnergy_le_row parameters cell (field.val cell) 0
  simp only [pow_zero, one_mul] at energyBound
  have rowBound : ‖cellGradeRowLinear (grade := 2) parameters cell (field.val cell)‖ ≤
      originalGradeNorm 2 field := by
    rw [originalGradeNorm_eq_lp]
    have evaluation := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (⟨rawCartesianGradeCoordinates parameters 2 field.val, field.property 2⟩ :
        lp (fun _ : ℤ => CartesianGradeRow dimension 2) 2) cell
    simpa only [raw_norm_eq_row] using evaluation
  exact (le_mul_of_one_le_left (norm_nonneg _) (cartesianWeight_one_le parameters cell point)).trans
    (pointBound.trans ((mul_le_mul_of_nonneg_left energyBound diskSupConstant_pos.le).trans
      (mul_le_mul_of_nonneg_left rowBound diskSupConstant_pos.le)))

def rowCoefficientValue (row : Fin 4) (cell : ℤ) (point : ClosedDisk) :
    QuotientRows parameters →ₗ[ℂ] ComplexEuclidean 1 :=
  (coefficientValue cell point).comp (LinearMap.proj row)

theorem rowCoefficientValue_bound (rows : QuotientRows parameters)
    (row : Fin 4) (cell : ℤ) (point : ClosedDisk) :
    ‖rowCoefficientValue row cell point rows‖ ≤ diskSupConstant * rowsGradeNorm 2 rows := by
  apply (coefficientValue_bound (rows row) cell point).trans
  apply mul_le_mul_of_nonneg_left _ diskSupConstant_pos.le
  exact Finset.single_le_sum (fun _ _ => originalGradeNorm_nonnegative _ _) (Finset.mem_univ row)

/-- A genuine core derivative can be evaluated at every cell and every closed-disk point.
The estimate is in the original grade two norm, not an auxiliary coefficient topology. -/
theorem rowsDirectional_value {E : Type*} [AddCommGroup E] [Module ℂ E]
    (mapping : E → QuotientRows parameters) (base direction : E)
    (derivative : QuotientRows parameters)
    (genuine : ∀ grade, Tendsto
      (fun scalar : ℝ => rowsGradeNorm grade
        ((scalar : ℂ)⁻¹ • (mapping (base + (scalar : ℂ) • direction) - mapping base) - derivative))
      (𝓝[≠] 0) (𝓝 0))
    (row : Fin 4) (cell : ℤ) (point : ClosedDisk) :
    HasDerivAt (fun scalar : ℝ => rowCoefficientValue row cell point
      (mapping (base + (scalar : ℂ) • direction)))
      (rowCoefficientValue row cell point derivative) 0 := by
  apply (hasDerivAt_iff_tendsto_slope_zero).2
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have majorant := (genuine 2).const_mul diskSupConstant
  rw [mul_zero] at majorant
  have evaluated := squeeze_zero (fun _ => norm_nonneg _)
    (fun scalar : ℝ => rowCoefficientValue_bound
      ((scalar : ℂ)⁻¹ • (mapping (base + (scalar : ℂ) • direction) - mapping base) - derivative)
      row cell point) majorant
  simpa only [map_sub, map_smul, ← Complex.ofReal_inv, Complex.coe_smul,
    sub_zero, zero_smul, add_zero, zero_add, Complex.ofReal_zero] using evaluated

end Grad.AxisSourceLift

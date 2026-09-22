import AKU18ActualAxisFourierAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Algebra

theorem axisValueMap_mem {parameters : PhaseParameters} {input output : ℕ}
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (data : Grad.AxisCore.AxisSmoothCore parameters input) :
    (fun cell => mapping (data.val cell)) ∈ Grad.AxisCore.axisCoreSubmodule parameters output := by
  intro grade
  apply Summable.of_nonneg_of_le (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun cell => ?_) ((data.property grade).mul_left (‖mapping‖^2))
  have square := pow_le_pow_left₀ (norm_nonneg _) (mapping.le_opNorm (data.val cell)) 2
  rw [mul_pow] at square
  apply (mul_le_mul_of_nonneg_left square (sq_nonneg _)).trans_eq
  ring

def axisValueMap {parameters : PhaseParameters} {input output : ℕ}
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output) :
    Grad.AxisCore.AxisSmoothCore parameters input →ₗ[ℂ] Grad.AxisCore.AxisSmoothCore parameters output where
  toFun data := ⟨fun cell => mapping (data.val cell),axisValueMap_mem mapping data⟩
  map_add' first second := by
    apply Subtype.ext
    funext cell
    exact map_add mapping _ _
  map_smul' scalar data := by
    apply Subtype.ext
    funext cell
    exact map_smul mapping scalar _

theorem axisValueMap_val {parameters : PhaseParameters} {input output : ℕ}
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (data : Grad.AxisCore.AxisSmoothCore parameters input) (cell : ℤ) :
    (axisValueMap mapping data).val cell = mapping (data.val cell) := rfl

theorem axisValueMap_bound {parameters : PhaseParameters} {input output : ℕ}
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (data : Grad.AxisCore.AxisSmoothCore parameters input) (grade : ℕ) :
    ‖Grad.AxisCore.axisEta parameters output grade (axisValueMap mapping data)‖ ≤
      ‖mapping‖ * ‖Grad.AxisCore.axisEta parameters input grade data‖ := by
  have majorant : ‖‖mapping‖ • axisDataNormSequence grade data‖ =
      ‖mapping‖ * ‖Grad.AxisCore.axisEta parameters input grade data‖ := by
    rw [norm_smul,Real.norm_of_nonneg (norm_nonneg _),axisDataNormSequence_norm]
  rw [← majorant]
  apply lp.norm_mono (by norm_num)
  intro cell
  rw [Grad.AxisCore.axisEta_apply,axisValueMap_val,norm_smul,Complex.norm_real,
    Real.norm_of_nonneg (Grad.AxisCore.axisWeight_pos parameters grade cell).le]
  change _ ≤ ‖‖mapping‖ * axisDataNormSequence grade data cell‖
  rw [axisDataNormSequence_apply,Real.norm_of_nonneg (mul_nonneg (norm_nonneg mapping)
    (mul_nonneg (Grad.AxisCore.axisWeight_pos parameters grade cell).le (norm_nonneg _)))]
  apply (mul_le_mul_of_nonneg_left (mapping.le_opNorm (data.val cell))
    (Grad.AxisCore.axisWeight_pos parameters grade cell).le).trans_eq
  ring

theorem axisPhysicalValue_hasSum {parameters : PhaseParameters} {dimension : ℕ}
    (data : Grad.AxisCore.AxisSmoothCore parameters dimension) (angle : ℝ) :
    HasSum (fun cell => fourierPhase cell angle • data.val cell) (axisPhysicalValue data angle) := by
  apply Summable.hasSum
  apply Summable.of_norm
  simpa only [norm_smul,fourierPhase_norm,one_mul] using axisData_value_norm_summable data

theorem axisValueMap_physical {parameters : PhaseParameters} {input output : ℕ}
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (data : Grad.AxisCore.AxisSmoothCore parameters input) (angle : ℝ) :
    axisPhysicalValue (axisValueMap mapping data) angle = mapping (axisPhysicalValue data angle) := by
  have total := mapping.hasSum (axisPhysicalValue_hasSum data angle)
  have same := axisPhysicalValue_hasSum (axisValueMap mapping data) angle
  apply same.unique
  apply total.congr_fun
  intro cell
  rw [axisValueMap_val,map_smul]

end Grad.FinitePhysicalJetLift

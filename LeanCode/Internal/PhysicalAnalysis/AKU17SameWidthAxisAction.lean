import AKU16AxisConvolutionPointwise

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Physical.Allocation

theorem axisFamilyRawAction_mem {parameters : PhaseParameters} {input output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (data : Grad.AxisCore.AxisSmoothCore parameters input) :
    axisFamilyRawAction family data ∈ Grad.AxisCore.axisCoreSubmodule parameters output := by
  intro grade
  have member : Memℓp (fun cell => (Grad.AxisCore.axisWeight parameters grade cell : ℂ) •
      axisFamilyRawAction family data cell) 2 := by
    apply (lp.memℓp (axisActionMajorant family coherent data grade)).mono'
    intro cell
    rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (Grad.AxisCore.axisWeight_pos parameters grade cell).le]
    exact (axisFamilyRawAction_majorized family coherent data grade cell).trans (le_abs_self _)
  apply ((memlp_iff_summable_sq _).mp member).congr
  intro cell
  rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (Grad.AxisCore.axisWeight_pos parameters grade cell).le,mul_pow]

def axisFamilyAction {parameters : PhaseParameters} {input output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) :
    Grad.AxisCore.AxisSmoothCore parameters input →ₗ[ℂ] Grad.AxisCore.AxisSmoothCore parameters output where
  toFun data := ⟨axisFamilyRawAction family data,axisFamilyRawAction_mem family coherent data⟩
  map_add' first second := by
    apply Subtype.ext
    funext cell
    change (∑' shift, axisFamilyOperator family shift (first.val (cell-shift) + second.val (cell-shift))) = _
    simp_rw [map_add]
    exact (axisFamilyRawAction_term_summable family coherent first cell).of_norm.tsum_add
      (axisFamilyRawAction_term_summable family coherent second cell).of_norm
  map_smul' scalar data := by
    apply Subtype.ext
    funext cell
    change (∑' shift, axisFamilyOperator family shift (scalar • data.val (cell-shift))) = _
    simp_rw [map_smul]
    exact ((scalar • ContinuousLinearMap.id ℂ (ComplexEuclidean output)).map_tsum
      (axisFamilyRawAction_term_summable family coherent data cell).of_norm).symm

theorem axisFamilyAction_val {parameters : PhaseParameters} {input output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (data : Grad.AxisCore.AxisSmoothCore parameters input) (cell : ℤ) :
    (axisFamilyAction family coherent data).val cell =
      ∑' shift, axisFamilyOperator family shift (data.val (cell-shift)) := rfl

/-- Exact same-width one-high axis action, obtained from actual Young
convolution and without a source-norm hypothesis. -/
theorem axisFamilyAction_one_high_envelope {parameters : PhaseParameters} {input output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (data : Grad.AxisCore.AxisSmoothCore parameters input) (grade : ℕ) :
    ‖Grad.AxisCore.axisEta parameters output grade (axisFamilyAction family coherent data)‖ ≤ (2 : ℝ)^grade *
      (Grad.Constraints.Multipliers.envelope parameters grade (axisFamilyOperator family) *
        ‖Grad.AxisCore.axisEta parameters input 0 data‖ +
       Grad.Constraints.Multipliers.envelope parameters 0 (axisFamilyOperator family) *
        ‖Grad.AxisCore.axisEta parameters input grade data‖) := by
  apply le_trans _ (axisActionMajorant_norm_bound family coherent data grade)
  apply lp.norm_mono (by norm_num)
  intro cell
  rw [Grad.AxisCore.axisEta_apply,norm_smul,Complex.norm_real,
    Real.norm_of_nonneg (Grad.AxisCore.axisWeight_pos parameters grade cell).le]
  exact (axisFamilyRawAction_majorized family coherent data grade cell).trans (le_abs_self _)

/-- The matrix norm is the accepted completed original-width coefficient
norm. The high degree is allocated separately to coefficient and source. -/
theorem axisFamilyAction_one_high {parameters : PhaseParameters} {input output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (data : Grad.AxisCore.AxisSmoothCore parameters input) (grade : ℕ) :
    ‖Grad.AxisCore.axisEta parameters output grade (axisFamilyAction family coherent data)‖ ≤ (2 : ℝ)^grade *
      (((Real.exp parameters.sigma0 * 2 ^ grade) * ‖family grade‖) *
        ‖Grad.AxisCore.axisEta parameters input 0 data‖ +
       (Real.exp parameters.sigma0 * ‖family 0‖) *
        ‖Grad.AxisCore.axisEta parameters input grade data‖) := by
  apply (axisFamilyAction_one_high_envelope family coherent data grade).trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (axisFamilyOperator_envelope_bound family coherent grade) (norm_nonneg _)
  · simpa only [pow_zero,mul_one] using
      mul_le_mul_of_nonneg_right (axisFamilyOperator_envelope_bound family coherent 0)
        (norm_nonneg (Grad.AxisCore.axisEta parameters input grade data))

end Grad.FinitePhysicalJetLift

import AKU14AxisOneHighWeight

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds Grad.AxisSplit
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.PhaseAlgebra

/-- The exact axis Hilbert norm sequence. -/
def axisDataNormSequence {parameters : PhaseParameters} {dimension : ℕ} (grade : ℕ)
    (data : Grad.AxisCore.AxisSmoothCore parameters dimension) : lp (fun _ : ℤ => ℝ) 2 :=
  ⟨fun cell => ‖Grad.AxisCore.axisEta parameters dimension grade data cell‖,
    (lp.memℓp (Grad.AxisCore.axisEta parameters dimension grade data)).norm⟩

theorem axisDataNormSequence_apply {parameters : PhaseParameters} {dimension : ℕ} (grade : ℕ)
    (data : Grad.AxisCore.AxisSmoothCore parameters dimension) (cell : ℤ) :
    axisDataNormSequence grade data cell = Grad.AxisCore.axisWeight parameters grade cell * ‖data.val cell‖ := by
  change ‖Grad.AxisCore.axisEta parameters dimension grade data cell‖ = _
  rw [Grad.AxisCore.axisEta_apply,norm_smul,Complex.norm_real,
    Real.norm_of_nonneg (Grad.AxisCore.axisWeight_pos parameters grade cell).le]

theorem axisDataNormSequence_norm {parameters : PhaseParameters} {dimension : ℕ} (grade : ℕ)
    (data : Grad.AxisCore.AxisSmoothCore parameters dimension) :
    ‖axisDataNormSequence grade data‖ = ‖Grad.AxisCore.axisEta parameters dimension grade data‖ :=
  lp_norm_of_norms _

theorem axisData_value_norm_le {parameters : PhaseParameters} {dimension : ℕ}
    (data : Grad.AxisCore.AxisSmoothCore parameters dimension) (cell : ℤ) :
    ‖data.val cell‖ ≤ ‖Grad.AxisCore.axisEta parameters dimension 0 data‖ := by
  apply (le_mul_of_one_le_left (norm_nonneg _) (Grad.AxisCore.axisWeight_one_le parameters 0 cell)).trans
  rw [← axisDataNormSequence_apply]
  change ‖Grad.AxisCore.axisEta parameters dimension 0 data cell‖ ≤ _
  exact component_norm_le _ _

def axisFamilyRawAction {parameters : PhaseParameters} {input output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (data : Grad.AxisCore.AxisSmoothCore parameters input) : ℤ → ComplexEuclidean output :=
  fun cell => ∑' shift, axisFamilyOperator family shift (data.val (cell-shift))

theorem axisFamilyRawAction_term_summable {parameters : PhaseParameters} {input output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (data : Grad.AxisCore.AxisSmoothCore parameters input) (cell : ℤ) :
    Summable (fun shift => ‖axisFamilyOperator family shift (data.val (cell-shift))‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun shift => ?_)
    ((Grad.Constraints.Gauges.coefficientNorm_summable parameters _
      (axisFamilyOperator_envelope_summable family coherent 0)).mul_right
        ‖Grad.AxisCore.axisEta parameters input 0 data‖)
  exact ((axisFamilyOperator family shift).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (axisData_value_norm_le data _) (norm_nonneg _))

def axisEnvelopeConvolution {parameters : PhaseParameters} {input output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (grade : ℕ) : lp (fun _ : ℤ => ℝ) 2 →L[ℝ] lp (fun _ : ℤ => ℝ) 2 :=
  envelopeConvolution (Grad.Constraints.Multipliers.envelopeTerm parameters grade (axisFamilyOperator family))
    (Grad.Constraints.Multipliers.envelopeTerm_nonnegative parameters grade _)
    (axisFamilyOperator_envelope_summable family coherent grade)

theorem axisEnvelopeConvolution_apply {parameters : PhaseParameters} {input output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (grade : ℕ) (field : lp (fun _ : ℤ => ℝ) 2) (cell : ℤ) :
    axisEnvelopeConvolution family coherent grade field cell =
      ∑' shift, Grad.Constraints.Multipliers.envelopeTerm parameters grade (axisFamilyOperator family) shift *
        field (cell-shift) := envelopeConvolution_apply _ _ _ _ _

theorem axisEnvelopeConvolution_bound {parameters : PhaseParameters} {input output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (grade : ℕ) (field : lp (fun _ : ℤ => ℝ) 2) :
    ‖axisEnvelopeConvolution family coherent grade field‖ ≤
      Grad.Constraints.Multipliers.envelope parameters grade (axisFamilyOperator family) * ‖field‖ :=
  ((axisEnvelopeConvolution family coherent grade).le_opNorm field).trans
    (mul_le_mul_of_nonneg_right (envelopeConvolution_norm_le _ _ _) (norm_nonneg _))

/-- Exactly two Young convolution terms: the high degree is on the matrix
or on the source, and every other factor remains at degree zero. -/
def axisActionMajorant {parameters : PhaseParameters} {input output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (data : Grad.AxisCore.AxisSmoothCore parameters input) (grade : ℕ) :
    lp (fun _ : ℤ => ℝ) 2 :=
  (2 : ℝ)^grade • (axisEnvelopeConvolution family coherent grade (axisDataNormSequence 0 data) +
    axisEnvelopeConvolution family coherent 0 (axisDataNormSequence grade data))

theorem axisActionMajorant_norm_bound {parameters : PhaseParameters} {input output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (data : Grad.AxisCore.AxisSmoothCore parameters input) (grade : ℕ) :
    ‖axisActionMajorant family coherent data grade‖ ≤ (2 : ℝ)^grade *
      (Grad.Constraints.Multipliers.envelope parameters grade (axisFamilyOperator family) *
        ‖Grad.AxisCore.axisEta parameters input 0 data‖ +
       Grad.Constraints.Multipliers.envelope parameters 0 (axisFamilyOperator family) *
        ‖Grad.AxisCore.axisEta parameters input grade data‖) := by
  rw [axisActionMajorant,norm_smul,Real.norm_of_nonneg (pow_nonneg (by norm_num) _)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
  apply (norm_add_le _ _).trans
  simpa only [axisDataNormSequence_norm] using add_le_add
    (axisEnvelopeConvolution_bound family coherent grade (axisDataNormSequence 0 data))
    (axisEnvelopeConvolution_bound family coherent 0 (axisDataNormSequence grade data))

end Grad.FinitePhysicalJetLift

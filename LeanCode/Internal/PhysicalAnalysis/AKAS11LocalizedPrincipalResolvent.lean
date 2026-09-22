import AKAS10ActualTensorNormBounds
import AKAS7SecondResolventDistribution

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000

open MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.TensorBootstrap Grad.ClosedJets Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

variable {L sigma gamma ell : ℝ}

def startupSecondKernelSumFor (kernels : TensorIndex → FieldL2 →L[ℂ] FieldL2) :
    FieldL2 →L[ℂ] FieldL2 :=
  ∑ index : TensorIndex, (startupSecondL2 index).comp (kernels index)

def startupActualPrincipalL2 (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (compact : HasCompactSupport scalar) (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) :
    FieldL2 →L[ℂ] FieldL2 :=
  startupSecondKernelSumFor (fun index : TensorIndex => startupLocalizedKernel scalar smooth compact
    (startupActualPrincipalTensorKernel admissible data coherent inverseCoherent index.1 index.2))

theorem startupSecondL2_opNorm (index : TensorIndex) : ‖startupSecondL2 index‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro field
  exact (startupSecondL2_norm index field).trans_eq (one_mul _).symm

theorem startupSecondH1_opNorm (index : TensorIndex) : ‖startupSecondH1 index‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro field
  exact (startupSecondH1_norm index field).trans_eq (one_mul _).symm

theorem startupFourComposedBound {Input Output : Type*}
    [NormedAddCommGroup Input] [NormedSpace ℂ Input]
    [NormedAddCommGroup Output] [NormedSpace ℂ Output]
    (fixed : TensorIndex → Output →L[ℂ] Output)
    (rows : TensorIndex → Input →L[ℂ] Output) (payment : ℝ)
    (fixedBounds : ∀ index, ‖fixed index‖ ≤ 1)
    (rowBounds : ∀ index, ‖rows index‖ ≤ payment) :
    ‖∑ index, (fixed index).comp (rows index)‖ ≤ 4 * payment := by
  have bounded := startupFiniteComposedBound fixed rows 1 payment zero_le_one fixedBounds rowBounds
  have cardinality : (Fintype.card TensorIndex : ℝ) = 4 := by norm_num [TensorIndex]
  rw [cardinality, mul_one] at bounded
  exact bounded

theorem startupSecondKernelSum_h1_exists
    (kernels : TensorIndex → FieldL2 →L[ℂ] FieldL2) (payment : ℝ)
    (coarseBound : ∀ index, ‖kernels index‖ ≤ payment)
    (supplied : ∀ index, ∃ regular : FieldH1 →L[ℂ] FieldH1,
      (∀ field, valueInclusion (regular field) = kernels index (valueInclusion field)) ∧
      ‖regular‖ ≤ payment) :
    ∃ regular : FieldH1 →L[ℂ] FieldH1,
      (∀ field, valueInclusion (regular field) = startupSecondKernelSumFor kernels (valueInclusion field)) ∧
      ‖startupSecondKernelSumFor kernels‖ ≤ 4 * payment ∧ ‖regular‖ ≤ 4 * payment := by
  classical
  let lifts (index : TensorIndex) : FieldH1 →L[ℂ] FieldH1 := (supplied index).choose
  let regular : FieldH1 →L[ℂ] FieldH1 := ∑ index : TensorIndex, (startupSecondH1 index).comp (lifts index)
  refine ⟨regular, ?_, ?_, ?_⟩
  · intro field
    change valueInclusion ((∑ index : TensorIndex, (startupSecondH1 index).comp (lifts index)) field) = _
    simp only [startupSecondKernelSumFor, sum_apply, map_sum, ContinuousLinearMap.comp_apply]
    apply Finset.sum_congr rfl
    intro index _
    exact (startupSecond_compatible index (lifts index field)).trans
      (congrArg (startupSecondL2 index) ((supplied index).choose_spec.1 field))
  · exact startupFourComposedBound startupSecondL2 kernels payment startupSecondL2_opNorm coarseBound
  · exact startupFourComposedBound startupSecondH1 lifts payment startupSecondH1_opNorm
      (fun index => (supplied index).choose_spec.2)

/-- Actual bounded SAME H1 realization of the entire localized ER11
 principal tensor resolvent, with all four tensor entries paid. -/
theorem startupActualPrincipalH1_exists {parameters : PhaseParameters}
    {L ell rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar) (compact : HasCompactSupport scalar)
    (included : tsupport scalar ⊆ openUnitDisk)
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation))
    (threshold : ℝ) (small : ActualStartupRowsSmall ledger inverseCoherent threshold) :
    ∃ regular : FieldH1 →L[ℂ] FieldH1,
      (∀ field, valueInclusion (regular field) = startupActualPrincipalL2 scalar smooth compact
        admissible ledger.val ledger.property.1 inverseCoherent (valueInclusion field)) ∧
      ‖startupActualPrincipalL2 scalar smooth compact admissible ledger.val ledger.property.1 inverseCoherent‖ ≤
        4 * (startupCutoffConstant scalar smooth compact *
          (3 * startupPrincipalFixedConstant * (startupEREmbeddingConstant * threshold))) ∧
      ‖regular‖ ≤ 4 * (startupCutoffConstant scalar smooth compact *
          (3 * startupPrincipalFixedConstant * (startupEREmbeddingConstant * threshold))) := by
  classical
  let bound := 3 * startupPrincipalFixedConstant * (startupEREmbeddingConstant * threshold)
  let payment := startupCutoffConstant scalar smooth compact * bound
  have cutNonnegative := (startupCutoffConstant_positive scalar smooth compact).le
  have coarseCut : ‖startupCutoffL2 scalar smooth compact‖ ≤ startupCutoffConstant scalar smooth compact := by
    unfold startupCutoffConstant
    linarith [norm_nonneg (startupCutoffFirst scalar smooth compact)]
  have fineCut : ‖startupCutoffFirst scalar smooth compact‖ ≤ startupCutoffConstant scalar smooth compact := by
    unfold startupCutoffConstant
    linarith [norm_nonneg (startupCutoffL2 scalar smooth compact)]
  have coarseBound (index : TensorIndex) :
      ‖startupLocalizedKernel scalar smooth compact
        (startupActualPrincipalTensorKernel admissible ledger.val ledger.property.1 inverseCoherent index.1 index.2)‖ ≤ payment :=
    (startupLocalizedKernel_norm scalar smooth compact _).trans (mul_le_mul coarseCut
      (startupActualPrincipalTensor_bounds ledger inverseCoherent threshold small index.1 index.2).1
      (norm_nonneg (startupActualPrincipalTensorKernel admissible ledger.val ledger.property.1 inverseCoherent index.1 index.2))
      cutNonnegative)
  apply startupSecondKernelSum_h1_exists _ payment coarseBound
  intro index
  obtain ⟨regular, same, bounded⟩ := startupLocalizedKernel_h1_exists scalar smooth compact included
    (startupActualPrincipalTensorKernel admissible ledger.val ledger.property.1 inverseCoherent index.1 index.2)
    (startupActualPrincipalTensorFirst admissible ledger.val ledger.property.1 inverseCoherent index.1 index.2)
    (startupActualPrincipalTensor_compatible admissible ledger.val ledger.property.1 inverseCoherent index.1 index.2)
  refine ⟨regular, same, bounded.trans ?_⟩
  exact mul_le_mul fineCut
    (startupActualPrincipalTensor_bounds ledger inverseCoherent threshold small index.1 index.2).2
    (norm_nonneg (startupActualPrincipalTensorFirst admissible ledger.val ledger.property.1 inverseCoherent index.1 index.2))
    cutNonnegative

end Grad.CartesianStartup

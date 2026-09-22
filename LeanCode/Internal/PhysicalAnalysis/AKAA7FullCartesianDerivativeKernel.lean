import AKAA6ActualCartesianKernelMajorants

noncomputable section

set_option maxHeartbeats 1200000

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnalyticWeights.Higher

def startupDerivativeCoefficient {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (index : DerivativeIndex grade) (input shift : ℤ) :
    C(ClosedDisk, OperatorValue inputDimension outputDimension) :=
  (((scaledCellWeight L ell input ^ (derivativeOrder index - 1) : ℝ) : ℂ)⁻¹) •
    smoothOperatorDerivative (startupConjugatedCoefficientJet admissible family coherent input shift)
      (derivativeMultiIndex index)

theorem startupDerivativeCoefficient_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (index : DerivativeIndex grade) (input shift : ℤ) :
    ‖startupDerivativeCoefficient admissible family coherent index input shift‖ ≤
      startupDerivativeMajorant (family grade) index shift := by
  apply (ContinuousMap.norm_le _ (startupDerivativeMajorant_nonnegative admissible _ _ _)).mpr
  intro point
  have positive : 0 < scaledCellWeight L ell input ^ (derivativeOrder index - 1) :=
    pow_pos (lt_of_lt_of_le zero_lt_one (scaledCellWeight_one_le L ell input)) _
  change ‖((_ : ℂ)⁻¹) • (_ : OperatorValue inputDimension outputDimension)‖ ≤ _
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg positive.le,
    mul_comm, ← div_eq_mul_inv]
  exact (div_le_iff₀ positive).mpr
    (startupConjugatedCoefficientJet_derivative_bound admissible family coherent input shift index point)

theorem startupDerivativeConstant_nonnegative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade : ℕ} (index : DerivativeIndex grade) :
    0 ≤ startupDerivativeConstant L sigma gamma index :=
  Finset.sum_nonneg fun _split _ => mul_nonneg (Nat.cast_nonneg _)
    (apRatioConstant_nonnegative admissible _)

theorem startup_row_summable (majorant : ℤ → ℝ) (summable : Summable majorant) (output : ℤ) :
    Summable (fun input : ℤ => majorant (output - input)) :=
  ((Equiv.subLeft output).summable_iff).mpr summable

theorem startup_column_summable (majorant : ℤ → ℝ) (summable : Summable majorant) (input : ℤ) :
    Summable (fun output : ℤ => majorant (output - input)) :=
  ((Equiv.subRight input).summable_iff).mpr summable

/-- Actual Cartesian coefficient derivative on the full cell carrier.
 Order zero and one act on bare L2; order two has exactly one cell reserve. -/
def startupDerivativeKernelData {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (index : DerivativeIndex grade) :
    Grad.FullCellKernel.L2KernelData (Measure.dirac (0 : ℝ))
      inputDimension outputDimension openUnitDisk where
  domainMeasurable := openUnitDisk_isOpen.measurableSet
  orthogonal := fun _ => LinearIsometryEquiv.refl ℝ _
  invariant := fun _ => by intro point; rfl
  actionMeasurable := measurable_snd
  coefficient := fun output input pair => closedDiskLift
    (startupDerivativeCoefficient admissible family coherent index input (output - input)) pair.2
  weight := fun output input _ => startupDerivativeMajorant (family grade) index (output - input)
  coefficientMeasurable := fun output input =>
    (closedOperator_measurable
      (startupDerivativeCoefficient admissible family coherent index input (output - input))).comp_quasiMeasurePreserving
        quasiMeasurePreserving_snd
  weightMeasurable := fun _ _ => measurable_const
  weightNonnegative := fun _ _ _ => startupDerivativeMajorant_nonnegative admissible _ _ _
  weightIntegrable := fun _ _ => integrable_const _
  domination := fun output input => by
    filter_upwards [quasiMeasurePreserving_snd.ae (closedOperator_bound
      (startupDerivativeCoefficient admissible family coherent index input (output - input)))] with pair bound
    exact bound.trans (startupDerivativeCoefficient_bound admissible family coherent index input _)
  rowBound := startupDerivativeConstant L sigma gamma index * ‖family grade‖
  columnBound := startupDerivativeConstant L sigma gamma index * ‖family grade‖
  rowNonnegative := mul_nonneg (startupDerivativeConstant_nonnegative admissible index) (norm_nonneg _)
  columnNonnegative := mul_nonneg (startupDerivativeConstant_nonnegative admissible index) (norm_nonneg _)
  rowsSummable := fun output => by
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    exact startup_row_summable (startupDerivativeMajorant (family grade) index)
      (startupDerivativeMajorant_summable (family grade) index) output
  columnsSummable := fun input => by
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    exact startup_column_summable (startupDerivativeMajorant (family grade) index)
      (startupDerivativeMajorant_summable (family grade) index) input
  rows := fun output => by
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    have reindex := (Equiv.subLeft output).tsum_eq (startupDerivativeMajorant (family grade) index)
    change (∑' input : ℤ, startupDerivativeMajorant (family grade) index (output - input)) = _ at reindex
    rw [reindex]
    exact startupDerivativeMajorant_sum_bound admissible (family grade) index
  columns := fun input => by
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    have reindex := (Equiv.subRight input).tsum_eq (startupDerivativeMajorant (family grade) index)
    change (∑' output : ℤ, startupDerivativeMajorant (family grade) index (output - input)) = _ at reindex
    rw [reindex]
    exact startupDerivativeMajorant_sum_bound admissible (family grade) index

def startupDerivativeKernel {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (index : DerivativeIndex grade) :=
  Grad.FullCellKernel.kernel (startupDerivativeKernelData admissible family coherent index)

theorem startupDerivativeKernel_norm {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (index : DerivativeIndex grade) :
    ‖startupDerivativeKernel admissible family coherent index‖ ≤
      startupDerivativeConstant L sigma gamma index * ‖family grade‖ := by
  have bound := Grad.FullCellKernel.kernel_norm_le
    (startupDerivativeKernelData admissible family coherent index)
  change ‖startupDerivativeKernel admissible family coherent index‖ ≤
    Real.sqrt ((startupDerivativeConstant L sigma gamma index * ‖family grade‖) *
      (startupDerivativeConstant L sigma gamma index * ‖family grade‖)) at bound
  simpa only [Real.sqrt_mul_self (mul_nonneg
    (startupDerivativeConstant_nonnegative admissible index) (norm_nonneg (family grade)))] using bound

end Grad.GaugeCoefficients.Physical.RadialLedger

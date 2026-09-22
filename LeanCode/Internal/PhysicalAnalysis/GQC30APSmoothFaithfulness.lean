import GQC29FixedSmoothMultiplier

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope

theorem apL2Trace_lowering {dimension low high : ℕ} (L sigma gamma ell : ℝ) (ordered : low ≤ high)
    (cell : ℤ) (field : apGrade L sigma gamma ell dimension high) :
    apL2Trace L sigma gamma ell cell (apLowering L sigma gamma ell ordered field) = apL2Trace L sigma gamma ell cell field := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := dimension) (grade := high) L sigma gamma ell)
    (isClosed_eq ((apL2Trace L sigma gamma ell cell).continuous.comp (apLowering L sigma gamma ell ordered).continuous)
      (apL2Trace L sigma gamma ell cell).continuous) _ field
  intro core
  simp only [Function.comp_apply]
  rw [apLowering_core, apL2Trace_core, apL2Trace_core]

theorem apTrace_l2 {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension grade : ℕ} (large : 2 ≤ grade) (cell : ℤ) (field : apGrade L sigma gamma ell dimension grade) :
    closedValueL2Continuous dimension (apTrace admissible large cell field) = apL2Trace L sigma gamma ell cell field := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := dimension) (grade := grade) L sigma gamma ell)
    (isClosed_eq ((closedValueL2Continuous dimension).continuous.comp (apTrace admissible large cell).continuous)
      (apL2Trace L sigma gamma ell cell).continuous) _ field
  intro core
  simp only [Function.comp_apply]
  rw [apTrace_core, apL2Trace_core]
  rfl

theorem apSmoothJet_l2 {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (field : APSmooth L sigma gamma ell dimension) (grade : ℕ) (cell : ℤ) :
    closedContinuousToDiskL2 (apSmoothJet admissible dimension cell field).value =
      apL2Trace L sigma gamma ell cell (apSmoothGrade L sigma gamma ell dimension grade field) := by
  change closedValueL2Continuous dimension (apFamilyJet field.val field.property cell).value = _
  rw [apFamilyJet_value_trace admissible field.val field.property (by omega : 2 ≤ grade + 2) cell, apTrace_l2]
  change _ = apL2Trace L sigma gamma ell cell (field.val grade)
  rw [← field.property grade (grade + 2) (by omega), apL2Trace_lowering]

theorem closedValueL2_injective (dimension : ℕ) : Function.Injective (closedValueL2Continuous dimension) := by
  intro first second same
  apply sub_eq_zero.mp
  apply closedContinuousToDiskL2_eq_zero
  change closedValueL2Continuous dimension (first - second) = 0
  rw [map_sub, same, sub_self]

theorem apSmoothGrade_injective {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (dimension grade : ℕ) : Function.Injective (apSmoothGrade L sigma gamma ell dimension grade) := by
  intro first second same
  apply apSmoothJet_ext admissible
  intro cell
  apply closedJet_eq_of_value_eq
  apply closedValueL2_injective dimension
  exact (apSmoothJet_l2 admissible first grade cell).trans
    ((congrArg (apL2Trace L sigma gamma ell cell) same).trans (apSmoothJet_l2 admissible second grade cell).symm)

theorem apLiteralGrade_l2 {dimension grade : ℕ} (L sigma gamma ell : ℝ)
    (fields : ℤ → ClosedJet dimension)
    (summable : Memℓp (fun cell => apRowLinear (grade := grade) L sigma gamma ell cell (fields cell)) 2)
    (cell : ℤ) :
    apL2Trace L sigma gamma ell cell (apLiteralGrade L sigma gamma ell fields summable) =
      closedContinuousToDiskL2 (fields cell).value := by
  change closedOperatorL2 _ (apUnscaledCoordinate L sigma gamma ell cell (zeroGradeIndex grade)
    (apLiteralGrade L sigma gamma ell fields summable)) = _
  rw [apLiteralGrade_unscaled]
  change closedOperatorL2 _ (closedContinuousToDiskL2
    (closedMultiDerivative (apWeightedJet sigma gamma ell cell (fields cell)) (0, 0))) = _
  rw [closedMultiDerivative_zero, closedOperatorL2_closed]
  apply congrArg closedContinuousToDiskL2
  apply ContinuousMap.ext
  intro point
  change (originalWeight sigma gamma ell cell point.val)⁻¹ •
    (apWeightedJet sigma gamma ell cell (fields cell)).value point = _
  rw [apWeightedJet_value, smul_smul, inv_mul_cancel₀, one_smul]
  change Grad.AnalyticWeights.Calculus.physicalWeight sigma gamma ell cell point.val ≠ 0
  rw [Grad.AnalyticWeights.Calculus.physicalWeight_exp]
  exact (Real.exp_pos _).ne'

end Grad.GaugeCoefficients.Physical.Compensated

import GQC12APSmoothTower

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger

theorem apWeightedMultiDerivative_l2 {dimension grade : ℕ} (L sigma gamma ell : ℝ)
    (index : DerivativeIndex grade) (large : cartesianOrder (derivativeMultiIndex index) + 2 ≤ grade) (cell : ℤ)
    (field : apGrade L sigma gamma ell dimension grade) :
    closedValueL2Continuous dimension
      (apWeightedMultiDerivative L sigma gamma ell (derivativeMultiIndex index) large cell field) =
      apUnscaledCoordinate L sigma gamma ell cell index field := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := dimension) (grade := grade) L sigma gamma ell)
    (isClosed_eq ((closedValueL2Continuous dimension).continuous.comp
      (apWeightedMultiDerivative L sigma gamma ell (derivativeMultiIndex index) large cell).continuous)
      (apUnscaledCoordinate L sigma gamma ell cell index).continuous) _ field
  intro core
  simp only [Function.comp_apply]
  rw [apWeightedMultiDerivative_core, apUnscaledCoordinate_core]
  rfl

theorem apUnscaledCoordinate_lowering {dimension low high : ℕ} (L sigma gamma ell : ℝ)
    (ordered : low ≤ high) (cell : ℤ) (lowIndex : DerivativeIndex low) (highIndex : DerivativeIndex high)
    (same : derivativeMultiIndex lowIndex = derivativeMultiIndex highIndex)
    (field : apGrade L sigma gamma ell dimension high) :
    apUnscaledCoordinate L sigma gamma ell cell lowIndex (apLowering L sigma gamma ell ordered field) =
      apUnscaledCoordinate L sigma gamma ell cell highIndex field := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := dimension) (grade := high) L sigma gamma ell)
    (isClosed_eq ((apUnscaledCoordinate L sigma gamma ell cell lowIndex).continuous.comp
      (apLowering L sigma gamma ell ordered).continuous)
      (apUnscaledCoordinate L sigma gamma ell cell highIndex).continuous) _ field
  intro core
  simp only [Function.comp_apply]
  rw [apLowering_core, apUnscaledCoordinate_core, apUnscaledCoordinate_core, same]

theorem apFamilyClosedDerivative_l2 {L sigma gamma ell : ℝ} {dimension grade : ℕ}
    (family : APFamily L sigma gamma ell dimension) (coherent : APFamilyCoherent family)
    (cell : ℤ) (index : DerivativeIndex grade) :
    closedValueL2Continuous dimension (apFamilyClosedDerivative family cell (derivativeMultiIndex index)) =
      apUnscaledCoordinate L sigma gamma ell cell index (family grade) := by
  let high := grade + cartesianOrder (derivativeMultiIndex index) + 2
  have ordered : grade ≤ high := by dsimp [high]; omega
  let highIndex : DerivativeIndex high :=
    ⟨(⟨index.val.1.val, index.val.1.isLt.trans_le (Nat.add_le_add_right ordered 1)⟩,
      ⟨index.val.2.val, index.val.2.isLt.trans_le (Nat.add_le_add_right ordered 1)⟩), index.property.trans ordered⟩
  have large : cartesianOrder (derivativeMultiIndex highIndex) + 2 ≤ high := by
    change cartesianOrder (derivativeMultiIndex index) + 2 ≤ grade + cartesianOrder (derivativeMultiIndex index) + 2
    omega
  rw [apFamilyClosedDerivative_eq family coherent cell (derivativeMultiIndex index)
    (grade := high) large]
  change closedValueL2Continuous dimension
      (apWeightedMultiDerivative L sigma gamma ell (derivativeMultiIndex highIndex) large cell (family high)) = _
  rw [apWeightedMultiDerivative_l2, ← coherent grade high ordered,
    apUnscaledCoordinate_lowering L sigma gamma ell ordered cell index highIndex rfl]

theorem apFamilyWeightedJet_l2 {L sigma gamma ell : ℝ} {dimension grade : ℕ}
    (family : APFamily L sigma gamma ell dimension) (coherent : APFamilyCoherent family)
    (cell : ℤ) (index : DerivativeIndex grade) :
    closedDerivativeL2 (derivativeMultiIndex index) (apFamilyWeightedJet family coherent cell) =
      apUnscaledCoordinate L sigma gamma ell cell index (family grade) := by
  change closedValueL2Continuous dimension
    (closedMultiDerivative (apFamilyWeightedJet family coherent cell) (derivativeMultiIndex index)) = _
  rw [apFamilyWeightedJet_derivative, apFamilyClosedDerivative_l2 family coherent cell index]

end Grad.GaugeCoefficients.Physical.Compensated

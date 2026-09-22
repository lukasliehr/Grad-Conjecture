import GC18CoefficientBounds

noncomputable section

set_option maxHeartbeats 1200000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Frame

theorem coefficient_ext {L sigma gamma ell : ℝ} {grade input output : ℕ}
    {first second : Coefficient L sigma gamma ell grade input output}
    (equal : ∀ cell index point, coefficientDerivative first cell index point =
      coefficientDerivative second cell index point) : first = second := by
  apply Subtype.ext
  apply Subtype.ext
  funext pair
  rcases pair with ⟨cell, index⟩
  apply ContinuousMap.ext
  intro point
  calc
    _ = (coefficientScale L sigma gamma ell grade cell index point : ℂ) •
      coefficientDerivative first cell index point := weighted_derivative_literal grade input output first cell index point
    _ = (coefficientScale L sigma gamma ell grade cell index point : ℂ) •
      coefficientDerivative second cell index point := by rw [equal cell index point]
    _ = _ := (weighted_derivative_literal grade input output second cell index point).symm

theorem smoothOperatorJet_ext {input output : ℕ} {first second : SmoothOperatorJet input output}
    (equal : first.value = second.value) : first = second := by
  cases first
  cases second
  cases equal
  rfl

theorem constantFamily_identity (L sigma gamma ell : ℝ) (dimension : ℕ) :
    constantFamily L sigma gamma ell (ContinuousLinearMap.id ℂ (PhysicalValue dimension)) =
      identityFamily L sigma gamma ell dimension := by
  funext grade
  apply coefficient_ext
  intro cell index point
  change coefficientDerivative (seedConstantCell L sigma gamma ell grade 0 _) cell index point = _
  rw [seedConstantCell_derivative]
  by_cases zeroOrder : derivativeOrder index = 0
  · rw [if_pos zeroOrder, derivativeIndex_eq_zeroDerivativeIndexAt_of_order_zero index zeroOrder]
    exact (gradedIdentityCoefficient_zeroDerivative L sigma gamma ell grade dimension cell point).symm
  · rw [if_neg zeroOrder]
    have derivativeZero := gradedIdentityCoefficient_positiveDerivative L sigma gamma ell grade dimension
      cell index (Nat.pos_of_ne_zero zeroOrder) point
    change _ = coefficientDerivative (gradedIdentityCoefficient L sigma gamma ell grade dimension) cell index point
    rw [derivativeZero]
    split_ifs <;> rfl

theorem constantFamily_comp {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input middle output : ℕ} (outer : OperatorValue middle output) (inner : OperatorValue input middle) :
    composeFamily admissible (constantFamily L sigma gamma ell outer) (constantFamily L sigma gamma ell inner) =
      constantFamily L sigma gamma ell (outer.comp inner) := by
  funext grade
  apply Subtype.ext
  change rawComposition admissible grade (weightedSingle L sigma gamma ell grade 0 (seedConstantJet outer))
    (weightedSingle L sigma gamma ell grade 0 (seedConstantJet inner)) =
      weightedSingle L sigma gamma ell grade 0 (seedConstantJet (outer.comp inner))
  rw [rawComposition_weightedSingle, zero_add]
  congr 1

theorem constantFamily_add (L sigma gamma ell : ℝ) {input output : ℕ}
    (first second : OperatorValue input output) :
    (fun grade => constantFamily L sigma gamma ell first grade + constantFamily L sigma gamma ell second grade) =
      constantFamily L sigma gamma ell (first + second) := by
  funext grade
  apply coefficient_ext
  intro cell index point
  rw [coefficientDerivative_add_apply]
  change coefficientDerivative (seedConstantCell L sigma gamma ell grade 0 first) cell index point +
    coefficientDerivative (seedConstantCell L sigma gamma ell grade 0 second) cell index point =
      coefficientDerivative (seedConstantCell L sigma gamma ell grade 0 (first + second)) cell index point
  simp only [seedConstantCell_derivative]
  split_ifs <;> simp

theorem constantFamily_zero (L sigma gamma ell : ℝ) (input output : ℕ) :
    constantFamily L sigma gamma ell (0 : OperatorValue input output) = zeroFamily L sigma gamma ell input output := by
  funext grade
  apply coefficient_ext
  intro cell index point
  change coefficientDerivative (seedConstantCell L sigma gamma ell grade 0 0) cell index point =
    coefficientDerivative (0 : Coefficient L sigma gamma ell grade input output) cell index point
  rw [seedConstantCell_derivative]
  split_ifs <;> simp [coefficientDerivative, weightedDerivative]

theorem composeFamily_zero_right {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input middle output : ℕ} (outer : CoefficientFamily L sigma gamma ell middle output) :
    composeFamily admissible outer (zeroFamily L sigma gamma ell input middle) = zeroFamily L sigma gamma ell input output := by
  funext grade
  apply Subtype.ext
  exact rawComposition_zero_inner admissible grade (outer grade).val

theorem composeFamily_zero_left {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input middle output : ℕ} (inner : CoefficientFamily L sigma gamma ell input middle) :
    composeFamily admissible (zeroFamily L sigma gamma ell middle output) inner = zeroFamily L sigma gamma ell input output := by
  funext grade
  apply Subtype.ext
  exact rawComposition_zero_outer admissible grade (inner grade).val

theorem composeFamily_identity_identity {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (dimension : ℕ) : composeFamily admissible (identityFamily L sigma gamma ell dimension)
      (identityFamily L sigma gamma ell dimension) = identityFamily L sigma gamma ell dimension := by
  rw [← constantFamily_identity L sigma gamma ell dimension, constantFamily_comp]
  rfl

end Grad.GaugeCoefficients.Physical.RadialLedger

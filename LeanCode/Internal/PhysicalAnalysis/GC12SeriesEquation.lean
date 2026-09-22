import GC12BaseInverse

noncomputable section

set_option maxHeartbeats 3000000

open Set
open Grad.GenericCarriers Grad.ClosedJets Grad.GaugeCoefficients.Envelope
open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Neumann.Regularity

open Grad.GaugeCoefficients.Algebra

theorem identitySmoothOperatorJet_positive_derivative (dimension : ℕ)
    (index : CartesianMultiIndex) (positive : 0 < cartesianOrder index) :
    smoothOperatorDerivative (identitySmoothOperatorJet dimension) index = 0 := by
  apply continuousMap_eq_of_openDisk
  intro point inside
  change (Classical.choose
    ((identitySmoothOperatorJet dimension).derivativeExists index)) point = 0
  calc
    (Classical.choose
        ((identitySmoothOperatorJet dimension).derivativeExists index)) point =
      cartesianMultiDerivative index
        (closedDiskLift (identitySmoothValue dimension)) point.val :=
      Classical.choose_spec
        ((identitySmoothOperatorJet dimension).derivativeExists index) point inside
    _ = 0 := by
      have localEquality :=
        closedDiskLift_identitySmoothValue_eventually dimension point.val inside
      unfold cartesianMultiDerivative cartesianDerivative
      have derivativeEquality :=
        (localEquality.iteratedFDeriv ℝ (cartesianOrder index)).eq_of_nhds
      rw [derivativeEquality]
      rw [iteratedFDeriv_const_of_ne (Nat.ne_of_gt positive)
        (ContinuousLinearMap.id ℂ (PhysicalValue dimension))]
      rfl

theorem gradedIdentityCoefficient_positiveDerivative
    (L sigma gamma ell : ℝ) (grade dimension : ℕ)
    (cell : ℤ) (index : DerivativeIndex grade)
    (positive : 0 < derivativeOrder index) (point : ClosedDisk) :
    coefficientDerivative
        (gradedIdentityCoefficient L sigma gamma ell grade dimension)
        cell index point = 0 := by
  change ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹) •
    weightedSingle L sigma gamma ell grade 0
      (identitySmoothOperatorJet dimension) (cell, index) point = 0
  rw [weightedSingle_apply]
  by_cases cellZero : cell = 0
  · subst cell
    rw [if_pos rfl]
    change ((coefficientScale L sigma gamma ell grade 0 index point : ℂ)⁻¹) •
      ((coefficientScale L sigma gamma ell grade 0 index point : ℂ) •
        smoothOperatorDerivative (identitySmoothOperatorJet dimension)
          (derivativeMultiIndex index) point) = 0
    rw [identitySmoothOperatorJet_positive_derivative dimension
      (derivativeMultiIndex index) positive]
    change ((coefficientScale L sigma gamma ell grade 0 index point : ℂ)⁻¹) •
      ((coefficientScale L sigma gamma ell grade 0 index point : ℂ) •
        (0 : OperatorValue dimension dimension)) = 0
    apply ContinuousLinearMap.ext
    intro value
    simp
  · rw [if_neg cellZero]
    change ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹) •
      (0 : OperatorValue dimension dimension) = 0
    apply ContinuousLinearMap.ext
    intro value
    simp

def gradedCompositionRight {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade dimension : ℕ)
    (outer : Coefficient L sigma gamma ell grade dimension dimension) :
    Coefficient L sigma gamma ell grade dimension dimension →L[ℂ]
    Coefficient L sigma gamma ell grade dimension dimension :=
  LinearMap.mkContinuous
    { toFun := fun inner => coefficientComposition admissible grade outer inner
      map_add' := fun first second => by
        apply Subtype.ext
        exact rawComposition_add_inner admissible grade outer.1 first.1 second.1
      map_smul' := fun scalar inner => by
        apply Subtype.ext
        exact rawComposition_smul_inner admissible grade scalar outer.1 inner.1 }
    (gradeProductConstant grade * ‖outer‖) (fun inner => by
      change ‖coefficientComposition admissible grade outer inner‖ ≤
        (gradeProductConstant grade * ‖outer‖) * ‖inner‖
      simpa only [mul_assoc] using
        coefficientComposition_norm_le admissible grade outer inner)

@[simp] theorem gradedCompositionRight_apply {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (outer inner : Coefficient L sigma gamma ell grade dimension dimension) :
    gradedCompositionRight admissible grade dimension outer inner =
      coefficientComposition admissible grade outer inner := rfl

theorem gradedCoefficientNeumannInverse_eq_identity_add_tail
    {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (positive : 0 < dimension)
    (baseCoefficient : BaseCoefficient L sigma gamma ell dimension)
    (gradedCoefficient : Coefficient L sigma gamma ell grade dimension dimension)
    (theta : ℝ)
    (realizes : RealizesSameCoefficient baseCoefficient gradedCoefficient)
    (normBound : ‖baseCoefficient‖ ≤ theta) (thetaLt : theta < 1) :
    gradedCoefficientNeumannInverse admissible gradedCoefficient =
      gradedIdentityCoefficient L sigma gamma ell grade dimension +
        ∑' power : ℕ,
          gradedCoefficientPower admissible gradedCoefficient (power + 1) := by
  unfold gradedCoefficientNeumannInverse
  rw [(gradedCoefficientPower_summable admissible positive baseCoefficient
    gradedCoefficient theta realizes normBound thetaLt).tsum_eq_zero_add]
  rw [gradedCoefficientPower_zero]

theorem gradedCoefficient_mul_neumannInverse
    {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (positive : 0 < dimension)
    (baseCoefficient : BaseCoefficient L sigma gamma ell dimension)
    (gradedCoefficient : Coefficient L sigma gamma ell grade dimension dimension)
    (theta : ℝ)
    (realizes : RealizesSameCoefficient baseCoefficient gradedCoefficient)
    (normBound : ‖baseCoefficient‖ ≤ theta) (thetaLt : theta < 1) :
    coefficientComposition admissible grade gradedCoefficient
        (gradedCoefficientNeumannInverse admissible gradedCoefficient) =
      ∑' power : ℕ,
        gradedCoefficientPower admissible gradedCoefficient (power + 1) := by
  let multiplication := gradedCompositionRight admissible grade dimension
    gradedCoefficient
  have summable := gradedCoefficientPower_summable admissible positive
    baseCoefficient gradedCoefficient theta realizes normBound thetaLt
  unfold gradedCoefficientNeumannInverse
  change multiplication
    (∑' power : ℕ, gradedCoefficientPower admissible gradedCoefficient power) = _
  rw [multiplication.map_tsum summable]
  apply tsum_congr
  intro power
  rfl

theorem gradedCoefficientNeumannInverse_fixedPoint
    {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (positive : 0 < dimension)
    (baseCoefficient : BaseCoefficient L sigma gamma ell dimension)
    (gradedCoefficient : Coefficient L sigma gamma ell grade dimension dimension)
    (theta : ℝ)
    (realizes : RealizesSameCoefficient baseCoefficient gradedCoefficient)
    (normBound : ‖baseCoefficient‖ ≤ theta) (thetaLt : theta < 1) :
    gradedCoefficientNeumannInverse admissible gradedCoefficient =
      gradedIdentityCoefficient L sigma gamma ell grade dimension +
        coefficientComposition admissible grade gradedCoefficient
          (gradedCoefficientNeumannInverse admissible gradedCoefficient) := by
  calc
    gradedCoefficientNeumannInverse admissible gradedCoefficient =
        gradedIdentityCoefficient L sigma gamma ell grade dimension +
          ∑' power : ℕ,
            gradedCoefficientPower admissible gradedCoefficient (power + 1) :=
      gradedCoefficientNeumannInverse_eq_identity_add_tail admissible positive
        baseCoefficient gradedCoefficient theta realizes normBound thetaLt
    _ = gradedIdentityCoefficient L sigma gamma ell grade dimension +
        coefficientComposition admissible grade gradedCoefficient
          (gradedCoefficientNeumannInverse admissible gradedCoefficient) := by
      rw [gradedCoefficient_mul_neumannInverse admissible positive baseCoefficient
        gradedCoefficient theta realizes normBound thetaLt]

end Grad.GaugeCoefficients.Neumann.Regularity

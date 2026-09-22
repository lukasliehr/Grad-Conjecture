import SCD19RadialPairing

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState

/-- C1 test functions with zero endpoint values. The unknown field has no
endpoint condition; these tests express its ordinary weak radial derivative. -/
structure RadialTest (lower : ℝ) where
  value : ℝ → ℝ
  derivative : ℝ → ℝ
  continuousValue : Continuous value
  continuousDerivative : Continuous derivative
  derivativeLaw : ∀ radius, HasDerivAt value (derivative radius) radius
  lowerZero : value lower = 0
  upperZero : value 1 = 0

def HasWeakRadialDerivative {dimension : ℕ} (lower : ℝ) (positive : 0 < lower)
    (field derivative : RadialL2 dimension lower) : Prop :=
  ∀ (test : RadialTest lower) (vector : ComplexEuclidean dimension),
    radialPairing lower positive test.value test.continuousValue vector derivative =
      -radialPairing lower positive test.derivative test.continuousDerivative vector field

theorem radialPairing_classical_derivative {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field derivative : ℝ → ComplexEuclidean dimension)
    (fieldContinuous : Continuous field) (derivativeContinuous : Continuous derivative)
    (derivativeLaw : ∀ radius, HasDerivAt field (derivative radius) radius) :
    HasWeakRadialDerivative lower positive (radialToLp lower field fieldContinuous)
      (radialToLp lower derivative derivativeContinuous) := by
  intro test vector
  rw [radialPairing_literal lower positive bounded, radialPairing_literal lower positive bounded]
  let pairing := (innerSL ℂ vector).restrictScalars ℝ
  have pairedDerivative (radius : ℝ) :
      HasDerivAt (fun point => inner ℂ vector (field point))
        (inner ℂ vector (derivative radius)) radius :=
    pairing.hasFDerivAt.comp_hasDerivAt radius (derivativeLaw radius)
  have identity := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (a := lower) (b := 1)
    (fun radius _ => test.derivativeLaw radius)
    (fun radius _ => pairedDerivative radius)
    (test.continuousDerivative.intervalIntegrable lower 1)
    ((pairing.continuous.comp derivativeContinuous).intervalIntegrable lower 1)
  simpa only [test.lowerZero, test.upperZero, zero_smul, sub_self, zero_sub] using identity

theorem radialCoefficient_weak_derivative {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : ℝ × ℝ → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field)
    (mode : ℤ) (order : ℕ) :
    HasWeakRadialDerivative lower positive
      (radialToLp lower (radialCoefficientJet field mode order)
        (radialCoefficientJet_smooth field smooth mode order).continuous)
      (radialToLp lower (radialCoefficientJet field mode (order + 1))
        (radialCoefficientJet_smooth field smooth mode (order + 1)).continuous) :=
  radialPairing_classical_derivative lower positive bounded _ _ _ _
    (radialCoefficientJet_hasDerivAt field smooth mode order)

theorem HasWeakRadialDerivative.smul {dimension : ℕ} {lower : ℝ} {positive : 0 < lower}
    {field derivative : RadialL2 dimension lower}
    (weak : HasWeakRadialDerivative lower positive field derivative) (scalar : ℂ) :
    HasWeakRadialDerivative lower positive (scalar • field) (scalar • derivative) := by
  intro test vector
  simp only [map_smul, weak test vector, smul_neg]

end Grad.SourceCollarDivision

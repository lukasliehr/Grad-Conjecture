import GC13Interface

noncomputable section

set_option maxHeartbeats 3000000

open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets
open Grad.GaugeCoefficients.Envelope

namespace Grad.GaugeCoefficients.Radial

open Grad.GaugeCoefficients.Algebra

def fixedMultiplierLinear {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (field : SmoothOperatorJet middleDimension outputDimension) :
    Coefficient L sigma gamma ell grade inputDimension middleDimension →ₗ[ℂ]
      Coefficient L sigma gamma ell grade inputDimension outputDimension where
  toFun coefficient := coefficientComposition admissible grade
    (fixedCoefficient L sigma gamma ell grade field) coefficient
  map_add' first second := by
    apply Subtype.ext
    exact rawComposition_add_inner admissible grade
      (fixedCoefficient L sigma gamma ell grade field).1 first.1 second.1
  map_smul' scalar coefficient := by
    apply Subtype.ext
    exact rawComposition_smul_inner admissible grade scalar
      (fixedCoefficient L sigma gamma ell grade field).1 coefficient.1

def fixedMultiplierMap {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (field : SmoothOperatorJet middleDimension outputDimension) :
    Coefficient L sigma gamma ell grade inputDimension middleDimension →L[ℂ]
      Coefficient L sigma gamma ell grade inputDimension outputDimension :=
  (fixedMultiplierLinear admissible grade field).mkContinuous
    (gradeProductConstant grade *
      ‖fixedCoefficient L sigma gamma ell grade field‖)
    (fun coefficient => coefficientComposition_norm_le admissible grade
      (fixedCoefficient L sigma gamma ell grade field) coefficient)

theorem fixedMultiplierMap_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (field : SmoothOperatorJet middleDimension outputDimension)
    (coefficient : Coefficient L sigma gamma ell grade inputDimension middleDimension) :
    ‖fixedMultiplierMap admissible grade field coefficient‖ ≤
      gradeProductConstant grade *
        ‖fixedCoefficient L sigma gamma ell grade field‖ * ‖coefficient‖ := by
  exact coefficientComposition_norm_le admissible grade
    (fixedCoefficient L sigma gamma ell grade field) coefficient

theorem fixedMultiplierMap_derivative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (field : SmoothOperatorJet middleDimension outputDimension)
    (coefficient : Coefficient L sigma gamma ell grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientDerivative (fixedMultiplierMap admissible grade field coefficient)
        cell index point =
      formalCompositionDerivative (fixedCoefficient L sigma gamma ell grade field)
        coefficient cell index point := by
  exact coefficientComposition_derivative admissible grade
    (fixedCoefficient L sigma gamma ell grade field) coefficient cell index point

end Grad.GaugeCoefficients.Radial

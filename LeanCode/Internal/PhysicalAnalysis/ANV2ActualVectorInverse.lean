import ANV1HelicityAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
open Set MeasureTheory
open scoped BigOperators
namespace Grad.ActualNonexceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra Grad.ActualAngularInverse
variable {L sigma gamma ell : ℝ}

def apSignedInverse (admissible : Admissible L sigma gamma ell) (sign : ℤ) :
    APSmooth L sigma gamma ell 2 →ₗ[ℂ] APSmooth L sigma gamma ell 2 :=
  (apShiftInverseLinear admissible 2 sign).comp (apHelicity L sigma gamma ell sign)

def apVectorInverse (admissible : Admissible L sigma gamma ell) :
    APSmooth L sigma gamma ell 2 →ₗ[ℂ] APSmooth L sigma gamma ell 2 :=
  apSignedInverse admissible 1 + apSignedInverse admissible (-1)

def vectorRotation (admissible : Admissible L sigma gamma ell) :
    APSmooth L sigma gamma ell 2 →ₗ[ℂ] APSmooth L sigma gamma ell 2 :=
  apSmoothRotation admissible 2 + apSmoothQuarter L sigma gamma ell

def VectorNonresonant (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 2) : Prop :=
  APNonresonant admissible 1 (apHelicity L sigma gamma ell 1 field) ∧
    APNonresonant admissible (-1) (apHelicity L sigma gamma ell (-1) field)

theorem apSignedInverse_quarter (admissible : Admissible L sigma gamma ell)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (field : APSmooth L sigma gamma ell 2) :
    apSmoothQuarter L sigma gamma ell (apSignedInverse admissible sign field) =
      (Complex.I * (sign : ℂ)) • apSignedInverse admissible sign field := by
  have commute := (apShiftInverse_valueMap admissible quarterValueMap sign (apHelicity L sigma gamma ell sign field)).symm
  exact commute.trans ((congrArg (apShiftInverse admissible sign)
    (apHelicity_quarter admissible sign signed field)).trans
      (map_smul (apShiftInverseLinear admissible 2 sign) _ _))

theorem apSignedInverse_solves (admissible : Admissible L sigma gamma ell)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (field : APSmooth L sigma gamma ell 2)
    (nonresonant : APNonresonant admissible sign (apHelicity L sigma gamma ell sign field)) :
    vectorRotation admissible (apSignedInverse admissible sign field) = apHelicity L sigma gamma ell sign field := by
  exact (congrArg (fun second : APSmooth L sigma gamma ell 2 =>
      apSmoothRotation admissible 2 (apSignedInverse admissible sign field) + second)
    (apSignedInverse_quarter admissible sign signed field)).trans
      (apShiftInverse_solves admissible sign (apHelicity L sigma gamma ell sign field) nonresonant)

/-- Genuine inversion of the Cartesian vector operator R+J. Its two resonance
conditions are stated on the actual helicity components of the original source. -/
theorem apVectorInverse_solves (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 2) (nonresonant : VectorNonresonant admissible field) :
    vectorRotation admissible (apVectorInverse admissible field) = field := by
  exact (map_add (vectorRotation admissible) (apSignedInverse admissible 1 field)
    (apSignedInverse admissible (-1) field)).trans
      ((congrArg₂ (fun first second : APSmooth L sigma gamma ell 2 => first + second)
        (apSignedInverse_solves admissible 1 (Or.inl rfl) field nonresonant.1)
        (apSignedInverse_solves admissible (-1) (Or.inr rfl) field nonresonant.2)).trans
          (apHelicity_sum admissible field))

end Grad.ActualNonexceptionalInverse

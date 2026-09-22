import ANS11InverseCompatibility
import ANM8ActualMeanConsumer

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

/-- The two actual constant Cartesian helicity projections. -/
def helicityValue (sign : ℤ) : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2 :=
  if sign = 1 then positiveHelicity else negativeHelicity

theorem helicityValue_positive : helicityValue 1 = positiveHelicity := by simp [helicityValue]
theorem helicityValue_negative : helicityValue (-1) = negativeHelicity := by norm_num [helicityValue]

theorem helicityValue_sum (value : ComplexEuclidean 2) :
    helicityValue 1 value + helicityValue (-1) value = value := by
  rw [helicityValue_positive, helicityValue_negative]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [positiveHelicity_apply, negativeHelicity_apply] <;> ring

theorem helicityValue_quarter (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (value : ComplexEuclidean 2) :
    quarterValueMap (helicityValue sign value) = (Complex.I * (sign : ℂ)) • helicityValue sign value := by
  rcases signed with rfl | rfl
  · rw [helicityValue_positive]
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp [quarterValueMap, quarterValueLinear, positiveHelicity_apply] <;>
      ring_nf <;> simp [Complex.I_sq] <;> ring
  · rw [helicityValue_negative]
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp [quarterValueMap, quarterValueLinear, negativeHelicity_apply] <;>
      ring_nf <;> simp [Complex.I_sq] <;> ring

theorem helicityJet_quarter (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (field : ClosedJet 2) :
    valueMapJet quarterValueMap (valueMapJet (helicityValue sign) field) =
      (Complex.I * (sign : ℂ)) • valueMapJet (helicityValue sign) field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simpa only [valueMapJet_value, closedJet_value_smul, ContinuousMap.smul_apply] using!
    helicityValue_quarter sign signed (field.value point)

variable {L sigma gamma ell : ℝ}

def apHelicity (L sigma gamma ell : ℝ) (sign : ℤ) :
    APSmooth L sigma gamma ell 2 →ₗ[ℂ] APSmooth L sigma gamma ell 2 :=
  apSmoothValueMap L sigma gamma ell (helicityValue sign)

theorem apHelicity_sum (admissible : Admissible L sigma gamma ell) (field : APSmooth L sigma gamma ell 2) :
    apHelicity L sigma gamma ell 1 field + apHelicity L sigma gamma ell (-1) field = field := by
  apply apSmoothJet_ext admissible
  intro cell
  have first := apSmoothValueMap_jet admissible (helicityValue 1) field cell
  have second := apSmoothValueMap_jet admissible (helicityValue (-1)) field cell
  have closed : valueMapJet (helicityValue 1) (apSmoothJet admissible 2 cell field) +
      valueMapJet (helicityValue (-1)) (apSmoothJet admissible 2 cell field) = apSmoothJet admissible 2 cell field := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    simpa only [closedJet_value_add, ContinuousMap.add_apply, valueMapJet_value] using
      helicityValue_sum ((apSmoothJet admissible 2 cell field).value point)
  exact (map_add (apSmoothJet admissible 2 cell) _ _).trans
    ((congrArg₂ (fun a b : ClosedJet 2 => a + b) first second).trans closed)

theorem apHelicity_quarter (admissible : Admissible L sigma gamma ell)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (field : APSmooth L sigma gamma ell 2) :
    apSmoothQuarter L sigma gamma ell (apHelicity L sigma gamma ell sign field) =
      (Complex.I * (sign : ℂ)) • apHelicity L sigma gamma ell sign field := by
  apply apSmoothJet_ext admissible
  intro cell
  have inner := apSmoothValueMap_jet admissible (helicityValue sign) field cell
  exact (apSmoothValueMap_jet admissible quarterValueMap _ cell).trans
    ((congrArg (valueMapJet quarterValueMap) inner).trans
      ((helicityJet_quarter sign signed _).trans
        ((congrArg (fun value : ClosedJet 2 => (Complex.I * (sign : ℂ)) • value) inner.symm).trans
          (map_smul (apSmoothJet admissible 2 cell) _ _).symm)))

end Grad.ActualNonexceptionalInverse

import ANV10ActualAxisDomain

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualNonexceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra Grad.ActualAngularInverse
open Grad.RawCircularSectors
variable {L sigma gamma ell : ℝ}

def vectorInverseJetLinear : ClosedJet 2 →ₗ[ℂ] ClosedJet 2 :=
  (shiftInverseLinear 2 1).comp (valueMapJetLinear 2 2 (helicityValue 1)) +
    (shiftInverseLinear 2 (-1)).comp (valueMapJetLinear 2 2 (helicityValue (-1)))

def vectorInverseJet (field : ClosedJet 2) : ClosedJet 2 := vectorInverseJetLinear field

theorem rawVectorJet_helicity_commute (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (mode : ℤ) (field : ClosedJet 2) :
    rawVectorJet mode (valueMapJet (helicityValue sign) field) = valueMapJet (helicityValue sign) (rawVectorJet mode field) := by
  rcases signed with rfl | rfl <;>
    simp only [helicityValue_positive, helicityValue_negative, rawVectorJet_eq, angularClosedJet_valueMap,
      valueMapJet_add, valueMapJet_comp, positiveHelicity_idempotent, negativeHelicity_idempotent,
      positiveHelicity_negative, negativeHelicity_positive, valueMapJet_zero, add_zero, zero_add]

theorem shiftInverseJet_rawVector (shift mode : ℤ) (field : ClosedJet 2) :
    shiftInverseJet shift (rawVectorJet mode field) = rawVectorJet mode (shiftInverseJet shift field) := by
  change shiftInverseLinear 2 shift (valueMapJet positiveHelicity (angularClosedJet (mode + 1) field) +
    valueMapJet negativeHelicity (angularClosedJet (mode - 1) field)) = _
  rw [map_add]
  change shiftInverseJet shift (valueMapJet positiveHelicity (angularClosedJet (mode + 1) field)) +
    shiftInverseJet shift (valueMapJet negativeHelicity (angularClosedJet (mode - 1) field)) = _
  rw [shiftInverseJet_valueMap, shiftInverseJet_valueMap, shiftInverseJet_angular, shiftInverseJet_angular]
  rfl

theorem rawVectorJet_vectorInverse (mode : ℤ) (field : ClosedJet 2) :
    rawVectorJet mode (vectorInverseJet field) = vectorInverseJet (rawVectorJet mode field) := by
  change rawVectorJetLinear mode (shiftInverseJet 1 (valueMapJet (helicityValue 1) field) +
    shiftInverseJet (-1) (valueMapJet (helicityValue (-1)) field)) = _
  rw [map_add]
  change rawVectorJet mode (shiftInverseJet 1 (valueMapJet (helicityValue 1) field)) +
    rawVectorJet mode (shiftInverseJet (-1) (valueMapJet (helicityValue (-1)) field)) = _
  rw [← shiftInverseJet_rawVector, ← shiftInverseJet_rawVector,
    rawVectorJet_helicity_commute 1 (Or.inl rfl), rawVectorJet_helicity_commute (-1) (Or.inr rfl)]
  rfl

theorem apVectorInverse_jet (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 2) (cell : ℤ) :
    apSmoothJet admissible 2 cell (apVectorInverse admissible field) = vectorInverseJet (apSmoothJet admissible 2 cell field) := by
  have signed (sign : ℤ) : apSmoothJet admissible 2 cell (apSignedInverse admissible sign field) =
      shiftInverseJet sign (valueMapJet (helicityValue sign) (apSmoothJet admissible 2 cell field)) :=
    (apShiftInverse_jet admissible sign _ cell).trans
      (congrArg (shiftInverseJet sign) (apSmoothValueMap_jet admissible (helicityValue sign) field cell))
  exact (map_add (apSmoothJet admissible 2 cell) _ _).trans
    (congrArg₂ (fun first second : ClosedJet 2 => first + second) (signed 1) (signed (-1)))

theorem apVectorInverse_rawVector (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (field : APSmooth L sigma gamma ell 2) :
    apSmoothRawVector L sigma gamma ell mode (apVectorInverse admissible field) =
      apVectorInverse admissible (apSmoothRawVector L sigma gamma ell mode field) := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothRawVector_jet admissible mode _ cell).trans
    ((congrArg (rawVectorJet mode) (apVectorInverse_jet admissible field cell)).trans
      ((rawVectorJet_vectorInverse mode _).trans
        ((congrArg vectorInverseJet (apSmoothRawVector_jet admissible mode field cell).symm).trans
          (apVectorInverse_jet admissible _ cell).symm)))

theorem reconstructedVector_excluded (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (thetaExcluded : ScalarAvoidsExceptional admissible theta) (sourceExcluded : AvoidsExceptionalSource source)
    (mode : ℤ) (exceptional : IsExceptionalRaw mode) :
    apSmoothRawVector L sigma gamma ell mode (reconstructedVector admissible theta source.1) = 0 := by
  have original := (apVectorInverse_rawVector admissible mode (reconstructionLoad admissible theta source.1)).trans
    ((congrArg (apVectorInverse admissible) (reconstructionLoad_excluded admissible theta source thetaExcluded sourceExcluded mode exceptional)).trans
      (map_zero _))
  exact (map_neg (apSmoothRawVector L sigma gamma ell mode) _).trans
    ((congrArg Neg.neg original).trans neg_zero)

end Grad.ActualNonexceptionalInverse

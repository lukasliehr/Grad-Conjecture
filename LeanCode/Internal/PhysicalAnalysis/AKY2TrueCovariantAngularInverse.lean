import AKY1ActualCurrentQuotient
import ANP12RotationCommutation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.CartesianUncompressed
open Grad.NonlinearRange
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.ActualAngularInverse Grad.ActualNonexceptionalInverse Grad.RawCircularSectors

/-- ER's actual vector inverse of R-J. Its resonances are the equivariant
helicities at +1 and -1; all other physical modes are retained. -/
def covariantAngularInverse : ClosedJet 2 →ₗ[ℂ] ClosedJet 2 :=
  (shiftInverseLinear 2 (-1)).comp (valueMapJetLinear 2 2 positiveHelicity) +
    (shiftInverseLinear 2 1).comp (valueMapJetLinear 2 2 negativeHelicity)

def signedCovariantInverse (sign : ℤ) (field : ClosedJet 2) : ClosedJet 2 :=
  shiftInverseJet (-sign) (valueMapJet (helicityValue sign) field)

theorem covariantAngularInverse_eq (field : ClosedJet 2) :
    covariantAngularInverse field = signedCovariantInverse 1 field +
      signedCovariantInverse (-1) field := by
  simp only [signedCovariantInverse, helicityValue_positive, helicityValue_negative, neg_neg]
  rfl

theorem helicityJet_commute_quarter (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (field : ClosedJet 2) :
    valueMapJet (helicityValue sign) (valueMapJet quarterValueMap field) =
      valueMapJet quarterValueMap (valueMapJet (helicityValue sign) field) := by
  rcases signed with rfl | rfl
  · simp only [helicityValue_positive, valueMapJet_comp, quarter_positive_commute]
  · simp only [helicityValue_negative, valueMapJet_comp, quarter_negative_commute]

theorem signedCovariantInverse_quarter (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (field : ClosedJet 2) :
    valueMapJet quarterValueMap (signedCovariantInverse sign field) =
      (Complex.I * (sign : ℂ)) • signedCovariantInverse sign field := by
  rw [signedCovariantInverse, ← shiftInverseJet_valueMap, helicityJet_quarter sign signed]
  exact map_smul (shiftInverseLinear 2 (-sign)) _ _

theorem signedCovariantInverse_right (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (field : ClosedJet 2) :
    rotationJet (signedCovariantInverse sign field) -
      valueMapJet quarterValueMap (signedCovariantInverse sign field) =
        valueMapJet (helicityValue sign) field -
          angularClosedJet sign (valueMapJet (helicityValue sign) field) := by
  rw [signedCovariantInverse_quarter sign signed]
  have shifted := shiftInverse_right (-sign) (valueMapJet (helicityValue sign) field)
  rw [excluded_single_eq] at shifted
  simpa only [shiftedRotationJet, Int.cast_neg, mul_neg, neg_smul, sub_eq_add_neg,
    neg_neg, signedCovariantInverse] using shifted

theorem signedCovariantInverse_left (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (field : ClosedJet 2) :
    signedCovariantInverse sign (rotationJet field - valueMapJet quarterValueMap field) =
      valueMapJet (helicityValue sign) field -
        angularClosedJet sign (valueMapJet (helicityValue sign) field) := by
  have quarter := (helicityJet_commute_quarter sign signed field).trans
    (helicityJet_quarter sign signed field)
  have shifted := shiftInverse_left (-sign) (valueMapJet (helicityValue sign) field)
  rw [excluded_single_eq] at shifted
  change shiftInverseJet (-sign)
    ((valueMapJetLinear 2 2 (helicityValue sign)) (_ - _)) = _
  rw [map_sub]
  change shiftInverseJet (-sign) (valueMapJet (helicityValue sign) (rotationJet field) -
    valueMapJet (helicityValue sign) (valueMapJet quarterValueMap field)) = _
  rw [quarter, ← rotationJet_valueMap]
  simpa only [shiftedRotationJet, Int.cast_neg, mul_neg, neg_smul, sub_eq_add_neg,
    neg_neg] using shifted

theorem helicityJet_sum (field : ClosedJet 2) :
    valueMapJet (helicityValue 1) field + valueMapJet (helicityValue (-1)) field = field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simpa only [closedJet_value_add, ContinuousMap.add_apply, valueMapJet_value] using
    helicityValue_sum (field.value point)

theorem covariantAngularInverse_right (field : ClosedJet 2) :
    rotationJet (covariantAngularInverse field) -
      valueMapJet quarterValueMap (covariantAngularInverse field) =
        field - equivariantAverageJet field := by
  rw [covariantAngularInverse_eq, rotationJet_add, valueMapJet_add]
  have first := signedCovariantInverse_right 1 (Or.inl rfl) field
  have second := signedCovariantInverse_right (-1) (Or.inr rfl) field
  have total := helicityJet_sum field
  have projection : angularClosedJet 1 (valueMapJet (helicityValue 1) field) +
      angularClosedJet (-1) (valueMapJet (helicityValue (-1)) field) =
        equivariantAverageJet field := by
    simp only [helicityValue_positive, helicityValue_negative, angularClosedJet_valueMap,
      equivariantAverageJet_eq]
  calc
    _ = (rotationJet (signedCovariantInverse 1 field) - valueMapJet quarterValueMap
        (signedCovariantInverse 1 field)) + (rotationJet (signedCovariantInverse (-1) field) -
          valueMapJet quarterValueMap (signedCovariantInverse (-1) field)) := by module
    _ = _ := by
      rw [first, second]
      exact (sub_add_sub_comm _ _ _ _).trans (congrArg₂ Sub.sub total projection)

theorem covariantAngularInverse_left (field : ClosedJet 2) :
    covariantAngularInverse (rotationJet field - valueMapJet quarterValueMap field) =
      field - equivariantAverageJet field := by
  rw [covariantAngularInverse_eq, signedCovariantInverse_left 1 (Or.inl rfl),
    signedCovariantInverse_left (-1) (Or.inr rfl)]
  have total := helicityJet_sum field
  have projection : angularClosedJet 1 (valueMapJet (helicityValue 1) field) +
      angularClosedJet (-1) (valueMapJet (helicityValue (-1)) field) =
        equivariantAverageJet field := by
    simp only [helicityValue_positive, helicityValue_negative, angularClosedJet_valueMap,
      equivariantAverageJet_eq]
  exact (sub_add_sub_comm _ _ _ _).trans (congrArg₂ Sub.sub total projection)

end Grad.CartesianUncompressed

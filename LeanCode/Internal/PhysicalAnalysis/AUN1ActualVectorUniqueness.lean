import ANV13ReconstructionConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.ActualReconstructionUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Envelope
open Grad.ActualAngularInverse Grad.ActualNonexceptionalInverse
variable {L sigma gamma ell : ℝ}

theorem apHelicity_quarter_commute (admissible : Admissible L sigma gamma ell)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (field : APSmooth L sigma gamma ell 2) :
    apHelicity L sigma gamma ell sign (apSmoothQuarter L sigma gamma ell field) =
      apSmoothQuarter L sigma gamma ell (apHelicity L sigma gamma ell sign field) := by
  have commuting : (helicityValue sign).comp quarterValueMap = quarterValueMap.comp (helicityValue sign) := by
    rcases signed with rfl | rfl
    · rw [helicityValue_positive]
      exact quarter_positive_commute.symm
    · rw [helicityValue_negative]
      exact quarter_negative_commute.symm
  apply apSmoothJet_ext admissible
  intro cell
  have first := (apSmoothValueMap_jet admissible (helicityValue sign) (apSmoothQuarter L sigma gamma ell field) cell).trans
    (congrArg (valueMapJet (helicityValue sign)) (apSmoothValueMap_jet admissible quarterValueMap field cell))
  have second := (apSmoothValueMap_jet admissible quarterValueMap (apHelicity L sigma gamma ell sign field) cell).trans
    (congrArg (valueMapJet quarterValueMap) (apSmoothValueMap_jet admissible (helicityValue sign) field cell))
  have closed : valueMapJet (helicityValue sign) (valueMapJet quarterValueMap (apSmoothJet admissible 2 cell field)) =
      valueMapJet quarterValueMap (valueMapJet (helicityValue sign) (apSmoothJet admissible 2 cell field)) := by
    rw [valueMapJet_comp, valueMapJet_comp, commuting]
  exact first.trans (closed.trans second.symm)

theorem apHelicity_vectorRotation (admissible : Admissible L sigma gamma ell)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (field : APSmooth L sigma gamma ell 2) :
    apHelicity L sigma gamma ell sign (vectorRotation admissible field) =
      apShiftedRotation admissible 2 sign (apHelicity L sigma gamma ell sign field) := by
  have rotation := (apSmoothRotation_valueMap admissible (helicityValue sign) field).symm
  have quarter := (apHelicity_quarter_commute admissible sign signed field).trans
    (apHelicity_quarter admissible sign signed field)
  exact (map_add (apHelicity L sigma gamma ell sign) (apSmoothRotation admissible 2 field)
    (apSmoothQuarter L sigma gamma ell field)).trans
      (congrArg₂ (fun first second : APSmooth L sigma gamma ell 2 => first + second) rotation quarter)

/-- Uniqueness for the actual Cartesian operator R+J on its genuine helicity
nonresonant subspace, using the accepted original angular inverses. -/
theorem apVectorInverse_unique (admissible : Admissible L sigma gamma ell)
    (source candidate : APSmooth L sigma gamma ell 2)
    (nonresonant : VectorNonresonant admissible candidate)
    (equation : vectorRotation admissible candidate = source) :
    candidate = apVectorInverse admissible source := by
  have component (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
      (excluded : APNonresonant admissible sign (apHelicity L sigma gamma ell sign candidate)) :
      apHelicity L sigma gamma ell sign candidate = apSignedInverse admissible sign source :=
    apShiftInverse_unique admissible sign (apHelicity L sigma gamma ell sign source) _ excluded
      ((apHelicity_vectorRotation admissible sign signed candidate).symm.trans
        (congrArg (apHelicity L sigma gamma ell sign) equation))
  exact (apHelicity_sum admissible candidate).symm.trans
    (congrArg₂ (fun first second : APSmooth L sigma gamma ell 2 => first + second)
      (component 1 (Or.inl rfl) nonresonant.1) (component (-1) (Or.inr rfl) nonresonant.2))

end Grad.ActualReconstructionUniqueness

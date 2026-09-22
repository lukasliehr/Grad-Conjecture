import GQF5RadialProjection

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.GaugeTransfer

variable {L sigma gamma ell : ℝ}

theorem apSmoothQuarter_square (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 2) :
    apSmoothQuarter L sigma gamma ell (apSmoothQuarter L sigma gamma ell field) = -field := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothValueMap_jet admissible quarterValueMap
    (apSmoothQuarter L sigma gamma ell field) cell).trans
    ((congrArg (valueMapJet quarterValueMap)
      (apSmoothValueMap_jet admissible quarterValueMap field cell)).trans
      ((quarterJet_square _).trans (map_neg (apSmoothJet admissible 2 cell) field).symm))

theorem apSmoothTangential_idempotent (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 2) :
    apSmoothTangential L sigma gamma ell (apSmoothTangential L sigma gamma ell field) =
      apSmoothTangential L sigma gamma ell field := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothTangential_jet admissible _ cell).trans
    ((congrArg tangentialJet (apSmoothTangential_jet admissible field cell)).trans
      ((tangentialJet_idempotent _).trans (apSmoothTangential_jet admissible field cell).symm))

theorem radialCancellation_algebra {E : Type*} [AddCommGroup E] [Module ℂ E]
    (J T : E →ₗ[ℂ] E) (square : ∀ field, J (J field) = -field)
    (fixed : ∀ field, T (T field) = T field) (field : E) :
    J (T field) + J (T (J (J (T field)))) = 0 := by
  rw [square, map_neg, fixed, map_neg, add_neg_cancel]

theorem apSmoothQrad_quarter_tangential (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 2) :
    apSmoothQrad L sigma gamma ell
      (apSmoothQuarter L sigma gamma ell (apSmoothTangential L sigma gamma ell field)) = 0 := by
  exact radialCancellation_algebra (apSmoothQuarter L sigma gamma ell)
    (apSmoothTangential L sigma gamma ell) (apSmoothQuarter_square admissible)
      (apSmoothTangential_idempotent admissible) field

theorem planarComplement_jet (field : ClosedJet 3) :
    valueMapJet planarPartMap (fixedComplementJet field) =
      tangentialJet (valueMapJet planarPartMap field) := by
  change valueMapJet planarPartMap (valueMapJet planarInclusionMap
    (tangentialJet (valueMapJet planarPartMap field)) + valueMapJet toroidalInclusionMap
      (angularClosedJet 0 (valueMapJet toroidalPartMap field))) = _
  rw [valueMapJet_add, valueMapJet_comp, valueMapJet_comp,
    planarPart_planarInclusion, planarPart_toroidalInclusion, valueMapJet_zero, add_zero]
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  exact valueMapJet_value _ _ _

theorem scalarComplement_jet (field : ClosedJet 3) :
    valueMapJet toroidalPartMap (fixedComplementJet field) =
      angularClosedJet 0 (valueMapJet toroidalPartMap field) := by
  change valueMapJet toroidalPartMap (valueMapJet planarInclusionMap
    (tangentialJet (valueMapJet planarPartMap field)) + valueMapJet toroidalInclusionMap
      (angularClosedJet 0 (valueMapJet toroidalPartMap field))) = _
  rw [valueMapJet_add, valueMapJet_comp, valueMapJet_comp,
    toroidalPart_planarInclusion, toroidalPart_toroidalInclusion, valueMapJet_zero, zero_add]
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  exact valueMapJet_value _ _ _

theorem apSmoothPlanar_complement (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 3) :
    apSmoothPlanar L sigma gamma ell (apSmoothComplement L sigma gamma ell field) =
      apSmoothTangential L sigma gamma ell (apSmoothPlanar L sigma gamma ell field) := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothValueMap_jet admissible planarPartMap _ cell).trans
    ((congrArg (valueMapJet planarPartMap) (apSmoothComplement_jet admissible field cell)).trans
      ((planarComplement_jet _).trans
        ((congrArg tangentialJet (apSmoothValueMap_jet admissible planarPartMap field cell).symm).trans
          (apSmoothTangential_jet admissible _ cell).symm)))

theorem apSmoothScalar_complement (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 3) :
    apSmoothScalar L sigma gamma ell (apSmoothComplement L sigma gamma ell field) =
      apSmoothAngularMean L sigma gamma ell 1 (apSmoothScalar L sigma gamma ell field) := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothValueMap_jet admissible toroidalPartMap _ cell).trans
    ((congrArg (valueMapJet toroidalPartMap) (apSmoothComplement_jet admissible field cell)).trans
      ((scalarComplement_jet _).trans
        ((congrArg (angularClosedJet 0) (apSmoothValueMap_jet admissible toroidalPartMap field cell).symm).trans
          (apSmoothAngularMean_jet admissible _ cell).symm)))

theorem apSmoothRotation_tangential (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 2) :
    apSmoothRotation admissible 2 (apSmoothTangential L sigma gamma ell field) =
      apSmoothQuarter L sigma gamma ell (apSmoothTangential L sigma gamma ell field) := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothRotation_jet admissible _ cell).trans
    ((congrArg Grad.NonlinearRange.rotationJet (apSmoothTangential_jet admissible field cell)).trans
      ((rotationJet_tangential _).trans
        ((congrArg (valueMapJet quarterValueMap) (apSmoothTangential_jet admissible field cell).symm).trans
          (apSmoothValueMap_jet admissible quarterValueMap _ cell).symm)))

theorem apSmoothRotation_mean_zero (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (field : APSmooth L sigma gamma ell dimension) :
    apSmoothRotation admissible dimension (apSmoothAngularMean L sigma gamma ell dimension field) = 0 := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothRotation_jet admissible _ cell).trans
    ((congrArg Grad.NonlinearRange.rotationJet (apSmoothAngularMean_jet admissible field cell)).trans
      ((rotationJet_angular_zero _).trans (map_zero (apSmoothJet admissible dimension cell)).symm))

end Grad.GaugeCoefficients.Physical.Compensated

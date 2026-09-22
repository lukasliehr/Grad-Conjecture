import GQF16AxisStability

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.NonlinearDivision

def planarCurlLinear : ClosedJet 2 →ₗ[ℂ] ClosedJet 1 :=
  (valueMapJetLinear 2 1 (matrixUnit 0 1)).comp (partialJetLinear 2 0) -
    (valueMapJetLinear 2 1 (matrixUnit 0 0)).comp (partialJetLinear 2 1)

def planarCurlJet (field : ClosedJet 2) : ClosedJet 1 := planarCurlLinear field

theorem planarCurlJet_quarter_planar (field : ClosedJet 3) :
    planarCurlJet (valueMapJet quarterValueMap (valueMapJet planarPartMap field)) = planarDivJet field := by
  change valueMapJet (matrixUnit 0 1) (partialJet 0 (valueMapJet quarterValueMap (valueMapJet planarPartMap field))) -
    valueMapJet (matrixUnit 0 0) (partialJet 1 (valueMapJet quarterValueMap (valueMapJet planarPartMap field))) = _
  rw [partialJet_valueMap, partialJet_valueMap, partialJet_valueMap, partialJet_valueMap]
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  simp [planarDivJet, sub_eq_add_neg, closedJet_value_add, closedJet_value_neg,
    valueMapJet_value, quarterValueMap, quarterValueLinear, planarPartMap, matrixUnit_apply, operatorBasis]

theorem planarCurlJet_quarter_tangential (field : ClosedJet 2) :
    planarCurlJet (valueMapJet quarterValueMap (tangentialJet field)) = 0 := by
  have representation := congrArg (fun jet => planarCurlJet (valueMapJet quarterValueMap jet))
    (planarComplement_planar field).symm
  exact representation.trans ((planarCurlJet_quarter_planar _).trans (planarDivJet_complement_zero _))

theorem tangentialJet_origin_zero (field : ClosedJet 2) :
    (tangentialJet field).value closedOrigin = 0 :=
  (closedTangentialValue_jet field closedOrigin).symm.trans (closedTangentialValue_origin field.value)

variable {L sigma gamma ell : ℝ}

theorem apSmoothCurl_jet (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 2) (cell : ℤ) :
    apSmoothJet admissible 1 cell (apSmoothCurl admissible field) =
      planarCurlJet (apSmoothJet admissible 2 cell field) := by
  have first := (apSmoothValueMap_jet admissible (matrixUnit (input := 2) (output := 1) 0 1)
    (apSmoothPartial admissible 2 0 field) cell).trans
    (congrArg (valueMapJet (matrixUnit (input := 2) (output := 1) 0 1))
      (apSmoothPartial_jet admissible field 0 cell))
  have second := (apSmoothValueMap_jet admissible (matrixUnit (input := 2) (output := 1) 0 0)
    (apSmoothPartial admissible 2 1 field) cell).trans
    (congrArg (valueMapJet (matrixUnit (input := 2) (output := 1) 0 0))
      (apSmoothPartial_jet admissible field 1 cell))
  exact (map_sub (apSmoothJet admissible 1 cell) _ _).trans
    (congrArg₂ (fun first second : ClosedJet 1 => first - second) first second)

theorem apSmoothQuarterTangential_jet (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 2) (cell : ℤ) :
    apSmoothJet admissible 2 cell (apSmoothQuarter L sigma gamma ell
      (apSmoothTangential L sigma gamma ell field)) =
        valueMapJet quarterValueMap (tangentialJet (apSmoothJet admissible 2 cell field)) :=
  (apSmoothValueMap_jet admissible quarterValueMap _ cell).trans
    (congrArg (valueMapJet quarterValueMap) (apSmoothTangential_jet admissible field cell))

theorem apSmoothCurl_quarter_tangential (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 2) :
    apSmoothCurl admissible (apSmoothQuarter L sigma gamma ell
      (apSmoothTangential L sigma gamma ell field)) = 0 := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothCurl_jet admissible _ cell).trans
    ((congrArg planarCurlJet (apSmoothQuarterTangential_jet admissible field cell)).trans
      ((planarCurlJet_quarter_tangential _).trans (map_zero (apSmoothJet admissible 1 cell)).symm))

/-- Qrad leaves the actual Cartesian curl unchanged on the full disk. -/
theorem apSmoothCurl_Qrad (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 2) :
    apSmoothCurl admissible (apSmoothQrad L sigma gamma ell field) = apSmoothCurl admissible field := by
  have expand : apSmoothQrad L sigma gamma ell field = field + apSmoothQuarter L sigma gamma ell
    (apSmoothTangential L sigma gamma ell (apSmoothQuarter L sigma gamma ell field)) := rfl
  exact (congrArg (apSmoothCurl admissible) expand).trans
    ((map_add (apSmoothCurl admissible) field _).trans
      ((congrArg (fun value : APSmooth L sigma gamma ell 1 => apSmoothCurl admissible field + value)
        (apSmoothCurl_quarter_tangential admissible (apSmoothQuarter L sigma gamma ell field))).trans (add_zero _)))

theorem apSmoothQrad_origin (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 2) (cell : ℤ) :
    (apSmoothJet admissible 2 cell (apSmoothQrad L sigma gamma ell field)).value closedOrigin =
      (apSmoothJet admissible 2 cell field).value closedOrigin := by
  have expand : apSmoothQrad L sigma gamma ell field = field + apSmoothQuarter L sigma gamma ell
    (apSmoothTangential L sigma gamma ell (apSmoothQuarter L sigma gamma ell field)) := rfl
  let evaluation : APSmooth L sigma gamma ell 2 →ₗ[ℂ] ComplexEuclidean 2 :=
    ((ContinuousMap.evalCLM ℂ closedOrigin).toLinearMap.comp (jetValueLinear 2)).comp
      (apSmoothJet admissible 2 cell)
  have correction := congrArg (fun jet : ClosedJet 2 => jet.value closedOrigin)
    (apSmoothQuarterTangential_jet admissible (apSmoothQuarter L sigma gamma ell field) cell)
  have zero := correction.trans ((valueMapJet_value quarterValueMap _ closedOrigin).trans
    ((congrArg quarterValueMap (tangentialJet_origin_zero _)).trans (map_zero quarterValueMap)))
  exact (congrArg evaluation expand).trans ((map_add evaluation field _).trans
    ((congrArg (fun value : ComplexEuclidean 2 => evaluation field + value) zero).trans (add_zero _)))

end Grad.GaugeCoefficients.Physical.Compensated

import ASX13RegularSecondMode
import ANM3ExplicitMeanState

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.ActualExceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.NonlinearProduct Grad.NonlinearRadial Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.ActualCenterVolterra Grad.FlatSourceProjection Grad.ActualMeanInverse
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra

/-- The actual Cartesian gradient has the specified signed scalar component. -/
theorem spinJet_gradient (sign : ℤ) (field : ClosedJet 1) :
    valueMapJet (spinValue (sign : ℂ)) (gradientJet field) = signedLowering (-sign) field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  change (valueMapJet (spinValue (sign : ℂ)) (gradientJet field)).value point 0 =
    (signedLowering (-sign) field).value point 0
  simp [valueMapJet_value, spinValue_apply, gradientJet_value, signedLowering,
    centerDifferential, sub_eq_add_neg, closedJet_value_add,
    closedJet_value_smul, originalPartial_eq, mul_comm]

theorem spinJet_quarter (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (field : ClosedJet 2) :
    valueMapJet (spinValue (sign : ℂ)) (valueMapJet quarterValueMap field) =
      (Complex.I * (sign : ℂ)) • valueMapJet (spinValue (sign : ℂ)) field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  rcases signed with rfl | rfl <;>
    simp [valueMapJet_value, spinValue_apply, quarterValueMap, quarterValueLinear,
      closedJet_value_smul] <;> ring_nf <;> simp [Complex.I_sq]

theorem smoothSpin_jet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (sign : ℤ) (field : APSmooth L sigma gamma ell 2) (cell : ℤ) :
    apSmoothJet admissible 1 cell (smoothSpin L sigma gamma ell sign field) =
      valueMapJet (spinValue (sign : ℂ)) (apSmoothJet admissible 2 cell field) :=
  apSmoothValueMap_jet admissible (spinValue (sign : ℂ)) field cell

theorem smoothSpin_gradient {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (sign : ℤ) (field : APSmooth L sigma gamma ell 1) :
    smoothSpin L sigma gamma ell sign (apSmoothGradient admissible field) =
      smoothSignedDerivative admissible 1 (-sign) field := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (smoothSpin_jet admissible sign (apSmoothGradient admissible field) cell).trans
    ((congrArg (valueMapJet (spinValue (sign : ℂ))) (apSmoothGradient_jet admissible field cell)).trans
      ((spinJet_gradient sign (apSmoothJet admissible 1 cell field)).trans
        (smoothSignedDerivative_jet admissible (-sign) field cell).symm))

theorem smoothSpin_quarter {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (field : APSmooth L sigma gamma ell 2) :
    smoothSpin L sigma gamma ell sign (apSmoothQuarter L sigma gamma ell field) =
      (Complex.I * (sign : ℂ)) • smoothSpin L sigma gamma ell sign field := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (smoothSpin_jet admissible sign (apSmoothQuarter L sigma gamma ell field) cell).trans
    ((congrArg (valueMapJet (spinValue (sign : ℂ))) (apSmoothValueMap_jet admissible quarterValueMap field cell)).trans
      ((spinJet_quarter sign signed (apSmoothJet admissible 2 cell field)).trans
        ((congrArg (fun jet : ClosedJet 1 => (Complex.I * (sign : ℂ)) • jet)
          (smoothSpin_jet admissible sign field cell).symm).trans
            ((apSmoothJet admissible 1 cell).map_smul (Complex.I * (sign : ℂ))
              (smoothSpin L sigma gamma ell sign field)).symm)))

theorem smoothSpin_planar_first {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (first second : APSmooth L sigma gamma ell 1) :
    smoothSpin L sigma gamma ell sign (smoothPlanarFromSpins L sigma gamma ell sign first second) = first := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (smoothSpin_jet admissible sign (smoothPlanarFromSpins L sigma gamma ell sign first second) cell).trans
    ((congrArg (valueMapJet (spinValue (sign : ℂ))) (smoothPlanarFromSpins_jet admissible sign first second cell)).trans
      (planarFromSpins_first sign signed _ _))

theorem smoothSpin_planar_second {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (first second : APSmooth L sigma gamma ell 1) :
    smoothSpin L sigma gamma ell (-sign) (smoothPlanarFromSpins L sigma gamma ell sign first second) = second := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (smoothSpin_jet admissible (-sign) (smoothPlanarFromSpins L sigma gamma ell sign first second) cell).trans
    ((congrArg (valueMapJet (spinValue ((-sign : ℤ) : ℂ))) (smoothPlanarFromSpins_jet admissible sign first second cell)).trans
      (planarFromSpins_second sign signed _ _))

theorem smoothValueMap_comp {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input middle output : ℕ} (first : ComplexEuclidean input →L[ℂ] ComplexEuclidean middle)
    (second : ComplexEuclidean middle →L[ℂ] ComplexEuclidean output) (field : APSmooth L sigma gamma ell input) :
    apSmoothValueMap L sigma gamma ell second (apSmoothValueMap L sigma gamma ell first field) =
      apSmoothValueMap L sigma gamma ell (second.comp first) field := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothValueMap_jet admissible second (apSmoothValueMap L sigma gamma ell first field) cell).trans
    ((congrArg (valueMapJet second) (apSmoothValueMap_jet admissible first field cell)).trans
      ((valueMapJet_comp first second (apSmoothJet admissible input cell field)).trans
        (apSmoothValueMap_jet admissible (second.comp first) field cell).symm))

theorem smoothValueMap_identity {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (field : APSmooth L sigma gamma ell dimension) :
    apSmoothValueMap L sigma gamma ell (ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)) field = field := by
  apply apSmoothJet_ext admissible
  intro cell
  apply (apSmoothValueMap_jet admissible _ field cell).trans
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  exact valueMapJet_value _ _ _

theorem smoothValueMap_zero {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (field : APSmooth L sigma gamma ell input) :
    apSmoothValueMap L sigma gamma ell (0 : ComplexEuclidean input →L[ℂ] ComplexEuclidean output) field = 0 := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothValueMap_jet admissible 0 field cell).trans
    ((valueMapJet_zero _).trans (map_zero (apSmoothJet admissible output cell)).symm)

end Grad.ActualExceptionalInverse

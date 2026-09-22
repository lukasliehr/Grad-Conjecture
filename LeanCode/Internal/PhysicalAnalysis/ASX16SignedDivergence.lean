import ASX15ActualStateComponents

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.ActualExceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.NonlinearRange Grad.NonlinearQuotientBounds Grad.ActualCenterVolterra Grad.FlatSourceProjection
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Frame

/-- The genuine planar divergence is the sum of the two signed Cartesian derivatives. -/
theorem planarDivJet_spins (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (field : ClosedJet 3) :
    planarDivJet field = (1 / 2 : ℂ) •
      (signedLowering sign (valueMapJet (spinValue (sign : ℂ)) (valueMapJet planarPartMap field)) +
       signedLowering (-sign) (valueMapJet (spinValue ((-sign : ℤ) : ℂ)) (valueMapJet planarPartMap field))) := by
  simp only [signedLowering, centerDifferential, ← originalPartial_eq, partialJet_valueMap]
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  change (planarDivJet field).value point 0 = _
  rcases signed with rfl | rfl <;>
    simp [planarDivJet_value, sub_eq_add_neg, closedJet_value_add, closedJet_value_neg,
      closedJet_value_smul, valueMapJet_value, spinValue_apply, planarPartMap] <;>
    ring_nf <;> simp [Complex.I_sq]

private theorem evaluate_three {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (evaluate : E →ₗ[ℂ] F) (first second third : E) :
    evaluate ((1 / 2 : ℂ) • (first + second) + third) =
      (1 / 2 : ℂ) • (evaluate first + evaluate second) + evaluate third := by
  simp only [map_add, map_smul]

/-- Exact divergence on the existing AP smooth carrier, retaining the original axial scaling. -/
theorem smoothDiv_spins {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (field : APSmooth L sigma gamma ell 3) :
    apSmoothDiv admissible field = (1 / 2 : ℂ) •
      (smoothSignedDerivative admissible 1 sign (smoothSpin L sigma gamma ell sign (apSmoothPlanar L sigma gamma ell field)) +
       smoothSignedDerivative admissible 1 (-sign) (smoothSpin L sigma gamma ell (-sign) (apSmoothPlanar L sigma gamma ell field))) +
      apSmoothAxial L sigma gamma ell 1 (apSmoothScalar L sigma gamma ell field) := by
  apply apSmoothJet_ext admissible
  intro cell
  have spin (direction : ℤ) := (smoothSpin_jet admissible direction (apSmoothPlanar L sigma gamma ell field) cell).trans
    (congrArg (valueMapJet (spinValue (direction : ℂ))) (apSmoothValueMap_jet admissible planarPartMap field cell))
  have derivative (direction : ℤ) := (smoothSignedDerivative_jet admissible direction
    (smoothSpin L sigma gamma ell direction (apSmoothPlanar L sigma gamma ell field)) cell).trans
      (congrArg (signedLowering direction) (spin direction))
  have axial := (apSmoothAxial_jet admissible (apSmoothScalar L sigma gamma ell field) cell).trans
    (congrArg (fun jet : ClosedJet 1 => seedScaledFrequency L ell cell • jet)
      (apSmoothValueMap_jet admissible toroidalPartMap field cell))
  have right := (evaluate_three (apSmoothJet admissible 1 cell)
    (smoothSignedDerivative admissible 1 sign (smoothSpin L sigma gamma ell sign (apSmoothPlanar L sigma gamma ell field)))
    (smoothSignedDerivative admissible 1 (-sign) (smoothSpin L sigma gamma ell (-sign) (apSmoothPlanar L sigma gamma ell field)))
    (apSmoothAxial L sigma gamma ell 1 (apSmoothScalar L sigma gamma ell field))).trans
      (congrArg₂ (fun first second : ClosedJet 1 => first + second)
        (congrArg (fun jet : ClosedJet 1 => (1 / 2 : ℂ) • jet)
          (congrArg₂ (fun first second : ClosedJet 1 => first + second) (derivative sign) (derivative (-sign)))) axial)
  exact (apSmoothDiv_jet admissible field cell).trans
    ((congrArg (fun jet : ClosedJet 1 => jet + seedScaledFrequency L ell cell •
      valueMapJet toroidalPartMap (apSmoothJet admissible 3 cell field))
      (planarDivJet_spins sign signed (apSmoothJet admissible 3 cell field))).trans right.symm)

private theorem forcing_cancellation {E : Type*} [AddCommGroup E] [Module ℂ E]
    (source axial fixed free : E) (equation : free = (-2 : ℂ) • source + (-2 : ℂ) • axial - fixed) :
    (1 / 2 : ℂ) • (fixed + free) + axial = -source := by
  rw [equation]
  module

/-- The literal divergence row of the constructed state follows from the genuine signed primitive equation. -/
theorem exceptionalState_divergence {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (primitive : smoothSignedDerivative admissible 1 (-sign) (exceptionalFreeSpin admissible sign source) =
      exceptionalFreeForcing admissible sign source) :
    apSmoothDiv admissible (compensatedReconstruct admissible (exceptionalState admissible sign source)) = -source.2.1 := by
  have components := (smoothDiv_spins admissible sign signed (exceptionalCovariant admissible sign source))
  have first := congrArg (smoothSignedDerivative admissible 1 sign)
    ((congrArg (smoothSpin L sigma gamma ell sign) (exceptionalCovariant_planar admissible sign source)).trans
      (exceptionalPlanar_first admissible sign signed source))
  have second := congrArg (smoothSignedDerivative admissible 1 (-sign))
    ((congrArg (smoothSpin L sigma gamma ell (-sign)) (exceptionalCovariant_planar admissible sign source)).trans
      (exceptionalPlanar_second admissible sign signed source))
  have axial := congrArg (apSmoothAxial L sigma gamma ell 1) (exceptionalCovariant_scalar admissible sign source)
  have row := components.trans (congrArg₂ (fun first second : APSmooth L sigma gamma ell 1 => first + second)
    (congrArg (fun value : APSmooth L sigma gamma ell 1 => (1 / 2 : ℂ) • value)
      (congrArg₂ (fun a b : APSmooth L sigma gamma ell 1 => a + b) first second)) axial)
  exact (congrArg (apSmoothDiv admissible) (exceptionalState_reconstruct admissible sign source)).trans
    (row.trans (forcing_cancellation source.2.1 _ _ _ primitive))

end Grad.ActualExceptionalInverse

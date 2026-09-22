import ASX10ActualExceptionalState

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.ActualExceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct Grad.NonlinearRadial
open Grad.Constraints.Gauges
open Grad.ActualCenterVolterra Grad.NonlinearQuotientBounds Grad.FlatSourceProjection
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Physical.Ledger

def planarFromSpins (sign : ℤ) (first second : ClosedJet 1) : ClosedJet 2 :=
  (1 / 2 : ℂ) • valueMapJet (matrixUnit (input := 1) (output := 2) 0 0) (first + second) +
    (2 * Complex.I * (sign : ℂ))⁻¹ • valueMapJet (matrixUnit (input := 1) (output := 2) 1 0) (first - second)

theorem signedCast_nonzero (sign : ℤ) (signed : sign = 1 ∨ sign = -1) : (sign : ℂ) ≠ 0 := by
  rcases signed with rfl | rfl <;> norm_num

theorem planarFromSpins_first (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (first second : ClosedJet 1) :
    valueMapJet (spinValue (sign : ℂ)) (planarFromSpins sign first second) = first := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  simp [planarFromSpins, valueMapJet_value, spinValue_apply, matrixUnit_apply, operatorBasis,
    closedJet_value_add, closedJet_value_smul, closedJet_value_neg, sub_eq_add_neg]
  field_simp [signedCast_nonzero sign signed, Complex.I_ne_zero]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem planarFromSpins_second (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (first second : ClosedJet 1) :
    valueMapJet (spinValue ((-sign : ℤ) : ℂ)) (planarFromSpins sign first second) = second := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  simp [planarFromSpins, valueMapJet_value, spinValue_apply, matrixUnit_apply, operatorBasis,
    closedJet_value_add, closedJet_value_smul, closedJet_value_neg, sub_eq_add_neg]
  field_simp [signedCast_nonzero sign signed, Complex.I_ne_zero]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem planarFromSpins_reconstruct (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (field : ClosedJet 2) :
    planarFromSpins sign (valueMapJet (spinValue (sign : ℂ)) field)
      (valueMapJet (spinValue ((-sign : ℤ) : ℂ)) field) = field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [planarFromSpins, valueMapJet_value, spinValue_apply, matrixUnit_apply, operatorBasis,
      closedJet_value_add, closedJet_value_smul, closedJet_value_neg, sub_eq_add_neg] <;>
    field_simp [signedCast_nonzero sign signed, Complex.I_ne_zero] <;> ring_nf
  simp only [Complex.I_sq]
  ring

theorem spinJet_ext (sign : ℤ) (signed : sign = 1 ∨ sign = -1) {first second : ClosedJet 2}
    (positive : valueMapJet (spinValue (sign : ℂ)) first = valueMapJet (spinValue (sign : ℂ)) second)
    (negative : valueMapJet (spinValue ((-sign : ℤ) : ℂ)) first = valueMapJet (spinValue ((-sign : ℤ) : ℂ)) second) :
    first = second :=
  (planarFromSpins_reconstruct sign signed first).symm.trans
    ((congrArg₂ (planarFromSpins sign) positive negative).trans (planarFromSpins_reconstruct sign signed second))

private theorem linear_reconstruction {E F G : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] [AddCommGroup G] [Module ℂ G]
    (project : F →ₗ[ℂ] G) (left right : E →ₗ[ℂ] F) (coefficient : ℂ) (first second : E) :
    project ((1 / 2 : ℂ) • left (first + second) + coefficient • right (first - second)) =
      (1 / 2 : ℂ) • project (left (first + second)) + coefficient • project (right (first - second)) := by
  rw [map_add, map_smul, map_smul]

theorem smoothPlanarFromSpins_jet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (sign : ℤ) (first second : APSmooth L sigma gamma ell 1) (cell : ℤ) :
    apSmoothJet admissible 2 cell (smoothPlanarFromSpins L sigma gamma ell sign first second) =
      planarFromSpins sign (apSmoothJet admissible 1 cell first) (apSmoothJet admissible 1 cell second) := by
  let left := matrixUnit (input := 1) (output := 2) 0 0
  let right := matrixUnit (input := 1) (output := 2) 1 0
  have leftValue := (apSmoothValueMap_jet admissible left (first + second) cell).trans
    (congrArg (valueMapJet left) ((apSmoothJet admissible 1 cell).map_add first second))
  have rightValue := (apSmoothValueMap_jet admissible right (first - second) cell).trans
    (congrArg (valueMapJet right) ((apSmoothJet admissible 1 cell).map_sub first second))
  exact (linear_reconstruction (apSmoothJet admissible 2 cell)
    (apSmoothValueMap L sigma gamma ell left) (apSmoothValueMap L sigma gamma ell right)
    (2 * Complex.I * (sign : ℂ))⁻¹ first second).trans
      (congrArg₂ (fun a b : ClosedJet 2 => (1 / 2 : ℂ) • a + (2 * Complex.I * (sign : ℂ))⁻¹ • b) leftValue rightValue)

theorem smoothSpin_ext {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) {first second : APSmooth L sigma gamma ell 2}
    (positive : smoothSpin L sigma gamma ell sign first = smoothSpin L sigma gamma ell sign second)
    (negative : smoothSpin L sigma gamma ell (-sign) first = smoothSpin L sigma gamma ell (-sign) second) : first = second := by
  apply apSmoothJet_ext admissible
  intro cell
  apply spinJet_ext sign signed
  · exact (apSmoothValueMap_jet admissible (spinValue (sign : ℂ)) first cell).symm.trans
      ((congrArg (apSmoothJet admissible 1 cell) positive).trans
        (apSmoothValueMap_jet admissible (spinValue (sign : ℂ)) second cell))
  · exact (apSmoothValueMap_jet admissible (spinValue ((-sign : ℤ) : ℂ)) first cell).symm.trans
      ((congrArg (apSmoothJet admissible 1 cell) negative).trans
        (apSmoothValueMap_jet admissible (spinValue ((-sign : ℤ) : ℂ)) second cell))

end Grad.ActualExceptionalInverse

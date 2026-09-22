import ANP4RawVectorAndSource

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.RawCircularSectors
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Algebra Grad.FlatSourceProjection Grad.ActualCenterVolterra

/-- Both actual scalar spins jointly determine a Cartesian vector jet. -/
theorem spinJet_joint_injective {first second : ClosedJet 2}
    (positive : valueMapJet (spinValue 1) first = valueMapJet (spinValue 1) second)
    (negative : valueMapJet (spinValue (-1)) first = valueMapJet (spinValue (-1)) second) : first = second := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have p := congrArg (fun jet : ClosedJet 1 => jet.value point 0) positive
  have n := congrArg (fun jet : ClosedJet 1 => jet.value point 0) negative
  simp only [valueMapJet_value, spinValue_apply, one_mul, neg_one_mul] at p n
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · change first.value point 0 = second.value point 0
    linear_combination (1 / 2 : ℂ) * p + (1 / 2 : ℂ) * n
  · change first.value point 1 = second.value point 1
    have equal : Complex.I * (first.value point 1 - second.value point 1) = 0 := by
      linear_combination (1 / 2 : ℂ) * p - (1 / 2 : ℂ) * n
    exact sub_eq_zero.mp ((mul_eq_zero.mp equal).resolve_left Complex.I_ne_zero)

theorem spin_gradientJet (sign : ℤ) (field : ClosedJet 1) :
    valueMapJet (spinValue (sign : ℂ)) (gradientJet field) = centerDifferential (-sign) field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  change (valueMapJet (spinValue (sign : ℂ)) (gradientJet field)).value point 0 =
    (centerDifferential (-sign) field).value point 0
  rw [valueMapJet_value, spinValue_apply, gradientJet_value]
  simp only [centerDifferential, sub_eq_add_neg, closedJet_value_add, closedJet_value_neg,
    closedJet_value_smul, ContinuousMap.add_apply, ContinuousMap.neg_apply, ContinuousMap.smul_apply,
    PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul, Int.cast_neg]
  change (partialJet 0 field).value point 0 + (sign : ℂ) * Complex.I * (partialJet 1 field).value point 0 =
    (partialJet 0 field).value point 0 + -((Complex.I * (-(sign : ℂ))) * (partialJet 1 field).value point 0)
  ring

/-- Literal scalar/vector covariance of the Cartesian gradient. -/
theorem gradientJet_angular (mode : ℤ) (field : ClosedJet 1) :
    gradientJet (angularClosedJet mode field) = rawVectorJet mode (gradientJet field) := by
  have spins (sign : ℤ) (signed : sign = 1 ∨ sign = -1) :
      valueMapJet (spinValue (sign : ℂ)) (gradientJet (angularClosedJet mode field)) =
        valueMapJet (spinValue (sign : ℂ)) (rawVectorJet mode (gradientJet field)) := by
    have opposite : -sign = 1 ∨ -sign = -1 := by omega
    calc
      _ = centerDifferential (-sign) (angularClosedJet mode field) := spin_gradientJet sign _
      _ = angularClosedJet (mode + sign) (centerDifferential (-sign) field) := by
        simpa only [sub_neg_eq_add] using centerDifferential_angular (-sign) opposite mode field
      _ = angularClosedJet (mode + sign) (valueMapJet (spinValue (sign : ℂ)) (gradientJet field)) :=
        congrArg (angularClosedJet (mode + sign)) (spin_gradientJet sign field).symm
      _ = _ := (rawVectorJet_spin sign signed mode (gradientJet field)).symm
  exact spinJet_joint_injective (by simpa only [Int.cast_one] using spins 1 (Or.inl rfl))
    (by simpa only [Int.cast_neg, Int.cast_one] using spins (-1) (Or.inr rfl))

theorem differential_spin_value (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (field : ClosedJet 2) (point : ClosedDisk) :
    (centerDifferential sign (valueMapJet (spinValue (sign : ℂ)) field)).value point 0 =
      (partialJet 0 field).value point 0 + (partialJet 1 field).value point 1 +
        Complex.I * (sign : ℂ) * ((partialJet 0 field).value point 1 - (partialJet 1 field).value point 0) := by
  change (partialJet 0 (valueMapJet (spinValue (sign : ℂ)) field) -
    (Complex.I * (sign : ℂ)) • partialJet 1 (valueMapJet (spinValue (sign : ℂ)) field)).value point 0 = _
  rw [partialJet_valueMap, partialJet_valueMap]
  rcases signed with rfl | rfl <;>
    simp [sub_eq_add_neg, closedJet_value_add, closedJet_value_neg, closedJet_value_smul,
      valueMapJet_value, spinValue_apply] <;> ring_nf <;> simp [Complex.I_sq]

/-- Actual Cartesian curl written in the two signed differential spins. -/
theorem planarCurlJet_spin (field : ClosedJet 2) :
    planarCurlJet field = (-Complex.I / 2) •
      (centerDifferential 1 (valueMapJet (spinValue 1) field) -
        centerDifferential (-1) (valueMapJet (spinValue (-1)) field)) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  change (planarCurlJet field).value point 0 = ((-Complex.I / 2) •
    (centerDifferential 1 (valueMapJet (spinValue 1) field) -
      centerDifferential (-1) (valueMapJet (spinValue (-1)) field))).value point 0
  have positive := differential_spin_value 1 (Or.inl rfl) field point
  have negative := differential_spin_value (-1) (Or.inr rfl) field point
  simp only [Int.cast_one, Int.cast_neg, mul_one, mul_neg_one] at positive negative
  simp only [sub_eq_add_neg, closedJet_value_add, closedJet_value_neg, closedJet_value_smul,
    ContinuousMap.add_apply, ContinuousMap.neg_apply, ContinuousMap.smul_apply,
    PiLp.smul_apply, PiLp.add_apply, PiLp.neg_apply, smul_eq_mul]
  rw [positive, negative]
  change (valueMapJet (matrixUnit 0 1) (partialJet 0 field) -
      valueMapJet (matrixUnit 0 0) (partialJet 1 field)).value point 0 = _
  simp [sub_eq_add_neg, closedJet_value_add, closedJet_value_neg, valueMapJet_value, matrixUnit_apply, operatorBasis]
  ring_nf
  simp [Complex.I_sq, sub_eq_add_neg]

/-- Exact curl projection law; in particular the original axis curl constraint
is retained by raw source projections without assuming their first jets vanish. -/
theorem planarCurlJet_rawVector (mode : ℤ) (field : ClosedJet 2) :
    planarCurlJet (rawVectorJet mode field) = angularClosedJet mode (planarCurlJet field) := by
  have positive := rawVectorJet_spin 1 (Or.inl rfl) mode field
  have negative := rawVectorJet_spin (-1) (Or.inr rfl) mode field
  simp only [Int.cast_one] at positive
  simp only [Int.cast_neg, Int.cast_one] at negative
  rw [planarCurlJet_spin, positive, negative]
  rw [centerDifferential_angular 1 (Or.inl rfl), centerDifferential_angular (-1) (Or.inr rfl)]
  have first : mode + 1 - 1 = mode := by omega
  have second : mode + -1 - -1 = mode := by omega
  rw [first, second, planarCurlJet_spin field]
  change (-Complex.I / 2) • (angularClosedJetLinear 1 mode _ - angularClosedJetLinear 1 mode _) =
    angularClosedJetLinear 1 mode ((-Complex.I / 2) • (_ - _))
  rw [map_smul, map_sub]

end Grad.RawCircularSectors

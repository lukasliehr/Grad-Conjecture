import ANP14OriginalStateBounds
import ANM4ScalarRotation

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.RawCircularSectors
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.FlatSourceProjection
open Grad.NonlinearDivision Grad.ActualCenterVolterra Grad.AxisSplit

def centerDifferentialLinear (dimension : ℕ) (sign : ℤ) : ClosedJet dimension →ₗ[ℂ] ClosedJet dimension :=
  partialJetLinear dimension 0 - (Complex.I * (sign : ℂ)) • partialJetLinear dimension 1

theorem centerDifferentialLinear_apply {dimension : ℕ} (sign : ℤ) (field : ClosedJet dimension) :
    centerDifferentialLinear dimension sign field = centerDifferential sign field := rfl

theorem centerDifferential_zero (dimension : ℕ) (sign : ℤ) :
    centerDifferential sign (0 : ClosedJet dimension) = 0 := map_zero (centerDifferentialLinear dimension sign)

theorem angular_zero_origin {dimension : ℕ} (field : ClosedJet dimension) :
    (angularClosedJet 0 field).value closedOrigin = field.value closedOrigin :=
  angularJet_zero_originValue field

theorem centerDifferential_axis_zero {dimension : ℕ} (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (field : ClosedJet dimension) (excluded : angularClosedJet sign field = 0) :
    (centerDifferential sign field).value closedOrigin = 0 := by
  have law := centerDifferential_angular sign signed sign field
  rw [sub_self, excluded, centerDifferential_zero] at law
  exact (angular_zero_origin _).symm.trans
    ((congrArg (fun jet : ClosedJet dimension => jet.value closedOrigin) law.symm).trans (by rfl))

theorem partial_axis_of_signed_zero {dimension : ℕ} (field : ClosedJet dimension)
    (positive : (centerDifferential 1 field).value closedOrigin = 0)
    (negative : (centerDifferential (-1) field).value closedOrigin = 0) (direction : Fin 2) :
    (partialJet direction field).value closedOrigin = 0 := by
  apply PiLp.ext
  intro coordinate
  have p := congrArg (fun value : ComplexEuclidean dimension => value coordinate) positive
  have n := congrArg (fun value : ComplexEuclidean dimension => value coordinate) negative
  simp only [centerDifferential, sub_eq_add_neg, closedJet_value_add, closedJet_value_neg,
    closedJet_value_smul, ContinuousMap.add_apply, ContinuousMap.neg_apply, ContinuousMap.smul_apply,
    PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul, Int.cast_one,
    Int.cast_neg, mul_one, mul_neg_one] at p n
  change (partialJet 0 field).value closedOrigin coordinate +
    -(Complex.I * (partialJet 1 field).value closedOrigin coordinate) = 0 at p
  change (partialJet 0 field).value closedOrigin coordinate +
    -(-Complex.I * (partialJet 1 field).value closedOrigin coordinate) = 0 at n
  fin_cases direction
  · change (partialJet 0 field).value closedOrigin coordinate = 0
    linear_combination (1 / 2 : ℂ) * p + (1 / 2 : ℂ) * n
  · change (partialJet 1 field).value closedOrigin coordinate = 0
    have product : Complex.I * (partialJet 1 field).value closedOrigin coordinate = 0 := by
      linear_combination -(1 / 2 : ℂ) * p + (1 / 2 : ℂ) * n
    exact (mul_eq_zero.mp product).resolve_left Complex.I_ne_zero

theorem partial_axis_zero_of_modes {dimension : ℕ} (field : ClosedJet dimension)
    (positive : angularClosedJet 1 field = 0) (negative : angularClosedJet (-1) field = 0)
    (direction : Fin 2) : (partialJet direction field).value closedOrigin = 0 :=
  partial_axis_of_signed_zero field (centerDifferential_axis_zero 1 (Or.inl rfl) field positive)
    (centerDifferential_axis_zero (-1) (Or.inr rfl) field negative) direction

theorem partial_centerDifferential {dimension : ℕ} (direction : Fin 2) (sign : ℤ) (field : ClosedJet dimension) :
    partialJet direction (centerDifferential sign field) = centerDifferential sign (partialJet direction field) := by
  change partialJetLinear dimension direction
    (partialJet 0 field - (Complex.I * (sign : ℂ)) • partialJet 1 field) = _
  rw [map_sub, map_smul, partialJetLinear_apply, partialJetLinear_apply]
  change partialJet direction (partialJet 0 field) - (Complex.I * (sign : ℂ)) •
    partialJet direction (partialJet 1 field) = _
  rw [Grad.ActualMeanInverse.partialJets_commute direction 0,
    Grad.ActualMeanInverse.partialJets_commute direction 1]
  rfl

/-- A genuine Cartesian Hessian at the axis only sees scalar angular modes
0 and ±2. These derivatives vanish without imposing a new Taylor pin. -/
theorem hessian_axis_zero_of_exceptional {dimension : ℕ} (field : ClosedJet dimension)
    (excluded : ∀ mode, IsExceptionalRaw mode → angularClosedJet mode field = 0)
    (first second : Fin 2) : (partialJet first (partialJet second field)).value closedOrigin = 0 := by
  have signedFlat (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (direction : Fin 2) :
      (partialJet direction (centerDifferential sign field)).value closedOrigin = 0 := by
    apply partial_axis_zero_of_modes
    · have law := centerDifferential_angular sign signed (1 + sign) field
      have exceptional : IsExceptionalRaw (1 + sign) := by rcases signed with rfl | rfl <;> norm_num [IsExceptionalRaw]
      rw [show 1 + sign - sign = 1 by omega, excluded _ exceptional, centerDifferential_zero] at law
      exact law.symm
    · have law := centerDifferential_angular sign signed (-1 + sign) field
      have exceptional : IsExceptionalRaw (-1 + sign) := by rcases signed with rfl | rfl <;> norm_num [IsExceptionalRaw]
      rw [show -1 + sign - sign = -1 by omega, excluded _ exceptional, centerDifferential_zero] at law
      exact law.symm
  apply partial_axis_of_signed_zero (partialJet second field)
  · exact (congrArg (fun jet : ClosedJet dimension => jet.value closedOrigin)
      (partial_centerDifferential second 1 field).symm).trans (signedFlat 1 (Or.inl rfl) second)
  · exact (congrArg (fun jet : ClosedJet dimension => jet.value closedOrigin)
      (partial_centerDifferential second (-1) field).symm).trans (signedFlat (-1) (Or.inr rfl) second)

variable {L sigma gamma ell : ℝ}

/-- The source complement's true Cartesian first derivatives vanish because
the spin modes that could contribute are precisely raw 0 and ±2. -/
theorem exceptionalSource_force_partial_zero (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (excluded : AvoidsExceptionalSource source)
    (cell : ℤ) (direction : Fin 2) :
    (partialJet direction (apSmoothJet admissible 2 cell source.1)).value closedOrigin = 0 := by
  let field := apSmoothJet admissible 2 cell source.1
  have spinFlat (sign : ℤ) (signed : sign = 1 ∨ sign = -1) :
      (partialJet direction (valueMapJet (spinValue (sign : ℂ)) field)).value closedOrigin = 0 := by
    apply partial_axis_zero_of_modes
    · have exceptional : IsExceptionalRaw (1 - sign) := by rcases signed with rfl | rfl <;> norm_num [IsExceptionalRaw]
      simpa only [sub_add_cancel] using rawSource_excluded_spin admissible (1 - sign) sign signed source
        (excluded _ exceptional) cell
    · have exceptional : IsExceptionalRaw (-1 - sign) := by rcases signed with rfl | rfl <;> norm_num [IsExceptionalRaw]
      simpa only [sub_add_cancel] using rawSource_excluded_spin admissible (-1 - sign) sign signed source
        (excluded _ exceptional) cell
  have p := congrArg (fun value : ComplexEuclidean 1 => value 0) (spinFlat 1 (Or.inl rfl))
  have n := congrArg (fun value : ComplexEuclidean 1 => value 0) (spinFlat (-1) (Or.inr rfl))
  simp only [partialJet_valueMap, valueMapJet_value, Int.cast_one, Int.cast_neg,
    spinValue_apply, one_mul, neg_one_mul, PiLp.zero_apply] at p n
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · change (partialJet direction field).value closedOrigin 0 = 0
    linear_combination (1 / 2 : ℂ) * p + (1 / 2 : ℂ) * n
  · change (partialJet direction field).value closedOrigin 1 = 0
    have product : Complex.I * (partialJet direction field).value closedOrigin 1 = 0 := by
      linear_combination (1 / 2 : ℂ) * p - (1 / 2 : ℂ) * n
    exact (mul_eq_zero.mp product).resolve_left Complex.I_ne_zero

theorem exceptionalSource_scalar_hessians_zero (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (excluded : AvoidsExceptionalSource source)
    (cell : ℤ) (first second : Fin 2) :
    (partialJet first (partialJet second (apSmoothJet admissible 1 cell source.2.1))).value closedOrigin = 0 ∧
      (partialJet first (partialJet second (apSmoothJet admissible 1 cell source.2.2))).value closedOrigin = 0 :=
  ⟨hessian_axis_zero_of_exceptional _
      (fun mode exceptional => (rawSource_excluded_components admissible mode source (excluded mode exceptional) cell).2.1) first second,
    hessian_axis_zero_of_exceptional _
      (fun mode exceptional => (rawSource_excluded_components admissible mode source (excluded mode exceptional) cell).2.2) first second⟩

theorem exceptionalState_theta_hessian_zero (admissible : Admissible L sigma gamma ell)
    (state : CompensatedData L sigma gamma ell) (excluded : AvoidsExceptionalState state)
    (cell : ℤ) (first second : Fin 2) :
    (partialJet first (partialJet second (apSmoothJet admissible 1 cell state.1))).value closedOrigin = 0 :=
  hessian_axis_zero_of_exceptional _
    (fun mode exceptional => (rawState_excluded_components admissible mode state (excluded mode exceptional) cell).1) first second

end Grad.RawCircularSectors

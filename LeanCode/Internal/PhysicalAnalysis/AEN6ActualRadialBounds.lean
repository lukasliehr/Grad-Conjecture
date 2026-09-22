import AEN5FiniteRadialInduction

noncomputable section
set_option maxHeartbeats 1400000
open scoped BigOperators
namespace Grad.ExceptionalNative
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.ActualCenterBounds Grad.ActualExceptionalInverse Grad.CircularHighRegularity

/-- Actual smooth first-order data, used only to choose constants uniformly.
The exceptional primitives below supply every equation and mode condition. -/
structure SignedEquationDatum where
  sign : ℤ
  mode : ℤ
  signed : sign = 1 ∨ sign = -1
  small : |(mode : ℝ)| ≤ 2
  field : ClosedJet 1
  forcing : ClosedJet 1
  pure : angularClosedJet mode field = field
  forcingPure : angularClosedJet (mode - sign) forcing = forcing
  equation : signedLowering sign field = forcing

def signedNativeSize (grade : ℕ) (datum : SignedEquationDatum) : ℝ :=
  ‖unitDiskCoreInto grade datum.forcing‖ + ‖unitDiskCoreInto 1 datum.field‖

theorem signedNativeSize_nonnegative (grade : ℕ) (datum : SignedEquationDatum) : 0 ≤ signedNativeSize grade datum :=
  add_nonneg (norm_nonneg _) (norm_nonneg _)

theorem signedNativeSize_source (grade : ℕ) (datum : SignedEquationDatum) :
    ‖unitDiskCoreInto grade datum.forcing‖ ≤ signedNativeSize grade datum := le_add_of_nonneg_right (norm_nonneg _)

theorem signedNativeSize_base (grade : ℕ) (datum : SignedEquationDatum) :
    ‖unitDiskCoreInto 1 datum.field‖ ≤ signedNativeSize grade datum := le_add_of_nonneg_left (norm_nonneg _)

theorem signedProfile_allRadial_exists (grade : ℕ) : ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (datum : SignedEquationDatum) (order : ℕ), order ≤ grade + 1 →
      radialWithinEnergy (1 / 2) order (pureProfile datum.mode datum.field) ≤
        constant * signedNativeSize grade datum ^ 2 := by
  apply firstOrderRadialInduction grade
    (fun datum order => radialWithinEnergy (1 / 2) order (pureProfile datum.mode datum.field))
    (fun datum order => radialWithinEnergy (1 / 2) order (pureProfile (datum.mode - datum.sign) datum.forcing))
    (fun datum => signedNativeSize grade datum ^ 2) (profileSourceConstant 1) (profileSourceConstant grade)
    (fun order => 4 * radialProductConstant (1 / 2) (by norm_num) (by norm_num) order)
    (fun _ => sq_nonneg _) (profileSourceConstant_nonnegative 1) (profileSourceConstant_nonnegative grade)
    (fun order => mul_nonneg (by norm_num) (radialProductConstant_nonnegative (1 / 2) (by norm_num) (by norm_num) order))
  · intro datum order zero
    subst order
    exact (pureProfile_energy_source 1 0 (by omega) datum.field datum.mode).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (signedNativeSize_base grade datum) 2)
        (profileSourceConstant_nonnegative 1))
  · intro datum order paid
    exact (pureProfile_energy_source grade order paid datum.forcing (datum.mode - datum.sign)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (signedNativeSize_source grade datum) 2)
        (profileSourceConstant_nonnegative grade))
  · intro datum order _
    exact pureProfile_signed_energy_recurrence datum.sign datum.mode datum.signed datum.small datum.field datum.forcing
      datum.pure datum.forcingPure datum.equation order

def signedProfileConstant (grade : ℕ) : ℝ := (signedProfile_allRadial_exists grade).choose

theorem signedProfileConstant_nonnegative (grade : ℕ) : 0 ≤ signedProfileConstant grade :=
  (signedProfile_allRadial_exists grade).choose_spec.1

theorem signedProfile_allRadial (grade : ℕ) (datum : SignedEquationDatum) (order : ℕ) (paid : order ≤ grade + 1) :
    radialWithinEnergy (1 / 2) order (pureProfile datum.mode datum.field) ≤
      signedProfileConstant grade * signedNativeSize grade datum ^ 2 :=
  (signedProfile_allRadial_exists grade).choose_spec.2 datum order paid

end Grad.ExceptionalNative

import AEN8SharpSignedNativeGain

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.ExceptionalNative
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.ActualCenterBounds Grad.ActualExceptionalInverse
open Grad.GaugeCoefficients.Physical.RadialLedger (apLoweringConstant apLoweringConstant_nonnegative)

def regularPrimitiveGainConstant (grade : ℕ) : ℝ :=
  signedNativeGainConstant grade * (1 + regularPrimitiveBaseConstant 1 * apLoweringConstant 1)

theorem regularPrimitiveBaseConstant_nonnegative (grade : ℕ) : 0 ≤ regularPrimitiveBaseConstant grade :=
  mul_nonneg (ordinaryPowerConstant_nonnegative _) (ordinarySignedCoordinateConstant_nonnegative _)

theorem regularPrimitiveGainConstant_nonnegative (grade : ℕ) : 0 ≤ regularPrimitiveGainConstant grade :=
  mul_nonneg (signedNativeGainConstant_nonnegative grade) (add_nonneg zero_le_one
    (mul_nonneg (regularPrimitiveBaseConstant_nonnegative 1) (apLoweringConstant_nonnegative 1)))

theorem regularPrimitive_sharp (grade : ℕ) (large : 1 ≤ grade) (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (forcing : ClosedJet 1) (pure : angularClosedJet sign forcing = forcing) :
    ‖unitDiskCoreInto (grade + 1) (regularSecondPrimitive sign forcing)‖ ≤
      regularPrimitiveGainConstant grade * ‖unitDiskCoreInto grade forcing‖ := by
  let datum : SignedEquationDatum := ⟨sign, 2 * sign, signed, by rcases signed with rfl | rfl <;> norm_num,
    regularSecondPrimitive sign forcing, forcing, regularSecondPrimitive_mode sign signed forcing pure,
    by simpa only [show 2 * sign - sign = sign by omega] using pure,
    regularSecondPrimitive_derivative sign signed forcing pure⟩
  have base := (regularPrimitive_base 1 sign signed forcing).trans
    (mul_le_mul_of_nonneg_left (originalCore_lower large forcing) (regularPrimitiveBaseConstant_nonnegative 1))
  exact (signedNativeGain grade datum).trans ((mul_le_mul_of_nonneg_left (add_le_add le_rfl base)
    (signedNativeGainConstant_nonnegative grade)).trans_eq (by unfold regularPrimitiveGainConstant; ring))

def pinnedPrimitiveGainConstant (grade : ℕ) : ℝ :=
  signedNativeGainConstant grade * (1 + pinnedPrimitiveBaseConstant 1 * apLoweringConstant 3)

theorem pinnedPrimitiveGainConstant_nonnegative (grade : ℕ) : 0 ≤ pinnedPrimitiveGainConstant grade :=
  mul_nonneg (signedNativeGainConstant_nonnegative grade) (add_nonneg zero_le_one
    (mul_nonneg (pinnedPrimitiveBaseConstant_nonnegative 1) (apLoweringConstant_nonnegative 3)))

/-- Sharp AN32-range pinned first-order gain for the same literal cubic
Euler primitive. The H3 base is the reason for the stated p ≥ 3 scope. -/
theorem pinnedPrimitive_sharp (grade : ℕ) (large : 3 ≤ grade) (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (forcing : ClosedJet 1) (pure : angularClosedJet (2 * sign) forcing = forcing) :
    ‖unitDiskCoreInto (grade + 1) (pinnedSpinPrimitive sign forcing)‖ ≤
      pinnedPrimitiveGainConstant grade * ‖unitDiskCoreInto grade forcing‖ := by
  let datum : SignedEquationDatum := ⟨-sign, sign, by rcases signed with rfl | rfl <;> norm_num,
    by rcases signed with rfl | rfl <;> norm_num, pinnedSpinPrimitive sign forcing, forcing,
    pinnedSpinPrimitive_mode sign signed forcing pure,
    by simpa only [show sign - -sign = 2 * sign by omega] using pure,
    pinnedSpinPrimitive_derivative sign signed forcing pure⟩
  have base := (pinnedPrimitive_base 1 sign signed forcing).trans
    (mul_le_mul_of_nonneg_left (originalCore_lower large forcing) (pinnedPrimitiveBaseConstant_nonnegative 1))
  exact (signedNativeGain grade datum).trans ((mul_le_mul_of_nonneg_left (add_le_add le_rfl base)
    (signedNativeGainConstant_nonnegative grade)).trans_eq (by unfold pinnedPrimitiveGainConstant; ring))

end Grad.ExceptionalNative

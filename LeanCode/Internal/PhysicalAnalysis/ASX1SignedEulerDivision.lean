import ACE26LiteralCenterConsumer
import ASU5LiteralStrongConsumer

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualExceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearRadial Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.ActualCenterVolterra

/-- The signed derivative lowering a positive signed angular mode. -/
abbrev signedLowering {dimension : ℕ} (sign : ℤ) (field : ClosedJet dimension) : ClosedJet dimension :=
  centerDifferential sign field

/-- The literal Y28 compact integral, with exponent `power + 1`. -/
def signedQuotient {dimension : ℕ} (sign : ℤ) (power : ℕ) (field : ClosedJet dimension) : ClosedJet dimension :=
  powerDilationJet (power + 1) (signedLowering sign field)

theorem signedCoordinate_powerDilation {dimension : ℕ} (sign : ℤ) (power : ℕ) (field : ClosedJet dimension) :
    powerDilationJet power (coordinateMultiplyJet (sign : ℝ) field) =
      coordinateMultiplyJet (sign : ℝ) (powerDilationJet (power + 1) field) := by
  simp only [centerCoordinate_decomposition, powerDilationJet_add, powerDilationJet_smul,
    powerDilation_coordinate]

theorem signedMode_euler {dimension : ℕ} (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (power : ℕ) (field : ClosedJet dimension)
    (pure : angularClosedJet (((power : ℤ) + 1) * sign) field = field) :
    coordinateMultiplyJet (sign : ℝ) (signedLowering sign field) = shiftedEulerJet power field := by
  rw [centerDifferential_euler sign signed, pureMode_rotation _ field pure, smul_smul]
  have coefficient : (Complex.I * (sign : ℂ)) *
      (Complex.I * ((((power : ℤ) + 1) * sign : ℤ) : ℂ)) = -((power + 1 : ℝ) : ℂ) := by
    rcases signed with rfl | rfl <;> push_cast <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  rw [coefficient, neg_smul, sub_neg_eq_add]
  rfl

/-- Genuine Cartesian division on the entire closed disk, including the axis. -/
theorem signedQuotient_factor {dimension : ℕ} (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (power : ℕ) (field : ClosedJet dimension)
    (pure : angularClosedJet (((power : ℤ) + 1) * sign) field = field) :
    coordinateMultiplyJet (sign : ℝ) (signedQuotient sign power field) = field := by
  exact (signedCoordinate_powerDilation sign power (signedLowering sign field)).symm.trans
    ((congrArg (powerDilationJet power) (signedMode_euler sign signed power field pure)).trans
      (powerDilation_shiftedEuler power field))

theorem signedCoordinate_mode {dimension : ℕ} (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (mode : ℤ) (field : ClosedJet dimension) :
    angularClosedJet mode (coordinateMultiplyJet (sign : ℝ) field) =
      coordinateMultiplyJet (sign : ℝ) (angularClosedJet (mode - sign) field) := by
  rcases signed with rfl | rfl
  · simpa only [Int.cast_one] using angularClosedJet_z mode field
  · simpa only [Int.cast_neg, Int.cast_one, sub_neg_eq_add] using angularClosedJet_zbar mode field

/-- Division lowers the literal signed mode by one. -/
theorem signedQuotient_mode {dimension : ℕ} (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (power : ℕ) (field : ClosedJet dimension)
    (pure : angularClosedJet (((power : ℤ) + 1) * sign) field = field) :
    angularClosedJet ((power : ℤ) * sign) (signedQuotient sign power field) =
      signedQuotient sign power field := by
  apply centerCoordinate_injective sign signed
  have shift : ((power : ℤ) + 1) * sign - sign = (power : ℤ) * sign := by ring
  have projected := signedCoordinate_mode sign signed (((power : ℤ) + 1) * sign)
    (signedQuotient sign power field)
  rw [shift, signedQuotient_factor sign signed power field pure, pure] at projected
  exact projected.symm.trans (signedQuotient_factor sign signed power field pure).symm

end Grad.ActualExceptionalInverse

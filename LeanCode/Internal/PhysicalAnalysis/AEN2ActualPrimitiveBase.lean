import AEN1OrdinaryPowerIntegral

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.ExceptionalNative
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial
open Grad.NonlinearQuotientBounds Grad.ActualCenterVolterra Grad.ActualExceptionalInverse
open Grad.CircularHighWeak Grad.ActualCenterBounds
open Grad.NonlinearDivision (laplacianJet)
open Grad.GaugeCoefficients.Algebra

def ordinarySignedCoordinateConstant (grade : ℕ) : ℝ :=
  unitCoordinateConstant grade 0 + unitCoordinateConstant grade 1

theorem ordinarySignedCoordinateConstant_nonnegative (grade : ℕ) : 0 ≤ ordinarySignedCoordinateConstant grade :=
  add_nonneg (unitCoordinateConstant_nonnegative _ _) (unitCoordinateConstant_nonnegative _ _)

theorem ordinarySignedCoordinate_bound (grade : ℕ) (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (field : ClosedJet 1) :
    ‖unitSobolevRow grade (coordinateMultiplyJet (sign : ℝ) field)‖ ≤
      ordinarySignedCoordinateConstant grade * ‖unitSobolevRow grade field‖ := by
  have coefficient : ‖Complex.I * (sign : ℂ)‖ = 1 := by rcases signed with rfl | rfl <;> norm_num
  rw [centerCoordinate_decomposition, map_add, map_smul]
  apply (norm_add_le _ _).trans
  rw [norm_smul]
  push_cast
  rw [coefficient, one_mul]
  exact (add_le_add (unitCoordinate_bound grade 0 field)
    (unitCoordinate_bound grade 1 field)).trans_eq (by unfold ordinarySignedCoordinateConstant; ring)

def ordinarySignedDerivativeConstant (grade : ℕ) : ℝ := 2 * ordinaryPowerConstant grade

theorem ordinarySignedDerivativeConstant_nonnegative (grade : ℕ) : 0 ≤ ordinarySignedDerivativeConstant grade :=
  mul_nonneg (by norm_num) (ordinaryPowerConstant_nonnegative grade)

theorem ordinarySignedDerivative_bound (grade : ℕ) (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (field : ClosedJet 1) :
    ‖unitSobolevRow grade (signedLowering sign field)‖ ≤
      ordinarySignedDerivativeConstant grade * ‖unitSobolevRow (grade + 1) field‖ := by
  have coefficient : ‖Complex.I * (sign : ℂ)‖ = 1 := by rcases signed with rfl | rfl <;> norm_num
  rw [signedLowering, centerDifferential, map_sub, map_smul]
  apply (norm_sub_le _ _).trans
  rw [norm_smul, coefficient, one_mul]
  exact (add_le_add (unitPartial_bound grade 0 field) (unitPartial_bound grade 1 field)).trans_eq
    (by unfold ordinarySignedDerivativeConstant ordinaryPowerConstant; ring)

def ordinaryRadiusConstant (grade : ℕ) : ℝ :=
  unitCoordinateConstant grade 0 ^ 2 + unitCoordinateConstant grade 1 ^ 2

theorem ordinaryRadiusConstant_nonnegative (grade : ℕ) : 0 ≤ ordinaryRadiusConstant grade := by
  unfold ordinaryRadiusConstant
  positivity

theorem ordinaryRadius_bound (grade : ℕ) (field : ClosedJet 1) :
    ‖unitSobolevRow grade (radiusPowerJet 1 field)‖ ≤ ordinaryRadiusConstant grade * ‖unitSobolevRow grade field‖ := by
  rw [radiusPower_one_decomposition, map_add]
  apply (norm_add_le _ _).trans
  have first := (unitCoordinate_bound grade 0 (coordinateJet 0 field)).trans
    (mul_le_mul_of_nonneg_left (unitCoordinate_bound grade 0 field) (unitCoordinateConstant_nonnegative _ _))
  have second := (unitCoordinate_bound grade 1 (coordinateJet 1 field)).trans
    (mul_le_mul_of_nonneg_left (unitCoordinate_bound grade 1 field) (unitCoordinateConstant_nonnegative _ _))
  exact (add_le_add first second).trans_eq (by unfold ordinaryRadiusConstant; ring)

def ordinaryQuotientConstant (grade : ℕ) : ℝ := ordinaryPowerConstant grade * ordinarySignedDerivativeConstant grade

theorem ordinaryQuotientConstant_nonnegative (grade : ℕ) : 0 ≤ ordinaryQuotientConstant grade :=
  mul_nonneg (ordinaryPowerConstant_nonnegative _) (ordinarySignedDerivativeConstant_nonnegative _)

theorem ordinaryQuotient_bound (grade power : ℕ) (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (field : ClosedJet 1) :
    ‖unitSobolevRow grade (signedQuotient sign power field)‖ ≤
      ordinaryQuotientConstant grade * ‖unitSobolevRow (grade + 1) field‖ :=
  ((ordinaryPower_row_bound grade power (signedLowering sign field)).trans
    (mul_le_mul_of_nonneg_left (ordinarySignedDerivative_bound grade sign signed field)
      (ordinaryPowerConstant_nonnegative grade))).trans_eq (mul_assoc _ _ _).symm

def regularPrimitiveBaseConstant (grade : ℕ) : ℝ :=
  ordinaryPowerConstant grade * ordinarySignedCoordinateConstant grade

theorem regularPrimitive_base (grade : ℕ) (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (field : ClosedJet 1) :
    ‖unitDiskCoreInto grade (regularSecondPrimitive sign field)‖ ≤
      regularPrimitiveBaseConstant grade * ‖unitDiskCoreInto grade field‖ := by
  rw [unitDiskCore_norm, unitDiskCore_norm]
  exact ((ordinaryPower_row_bound grade 0 (coordinateMultiplyJet (sign : ℝ) field)).trans
    (mul_le_mul_of_nonneg_left (ordinarySignedCoordinate_bound grade sign signed field)
      (ordinaryPowerConstant_nonnegative grade))).trans_eq (mul_assoc _ _ _).symm

def pinnedPrimitiveBaseConstant (grade : ℕ) : ℝ :=
  ordinarySignedCoordinateConstant grade * ordinaryRadiusConstant grade * ordinaryPowerConstant grade *
    ordinaryQuotientConstant grade * ordinaryQuotientConstant (grade + 1)

theorem pinnedPrimitiveBaseConstant_nonnegative (grade : ℕ) : 0 ≤ pinnedPrimitiveBaseConstant grade := by
  unfold pinnedPrimitiveBaseConstant
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (ordinarySignedCoordinateConstant_nonnegative _) (ordinaryRadiusConstant_nonnegative _))
      (ordinaryPowerConstant_nonnegative _)) (ordinaryQuotientConstant_nonnegative _))
        (ordinaryQuotientConstant_nonnegative _)

/-- A genuine coarse base for the later sharp induction. At grade one this
uses H3 and suffices for the required p ≥ 3 range. -/
theorem pinnedPrimitive_base (grade : ℕ) (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (field : ClosedJet 1) :
    ‖unitDiskCoreInto grade (pinnedSpinPrimitive sign field)‖ ≤
      pinnedPrimitiveBaseConstant grade * ‖unitDiskCoreInto (grade + 2) field‖ := by
  rw [unitDiskCore_norm, unitDiskCore_norm]
  have quotient := (ordinaryQuotient_bound grade 0 sign signed (signedQuotient sign 1 field)).trans
    (mul_le_mul_of_nonneg_left (ordinaryQuotient_bound (grade + 1) 1 sign signed field)
      (ordinaryQuotientConstant_nonnegative grade))
  have integral := (ordinaryPower_row_bound grade 0 (secondModeQuotient sign field)).trans
    (mul_le_mul_of_nonneg_left quotient (ordinaryPowerConstant_nonnegative grade))
  have radius := (ordinaryRadius_bound grade (powerDilationJet 1 (secondModeQuotient sign field))).trans
    (mul_le_mul_of_nonneg_left integral (ordinaryRadiusConstant_nonnegative grade))
  have coordinate := (ordinarySignedCoordinate_bound grade sign signed
    (radiusPowerJet 1 (powerDilationJet 1 (secondModeQuotient sign field)))).trans
      (mul_le_mul_of_nonneg_left radius (ordinarySignedCoordinateConstant_nonnegative grade))
  exact coordinate.trans_eq (by unfold pinnedPrimitiveBaseConstant; ring)

theorem signedEquation_laplacian (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (value forcing : ClosedJet 1) (equation : signedLowering sign value = forcing) :
    laplacianJet value = signedLowering (-sign) forcing := by
  have opposite : -sign = 1 ∨ -sign = -1 := by rcases signed with rfl | rfl <;> norm_num
  have identity := signedDerivatives_laplacian (-sign) opposite value
  rw [neg_neg, equation] at identity
  exact identity.symm

end Grad.ExceptionalNative

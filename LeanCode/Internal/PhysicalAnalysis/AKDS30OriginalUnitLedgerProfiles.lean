import AKDS29OriginalUnitLedger

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.SourceCollarCoefficients
open Grad.ActualGaugeSigmaPrimitives Grad.ActualCurrentPrimitives
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.InverseAllocation

def originalUnitFour (parameters : PhaseParameters) (length radius : ℝ) (grade : ℕ) : ℝ :=
  |(originalGaugeProfile parameters length radius).deviation grade|+
    |(fluxProfile (originalFullFrameProfile parameters length) (originalInverseProfile parameters length)).deviation grade|

def originalUnitFive (parameters : PhaseParameters) (length : ℝ) (grade : ℕ) : ℝ :=
  |(rotatedProductProfile planarFrameColumns (originalRotatedProfile parameters length)
      (originalInverseProfile parameters length)).deviation grade|+
    |(rotatedProductProfile thirdFrameColumn (originalRotatedProfile parameters length)
      (originalInverseProfile parameters length)).deviation grade|

theorem originalUnitFour_nonnegative (parameters : PhaseParameters) (length radius : ℝ) (grade : ℕ) :
    0≤originalUnitFour parameters length radius grade := add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem originalUnitFive_nonnegative (parameters : PhaseParameters) (length : ℝ) (grade : ℕ) :
    0≤originalUnitFive parameters length grade := add_nonneg (abs_nonneg _) (abs_nonneg _)

/-- The four genuine current/force/flux rows of the original unit-disk
ledger inherit their existing physical coefficient estimates. The length
factor stays in the actual families, and all profiles precede the state. -/
theorem originalUnitLedgerData_row_bounds (parameters : PhaseParameters) (length radius : ℝ)
    (radiusNonnegative : 0≤radius) (rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (alphaSmall : |alpha|≤radius) (deltaSmall : |delta|≤radius) (parameterSmall : |parameter|≤radius)
    (low : physicalBudget parameters field rho epsilon 6≤originalCoefficientLowRadius parameters length)
    (grade : ℕ) :
    let data := originalUnitLedgerData parameters length rho alpha delta parameter epsilon field
    ‖data.gaugeDeviation grade‖≤originalUnitFour parameters length radius grade*physicalBudget parameters field rho epsilon (grade+4) ∧
    ‖data.fluxDeviation grade‖≤originalUnitFour parameters length radius grade*physicalBudget parameters field rho epsilon (grade+4) ∧
    ‖data.rotatedPlanarProduct grade‖≤originalUnitFive parameters length grade*physicalBudget parameters field rho epsilon (grade+5) ∧
    ‖data.rotatedThirdProduct grade‖≤originalUnitFive parameters length grade*physicalBudget parameters field rho epsilon (grade+5) := by
  have margin := originalCoefficient_low_margin parameters length rho epsilon field low
  have lowFive : physicalBudget parameters field rho epsilon 5≤1 :=
    (physicalBudget_monotone parameters field rho epsilon (by norm_num : 5≤6)).trans (low.trans (min_le_left _ _))
  have inverse := originalInverseFamily_estimate parameters length rho epsilon field low
  have frame := originalFullFrameFamily_estimate parameters length rho epsilon field margin.1
  have rotated := originalRotatedFamily_estimate parameters length rho epsilon field margin.1
  have gaugeBound := (originalGauge_estimate parameters length rho alpha delta parameter epsilon radius field
    radiusNonnegative alphaSmall deltaSmall parameterSmall low).absoluteBound grade
  have fluxBound := (fluxFamily_estimate (unitDiskAdmissible parameters) margin.2.1 frame inverse).absoluteBound grade
  have planarBound := (rotatedProductFamily_estimate (unitDiskAdmissible parameters) lowFive planarFrameColumns
    rotated (inverse.offset_mono (by norm_num : 4≤5))).absoluteBound grade
  have thirdBound := (rotatedProductFamily_estimate (unitDiskAdmissible parameters) lowFive thirdFrameColumn
    rotated (inverse.offset_mono (by norm_num : 4≤5))).absoluteBound grade
  have fourGauge : |(originalGaugeProfile parameters length radius).deviation grade|≤originalUnitFour parameters length radius grade :=
    le_add_of_nonneg_right (abs_nonneg _)
  have fourFlux : |(fluxProfile (originalFullFrameProfile parameters length) (originalInverseProfile parameters length)).deviation grade|≤
      originalUnitFour parameters length radius grade := le_add_of_nonneg_left (abs_nonneg _)
  have fivePlanar : |(rotatedProductProfile planarFrameColumns (originalRotatedProfile parameters length)
      (originalInverseProfile parameters length)).deviation grade|≤originalUnitFive parameters length grade :=
    le_add_of_nonneg_right (abs_nonneg _)
  have fiveThird : |(rotatedProductProfile thirdFrameColumn (originalRotatedProfile parameters length)
      (originalInverseProfile parameters length)).deviation grade|≤originalUnitFive parameters length grade :=
    le_add_of_nonneg_left (abs_nonneg _)
  exact ⟨gaugeBound.trans (mul_le_mul_of_nonneg_right fourGauge (physicalBudget_nonnegative _ _ _ _ _)),
    fluxBound.trans (mul_le_mul_of_nonneg_right fourFlux (physicalBudget_nonnegative _ _ _ _ _)),
    planarBound.trans (mul_le_mul_of_nonneg_right fivePlanar (physicalBudget_nonnegative _ _ _ _ _)),
    thirdBound.trans (mul_le_mul_of_nonneg_right fiveThird (physicalBudget_nonnegative _ _ _ _ _))⟩

end Grad.OriginalCoreRealization

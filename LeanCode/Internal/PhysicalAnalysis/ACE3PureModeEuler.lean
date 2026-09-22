import ACE2DilationBoundsAndLinearity

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterVolterra
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial
open Grad.NonlinearProduct Grad.NonlinearRange Grad.NonlinearQuotientBounds Grad.RepresentedKernel.SpatialProduct
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.GaugeTransfer

theorem centerExponential_hasDerivAt (mode : ℤ) (angle : ℝ) :
    HasDerivAt (cellExponential mode) ((Complex.I * (mode : ℂ)) * cellExponential mode angle) angle := by
  have derivative := (cellExponential_hasFDerivAt mode angle).hasDerivAt
  apply derivative.congr_deriv
  change ((Complex.I * (mode : ℂ)) * (1 : ℂ)) * cellExponential mode angle = _
  rw [mul_one]

theorem pureMode_covariance {dimension : ℕ} (mode : ℤ) (field : ClosedJet dimension)
    (pure : angularClosedJet mode field = field) (angle : ℝ) (point : ClosedDisk) :
    field.value (rotatedPoint angle point) = cellExponential mode angle • field.value point := by
  have covariance := angularClosedJet_rotation_value mode field angle point
  rw [pure, angularCharacter_neg_angle] at covariance
  simpa only [angularCharacter, neg_neg] using covariance

theorem pureMode_rotation {dimension : ℕ} (mode : ℤ) (field : ClosedJet dimension)
    (pure : angularClosedJet mode field = field) :
    rotationJet field = (Complex.I * (mode : ℂ)) • field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have original := closedOrbit_hasDerivAt field point 0
  have equalFunctions : (fun angle => field.value (rotatedPoint angle point)) =
      fun angle => cellExponential mode angle • field.value point :=
    funext (fun angle => pureMode_covariance mode field pure angle point)
  rw [equalFunctions] at original
  have specified := (centerExponential_hasDerivAt mode 0).smul_const (field.value point)
  have same := original.unique specified
  simpa [rotatedPoint_zero, cellExponential] using same

/-- Twice the actual signed Wirtinger derivative. -/
def centerDifferential {dimension : ℕ} (mode : ℤ) (field : ClosedJet dimension) : ClosedJet dimension :=
  partialJet 0 field - (Complex.I * (mode : ℂ)) • partialJet 1 field

theorem centerDifferential_euler {dimension : ℕ} (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (field : ClosedJet dimension) :
    coordinateMultiplyJet (mode : ℝ) (centerDifferential mode field) =
      eulerJet field - (Complex.I * (mode : ℂ)) • rotationJet field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [coordinateMultiplyJet_value]
  simp only [centerDifferential, eulerJet, rotationJet, sub_eq_add_neg, closedJet_value_add,
    closedJet_value_neg, closedJet_value_smul, ContinuousMap.add_apply, ContinuousMap.neg_apply,
    ContinuousMap.smul_apply, coordinateJet_value, signedComplexCoordinate]
  ext coordinate
  rcases center with rfl | rfl <;>
    simp only [PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul,
      Int.cast_one, Int.cast_neg, Complex.ofReal_one, Complex.ofReal_neg, mul_one, mul_neg_one] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem pureCenter_euler {dimension : ℕ} (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (field : ClosedJet dimension) (pure : angularClosedJet mode field = field) :
    coordinateMultiplyJet (mode : ℝ) (centerDifferential mode field) = eulerJet field + field := by
  rw [centerDifferential_euler mode center, pureMode_rotation mode field pure, smul_smul]
  have coefficient : (Complex.I * (mode : ℂ)) * (Complex.I * (mode : ℂ)) = -1 := by
    rcases center with rfl | rfl <;> norm_num
  rw [coefficient, neg_one_smul, sub_neg_eq_add]

end Grad.ActualCenterVolterra

import ASP3PrimitiveMultiplier

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.ActualSmoothPDE
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.GaugeCoefficients.Radial Grad.PhysicalFamily Grad.FourierGrade

theorem angularPrimitiveJet_zero : angularPrimitiveJet 0 = 0 := by
  apply closedJet_eq_of_value_eq
  ext point coordinate
  rw [angularPrimitiveJet_value]
  simp

theorem angularPrimitiveJet_smul (scalar : ℂ) (field : ClosedJet 1) :
    angularPrimitiveJet (scalar • field) = scalar • angularPrimitiveJet field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change (angularPrimitiveJet (scalar • field)).value point = scalar • (angularPrimitiveJet field).value point
  simp_rw [angularPrimitiveJet_value]
  change (2 * Real.pi)⁻¹ • (∫ angle in Icc (0 : ℝ) (2 * Real.pi),
    angle • (scalar • field.value (rotatedPoint angle point))) = _
  simp_rw [smul_comm _ scalar]
  rw [integral_smul, smul_comm]

theorem angularPrimitiveJet_pureMode (mode : ℤ) (nonzero : mode ≠ 0) (field : ClosedJet 1) :
    angularPrimitiveJet (angularClosedJet mode field) =
      (Complex.I * (mode : ℂ))⁻¹ • angularClosedJet mode field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change (angularPrimitiveJet (angularClosedJet mode field)).value point =
    (Complex.I * (mode : ℂ))⁻¹ • (angularClosedJet mode field).value point
  rw [angularPrimitiveJet_value]
  simp_rw [angularClosedJet_rotation_value, angularCharacter_neg_angle]
  simp only [angularCharacter, neg_neg]
  have row (angle : ℝ) : angle • (cellExponential mode angle • (angularClosedJet mode field).value point) =
      ((angle : ℂ) * cellExponential mode angle) • (angularClosedJet mode field).value point := by
    rw [← smul_assoc]
    rfl
  simp_rw [row]
  rw [integral_smul_const, ← smul_assoc, angularPrimitive_scalar_integral mode nonzero]

theorem angularClosedJet_angularPrimitive (mode : ℤ) (field : ClosedJet 1) :
    angularClosedJet mode (angularPrimitiveJet field) = angularPrimitiveJet (angularClosedJet mode field) :=
  angularClosedJet_weightedRotation id contDiff_id mode field

/-- The accepted diskB uses zero on all five excluded modes. This smooth
Cartesian representative uses the same convention for every input jet. -/
def smoothDiskBJet (field : ClosedJet 1) : ClosedJet 1 :=
  excludedAngularJet lowAngularModes field + (4 : ℂ) •
    angularPrimitiveJet (angularPrimitiveJet (excludedAngularJet lowAngularModes field))

theorem angularClosedJet_excluded_high (field : ClosedJet 1) (mode : ℤ)
    (high : mode ∉ lowAngularModes) :
    angularClosedJet mode (excludedAngularJet lowAngularModes field) = angularClosedJet mode field := by
  change angularClosedJetLinear 1 mode (field - selectedAngularJet lowAngularModes field) = _
  rw [map_sub]
  change angularClosedJet mode field - angularClosedJet mode (selectedAngularJet lowAngularModes field) = _
  rw [angularClosedJet_selected, if_neg high, sub_zero]

theorem smoothDiskBJet_coefficient (mode : ℤ) (field : ClosedJet 1) :
    angularClosedJet mode (smoothDiskBJet field) = (highMultiplier mode : ℂ) • angularClosedJet mode field := by
  unfold smoothDiskBJet
  rw [angularClosedJet_add, angularClosedJet_smul]
  simp_rw [angularClosedJet_angularPrimitive]
  by_cases low : mode ∈ lowAngularModes
  · rw [excludedAngularJet_low_zero field mode low, angularPrimitiveJet_zero,
      angularPrimitiveJet_zero, highMultiplier, if_pos low]
    simp
  · have nonzero : mode ≠ 0 := by
      intro zero
      apply low
      simp [zero, lowAngularModes]
    rw [angularClosedJet_excluded_high field mode low,
      angularPrimitiveJet_pureMode mode nonzero, angularPrimitiveJet_smul,
      angularPrimitiveJet_pureMode mode nonzero, highMultiplier_high mode low]
    rw [smul_smul, smul_smul]
    calc
      _ = (1 + 4 * (Complex.I * (mode : ℂ))⁻¹ * (Complex.I * (mode : ℂ))⁻¹) • angularClosedJet mode field := by
        rw [add_smul, one_smul]
      _ = _ := by
        congr 1
        push_cast
        have frequency : (mode : ℂ) ≠ 0 := by exact_mod_cast nonzero
        field_simp
        simp [Complex.I_sq]
        ring

theorem smoothDiskBJet_bulk (field : ClosedJet 1) :
    closedL2Core (smoothDiskBJet field) = diskB (closedL2Core field) := by
  apply diskFourierIsometry.injective
  apply lp.ext
  funext mode
  change diskMode mode (closedL2Core (smoothDiskBJet field)) = diskMode mode (diskB (closedL2Core field))
  rw [diskMode_core, smoothDiskBJet_coefficient, map_smul, diskB_coefficient, diskMode_core]

end Grad.ActualSmoothPDE

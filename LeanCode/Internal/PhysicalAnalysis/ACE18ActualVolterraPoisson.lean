import ACE16CenterLaplacianIdentity
import ACE17VolterraRadiality

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterVolterra
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearRadial Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.NonlinearDivision (IsRotationInvariant laplacianJet)

theorem centerCoordinate_zero (dimension : ℕ) (coordinate : Fin 2) :
    coordinateJet coordinate (0 : ClosedJet dimension) = 0 := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simp only [coordinateJet_value, closedJet_value_zero, ContinuousMap.zero_apply]
  exact smul_zero _

theorem centerRotation_zero (dimension : ℕ) : rotationJet (0 : ClosedJet dimension) = 0 := by
  simp only [rotationJet, centerPartial_zero, centerCoordinate_zero, sub_self]

theorem centerLaplacian_radial {dimension : ℕ} (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (field : ClosedJet dimension) (radial : IsRotationInvariant field) :
    laplacianJet (coordinateMultiplyJet (mode : ℝ) (radiusPowerJet 1 field)) =
      coordinateMultiplyJet (mode : ℝ) (shiftedEulerJet 1 (shiftedEulerJet 3 field)) := by
  rw [centerLaplacian_cartesian mode center, radial_rotation_zero field radial,
    centerRotation_zero, smul_zero, add_zero, add_zero]

theorem shiftedEuler_dilation_commute {dimension : ℕ} (shift power : ℕ) (field : ClosedJet dimension) :
    shiftedEulerJet shift (powerDilationJet power field) = powerDilationJet power (shiftedEulerJet shift field) := by
  simp only [shiftedEulerJet, powerDilationJet_add, powerDilationJet_smul, powerDilation_euler]

theorem shiftedEuler_injective {dimension : ℕ} (power : ℕ) :
    Function.Injective (shiftedEulerJet (dimension := dimension) power) := by
  intro first second same
  have identity := congrArg (powerDilationJet power) same
  simpa only [powerDilation_shiftedEuler] using identity

theorem powerDilation_commute {dimension : ℕ} (first second : ℕ) (field : ClosedJet dimension) :
    powerDilationJet first (powerDilationJet second field) = powerDilationJet second (powerDilationJet first field) := by
  apply shiftedEuler_injective first
  rw [shiftedEuler_powerDilation, shiftedEuler_dilation_commute, shiftedEuler_powerDilation]

/-- W5 as a literal closed Cartesian Poisson identity for the signed first
mode. The right side is the same smooth source supplied to the actual T. -/
theorem volterraJet_poisson {dimension : ℕ} (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (field : ClosedJet dimension) (radial : IsRotationInvariant field) :
    laplacianJet (coordinateMultiplyJet (mode : ℝ) (volterraJet field)) =
      coordinateMultiplyJet (mode : ℝ) field := by
  change laplacianJet (coordinateMultiplyJet (mode : ℝ)
    (radiusPowerJet 1 (powerDilationJet 1 (powerDilationJet 3 field)))) = _
  rw [centerLaplacian_radial mode center _
    (powerDilation_radial 1 _ (powerDilation_radial 3 field radial)),
    shiftedEuler_dilation_commute 3 1, shiftedEuler_powerDilation, shiftedEuler_powerDilation]

theorem volterraPower_poisson {dimension : ℕ} (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (count : ℕ) (field : ClosedJet dimension) (radial : IsRotationInvariant field) :
    laplacianJet (coordinateMultiplyJet (mode : ℝ) (volterraPower (count + 1) field)) =
      coordinateMultiplyJet (mode : ℝ) (volterraPower count field) :=
  volterraJet_poisson mode center _ (volterraPower_radial count field radial)

end Grad.ActualCenterVolterra

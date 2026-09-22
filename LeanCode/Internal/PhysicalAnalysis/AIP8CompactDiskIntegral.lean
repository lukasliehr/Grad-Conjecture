import AIP7SpatialCoefficientIntegral

noncomputable section
open Set MeasureTheory

namespace Grad.InteriorPeriodization
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.DiskExtension.Operator Grad.FourierGrade Grad.COR12Extension

theorem compact_smoothClosedExtension_literal (field : ClosedJet 1)
    (supported : ∀ point : ClosedDisk, (3 / 4 : ℝ) < ‖point.val‖ → field.value point = 0)
    (point : SpatialPlane) : smoothClosedExtension field point = closedDiskLift field.value point := by
  change ambientExtensionFromValue (constantDiskCellJet field).value
    (planarPart (assembleSpatialCell point 0)) ((assembleSpatialCell point 0) 2 : CellCircle) = _
  rw [planarPart_assembleSpatialCell]
  exact compact_ambientExtension_literal field supported point _

theorem compact_closedDiskLift_outside (field : ClosedJet 1)
    (supported : ∀ point : ClosedDisk, (3 / 4 : ℝ) < ‖point.val‖ → field.value point = 0)
    (point : SpatialPlane) (outside : point ∉ openUnitDisk) : closedDiskLift field.value point = 0 := by
  classical
  by_cases closed : point ∈ closedUnitDisk
  · have large : 1 ≤ ‖point‖ := le_of_not_gt outside
    rw [closedDiskLift, dif_pos closed]
    exact supported ⟨point, closed⟩ (by linarith)
  · simp only [closedDiskLift, dif_neg closed]

/-- The spatial coefficient uses ordinary disk area, with precisely1/16
from the physical period-four probability torus. -/
theorem spatialCoreCoefficient_disk (field : ClosedJet 1)
    (supported : ∀ point : ClosedDisk, (3 / 4 : ℝ) < ‖point.val‖ → field.value point = 0)
    (firstMode secondMode : ℤ) :
    spatialCoreCoefficient field firstMode secondMode =
      (1 / 16 : ℝ) • ∫ point in openUnitDisk,
        negativeDiskCharacter firstMode secondMode point • closedDiskLift field.value point := by
  let integrand := fun point => negativeDiskCharacter firstMode secondMode point • smoothClosedExtension field point
  have continuousIntegrand : Continuous integrand :=
    (negativeDiskCharacter_continuous firstMode secondMode).smul (smoothClosedExtension_smooth field).continuous
  have literal (point : SpatialPlane) : integrand point =
      negativeDiskCharacter firstMode secondMode point • closedDiskLift field.value point := by
    change negativeDiskCharacter firstMode secondMode point • smoothClosedExtension field point = _
    rw [compact_smoothClosedExtension_literal field supported]
  have outsideDisk (point : SpatialPlane) (outside : point ∉ openUnitDisk) : integrand point = 0 := by
    rw [literal, compact_closedDiskLift_outside field supported point outside, smul_zero]
  have integrableSquare : IntegrableOn integrand fundamentalIocSquare :=
    (continuousIntegrand.continuousOn.integrableOn_compact fundamentalIccSquare_isCompact).mono_set
      fundamentalIocSquare_subset_Icc
  rw [spatialCoreCoefficient_box field supported]
  congr 1
  have box : (∫ second in Ico (-2 : ℝ) 2, ∫ first in Ico (-2 : ℝ) 2,
      negativeDiskCharacter firstMode secondMode (WithLp.toLp 2 ![first, second]) •
        closedDiskLift field.value (WithLp.toLp 2 ![first, second])) =
      ∫ point in fundamentalIocSquare, integrand point := by
    simp_rw [restrict_Ico_eq_restrict_Ioc, ← literal]
    exact (integral_fundamentalIocSquare_eq_iterated integrand integrableSquare).symm
  rw [box]
  calc
    _ = ∫ point, integrand point := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro point outside
      apply outsideDisk point
      intro inside
      exact outside (closedUnitDisk_subset_fundamentalIocSquare (openDiskMembershipClosed point inside))
    _ = ∫ point in openUnitDisk, integrand point :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero outsideDisk).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with point
      exact literal point

end Grad.InteriorPeriodization

import AKBV13WeightedCylinderGluing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter
open scoped ContDiff Topology
namespace Grad.CartesianCoreRecovery
open Grad.ClosedJets Grad.CartesianState Grad.DiskExtension.Operator Grad.BoundaryTrace

def rescaledWeightedInterior {dimension : ℕ} (weighted : DiskCellClosedJet dimension)
    (scale : ℝ) (point : SpatialCell) : ComplexEuclidean dimension :=
  ambientExtensionCellLift weighted (assembleSpatialCell (scale⁻¹ • planarPart point) (point 2))

theorem rescaledWeightedInterior_smooth {dimension : ℕ} (weighted : DiskCellClosedJet dimension) (scale : ℝ) :
    ContDiff ℝ ∞ (rescaledWeightedInterior weighted scale) :=
  (ambientExtensionCellLift_contDiff_infty weighted).comp
    (assembleSpatialCellCLM.contDiff.comp ((planarPartCLM.contDiff.const_smul scale⁻¹).prodMk cellCoordinateCLM.contDiff))

theorem rescaledWeightedInterior_periodic {dimension : ℕ} (weighted : DiskCellClosedJet dimension) (scale : ℝ)
    (point : SpatialPlane) :
    Function.Periodic (fun axial => rescaledWeightedInterior weighted scale (assembleSpatialCell point axial)) (2*Real.pi) := by
  intro axial
  simp only [rescaledWeightedInterior,ambientExtensionCellLift,planarPart_assembleSpatialCell]
  change ambientExtensionFromValue weighted.value (scale⁻¹ • point) ((axial + 2*Real.pi : ℝ) : CellCircle) =
    ambientExtensionFromValue weighted.value (scale⁻¹ • point) (axial : CellCircle)
  rw [AddCircle.coe_add_period]

def inverseScaledDiskPoint (scale : ℝ) (positive : 0 < scale) (point : SpatialPlane) (inside : ‖point‖ ≤ scale) : ClosedDisk :=
  ⟨scale⁻¹ • point,by
    change ‖scale⁻¹ • point‖ ≤ 1
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr positive.le)]
    exact (mul_le_mul_of_nonneg_left inside (inv_nonneg.mpr positive.le)).trans_eq (inv_mul_cancel₀ positive.ne')⟩

theorem rescaledWeightedInterior_actual {dimension : ℕ} (weighted : DiskCellClosedJet dimension)
    (scale : ℝ) (positive : 0 < scale) (point : SpatialPlane) (inside : ‖point‖ ≤ scale) (axial : ℝ) :
    rescaledWeightedInterior weighted scale (assembleSpatialCell point axial) =
      weighted.value (inverseScaledDiskPoint scale positive point inside,(axial : CellCircle)) := by
  simp only [rescaledWeightedInterior,ambientExtensionCellLift,planarPart_assembleSpatialCell]
  exact ambientExtension_inside weighted.value _ (inverseScaledDiskPoint scale positive point inside).property _

theorem rescaledWeightedInterior_cell {dimension : ℕ} (weighted : DiskCellClosedJet dimension)
    (scale : ℝ) (positive : 0 < scale) (point : SpatialPlane) (inside : ‖point‖ ≤ scale) (cell : ℤ) :
    angularCoefficient (fun axial => rescaledWeightedInterior weighted scale (assembleSpatialCell point axial)) cell =
      (diskCellFourierCoefficientJet weighted cell).value (inverseScaledDiskPoint scale positive point inside) := by
  simp_rw [rescaledWeightedInterior_actual weighted scale positive point inside]
  rw [diskCellFourierCoefficientJet_value,diskCellFourierValue_apply]
  exact angularCoefficient_circle (fun circle => weighted.value (inverseScaledDiskPoint scale positive point inside,circle)) cell

end Grad.CartesianCoreRecovery

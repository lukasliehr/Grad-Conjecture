import AKBV10SameWeightedClosedJet

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators Topology
namespace Grad.CartesianCoreRecovery
open Grad.ClosedJets Grad.CartesianState Grad.DiskExtension.Operator Grad.ActualSmoothPhysicalField

variable {dimension : ℕ} (field : SpatialCell → ComplexEuclidean dimension)
    (smooth : ContDiffOn ℝ ∞ field closedUnitCylinder)
    (periodic : ∀ point : SpatialPlane, Function.Periodic
      (fun axial => field (assembleSpatialCell point axial)) (2 * Real.pi))

def periodicCylinderPull : C(ClosedDisk × ℝ,ComplexEuclidean dimension) where
  toFun point := field (assembleSpatialCell point.1.val point.2)
  continuous_toFun := smooth.continuousOn.comp_continuous
    (assembleSpatialCellCLM.continuous.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))
    (fun point => by
      change ‖planarPart (assembleSpatialCell point.1.val point.2)‖ ≤ 1
      rw [planarPart_assembleSpatialCell]
      exact point.1.property)

include periodic in
theorem periodicCylinderPull_factors :
    Function.FactorsThrough (periodicCylinderPull field smooth) closedCylinderQuotient := by
  rintro ⟨first,one⟩ ⟨second,two⟩ same
  have planar : first = second := congrArg Prod.fst same
  subst second
  have cell : (one : CellCircle) = (two : CellCircle) := congrArg Prod.snd same
  exact Grad.ActualCartesianDescent.periodic_value_of_angle_eq _ (periodic first.val) cell

def periodicCylinderValue : C(DiskCellDomain,ComplexEuclidean dimension) :=
  closedCylinderQuotient_isQuotientMap.lift (periodicCylinderPull field smooth)
    (periodicCylinderPull_factors field smooth periodic)

theorem periodicCylinderValue_actual (point : ClosedDisk) (axial : ℝ) :
    periodicCylinderValue field smooth periodic (point,(axial : CellCircle)) =
      field (assembleSpatialCell point.val axial) := by
  change (periodicCylinderValue field smooth periodic).comp closedCylinderQuotient (point,axial) = _
  rw [periodicCylinderValue,Topology.IsQuotientMap.lift_comp]
  rfl

theorem periodicCylinderValue_lift :
    EqOn (diskCellLift (periodicCylinderValue field smooth periodic)) field closedUnitCylinder := by
  intro point inside
  rw [diskCellLift,dif_pos inside]
  change periodicCylinderValue field smooth periodic
    (⟨planarPart point,inside⟩,(point 2 : CellCircle)) = _
  rw [periodicCylinderValue_actual]
  congr 1
  ext coordinate
  fin_cases coordinate <;> rfl

/-- A genuine periodic field smooth within the closed cylinder determines the actual disk-cell closed jet. -/
def periodicClosedCylinderJet : DiskCellClosedJet dimension :=
  closedCylinderJet (periodicCylinderValue field smooth periodic)
    (smooth.congr (periodicCylinderValue_lift field smooth periodic))

theorem periodicClosedCylinderJet_actual (point : ClosedDisk) (axial : ℝ) :
    (periodicClosedCylinderJet field smooth periodic).value (point,(axial : CellCircle)) =
      field (assembleSpatialCell point.val axial) :=
  periodicCylinderValue_actual field smooth periodic point axial

end Grad.CartesianCoreRecovery

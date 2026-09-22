import NGP01OperatorBound
import P0910ExteriorGrade
import P0910OperatorCore

noncomputable section

set_option maxHeartbeats 800000

open Set
open scoped BigOperators

namespace Grad.CartesianState

open Grad.ClosedJets
open Grad.DiskExtension.Operator

local instance ngp02CellPeriodPositive : Fact (0 < 2 * Real.pi) :=
  ⟨by positivity⟩

/-- The literal closed physical collar of radius `4/3`. -/
abbrev PhysicalCollar := Metric.closedBall (0 : SpatialPlane) (4 / 3 : ℝ)

/-- The physical collar together with the original `2π` cell circle. -/
abbrev PhysicalCollarDomain := PhysicalCollar × CellCircle

local instance ngp02PhysicalCollarCompactSpace : CompactSpace PhysicalCollar := by
  rw [← isCompact_iff_compactSpace]
  exact isCompact_closedBall (0 : SpatialPlane) (4 / 3 : ℝ)

/-- Quotient the two physical planar coordinates with spatial period four. -/
def physicalCollarToTorus (point : PhysicalCollarDomain) : TorusCellDomain :=
  ((((point.1.val 0 : ℝ) : SpatialCircle),
    ((point.1.val 1 : ℝ) : SpatialCircle)), point.2)

theorem continuous_physicalCollarToTorus : Continuous physicalCollarToTorus := by
  unfold physicalCollarToTorus
  fun_prop

def physicalCollarToTorusContinuousMap :
    C(PhysicalCollarDomain, TorusCellDomain) where
  toFun := physicalCollarToTorus
  continuous_toFun := continuous_physicalCollarToTorus

/-- Assemble the coordinate derivatives of a torus field into its genuine
Euclidean multilinear derivative. -/
def torusPhysicalOperatorDerivative {dimension : ℕ}
    (field : TorusSmoothField dimension) (order : ℕ) :
    C(TorusCellDomain,
      SpatialCell [×order]→L[ℝ] ComplexEuclidean dimension) where
  toFun point := ∑ word : MixedCartesianWord order,
    (spatialCellWordCoefficient word).smulRight
      (torusDerivative field order word point)
  continuous_toFun := by
    apply continuous_finsetSum
    intro word _
    exact ((ContinuousMultilinearMap.smulRightL ℝ
      (fun _ : Fin order => SpatialCell) (ComplexEuclidean dimension)
      (spatialCellWordCoefficient word)).continuous.comp
        (torusDerivative field order word).continuous)

/-- The genuine derivative operator of a torus field restricted to the
physical radius-`4/3` collar. -/
def collarPhysicalOperatorDerivative {dimension : ℕ}
    (field : TorusSmoothField dimension) (order : ℕ) :
    C(PhysicalCollarDomain,
      SpatialCell [×order]→L[ℝ] ComplexEuclidean dimension) :=
  (torusPhysicalOperatorDerivative field order).comp
    physicalCollarToTorusContinuousMap

/-- The finite collection whose maximum is the exact collar `C^j` norm. -/
def collarPhysicalDerivativeNorms {dimension : ℕ}
    (field : TorusSmoothField dimension) (j : ℕ) : Finset ℝ :=
  Finset.univ.image (fun order : Fin (j + 1) =>
    ‖collarPhysicalOperatorDerivative field order.val‖)

theorem collarPhysicalDerivativeNorms_nonempty {dimension : ℕ}
    (field : TorusSmoothField dimension) (j : ℕ) :
    (collarPhysicalDerivativeNorms field j).Nonempty := by
  exact Finset.univ_nonempty.image _

/-- The literal `C^j` norm on `D̄_(4/3) × T`: the maximum of the
supremum operator norms of all Euclidean derivatives through order `j`. -/
def collarPhysicalCNorm {dimension : ℕ}
    (field : TorusSmoothField dimension) (j : ℕ) : ℝ :=
  (collarPhysicalDerivativeNorms field j).max'
    (collarPhysicalDerivativeNorms_nonempty field j)

theorem collarPhysicalOperatorDerivative_norm_le_cNorm
    {dimension order j : ℕ} (field : TorusSmoothField dimension)
    (orderLe : order ≤ j) :
    ‖collarPhysicalOperatorDerivative field order‖ ≤
      collarPhysicalCNorm field j := by
  unfold collarPhysicalCNorm
  apply Finset.le_max'
  rw [collarPhysicalDerivativeNorms, Finset.mem_image]
  exact ⟨⟨order, Nat.lt_succ_iff.mpr orderLe⟩, Finset.mem_univ _, rfl⟩

/-- P09 preserves every closed-disk coordinate jet, assembled here into the
exact Euclidean multilinear derivative operator. -/
theorem periodizedExtension_preserves_physical_jet
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (point : DiskCellDomain) :
    torusPhysicalOperatorDerivative (periodizedExtension field) order
        (diskToTorus point) =
      closedPhysicalOperatorDerivative field order point := by
  classical
  unfold torusPhysicalOperatorDerivative closedPhysicalOperatorDerivative
  apply Finset.sum_congr rfl
  intro word _
  congr 1
  change torusDerivativeRestrictionValue (periodizedExtension field)
      order word point = closedMixedDerivative field order word point
  rw [← torusRestriction_derivative,
    ordinaryExtensionRetraction_retracts]

/-- The actual real-line lift of the collar extension. -/
def physicalCollarExtensionLift {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : PhysicalCollar)
    (cell : ℝ) : ComplexEuclidean dimension :=
  (periodizedExtension field).value
    ((((point.val 0 : ℝ) : SpatialCircle),
      ((point.val 1 : ℝ) : SpatialCircle)), (cell : CellCircle))

theorem physicalCollarExtensionLift_periodic {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : PhysicalCollar)
    (cell : ℝ) :
    physicalCollarExtensionLift field point (cell + 2 * Real.pi) =
      physicalCollarExtensionLift field point cell := by
  unfold physicalCollarExtensionLift
  have circleEquality :
      (((cell + 2 * Real.pi : ℝ) : CellCircle)) =
        ((cell : ℝ) : CellCircle) :=
    AddCircle.coe_add_period (2 * Real.pi) cell
  rw [circleEquality]

theorem periodizedExtension_preserves_reality {dimension : ℕ}
    (field : DiskCellClosedJet dimension)
    (reality : IsRealDiskCellField field) :
    IsRealTorusField (periodizedExtension field) :=
  periodizedExtension_real field reality

end Grad.CartesianState

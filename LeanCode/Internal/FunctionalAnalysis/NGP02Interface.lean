import NGP02TorusBound

noncomputable section

namespace Grad.CartesianState

open Grad.ClosedJets
open Grad.DiskExtension.Operator

local instance ngp02InterfaceCellPeriodPositive : Fact (0 < 2 * Real.pi) :=
  ⟨by positivity⟩

/-- Real-line lift of an arbitrary torus field on the physical collar. -/
def torusPhysicalCollarLift {dimension : ℕ}
    (field : TorusSmoothField dimension) (point : PhysicalCollar)
    (cell : ℝ) : ComplexEuclidean dimension :=
  field.value ((((point.val 0 : ℝ) : SpatialCircle),
    ((point.val 1 : ℝ) : SpatialCircle)), (cell : CellCircle))

theorem torusPhysicalCollarLift_periodic {dimension : ℕ}
    (field : TorusSmoothField dimension) (point : PhysicalCollar)
    (cell : ℝ) :
    torusPhysicalCollarLift field point (cell + 2 * Real.pi) =
      torusPhysicalCollarLift field point cell := by
  unfold torusPhysicalCollarLift
  have circleEquality :
      (((cell + 2 * Real.pi : ℝ) : CellCircle)) =
        ((cell : ℝ) : CellCircle) :=
    AddCircle.coe_add_period (2 * Real.pi) cell
  rw [circleEquality]

/-- Exact NG_P02 contract.  One parameter-independent operator `E`, fixed
before the grade, preserves every disk jet and satisfies every physical
collar `C^j` estimate. -/
def PhysicalCollarExtensionGoal : Prop :=
  ∀ dimension : ℕ,
    ∃ E : DiskCellClosedJet dimension → TorusSmoothField dimension,
      E = (fun field => periodizedExtension field) ∧
      (∀ grade : ℕ, ∃ factor : ℝ, 0 ≤ factor ∧
        ∀ field : DiskCellClosedJet dimension,
          collarPhysicalCNorm (E field) grade ≤
            factor * closedPhysicalCNorm field grade) ∧
      (∀ (field : DiskCellClosedJet dimension) (order : ℕ)
          (point : DiskCellDomain),
        torusPhysicalOperatorDerivative (E field) order (diskToTorus point) =
          closedPhysicalOperatorDerivative field order point) ∧
      (∀ field : DiskCellClosedJet dimension,
        IsRealDiskCellField field → IsRealTorusField (E field)) ∧
      (∀ (field : DiskCellClosedJet dimension) (point : PhysicalCollar)
          (cell : ℝ),
        torusPhysicalCollarLift (E field) point (cell + 2 * Real.pi) =
          torusPhysicalCollarLift (E field) point cell)

end Grad.CartesianState

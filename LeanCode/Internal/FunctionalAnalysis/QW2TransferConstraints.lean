import QW1TransferReality

noncomputable section

namespace Grad.ConstrainedTransfer

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.CompletedReality Grad.RealFixedRanges Grad.SmoothingFamily Grad.Cor18 Grad.BoundaryTrace

theorem boundaryDiskPoint_eq_polar (angle : ℝ) :
    boundaryDiskPoint (angle : CellCircle) = polarClosedPoint 1 (by norm_num) angle := by
  apply Subtype.ext
  change boundaryCirclePoint (angle : CellCircle) = _
  rw [boundaryCirclePoint_coe, polarClosedPoint_coordinates]
  simp [collarPlane]

theorem rowFunction_coe_radial (parameters : PhaseParameters) (field : ACore parameters 2)
    (cell : ℤ) (angle : ℝ) :
    rowFunction parameters field cell (angle : CellCircle) =
      radialComponentAt angle ((field.1 cell).value (polarClosedPoint 1 (by norm_num) angle)) := by
  rw [rowFunction, boundaryCirclePoint_coe, boundaryDiskPoint_eq_polar]
  simp [collarPlane, radialComponentAt]

/-- The N19 radial identity is exactly the N29 physical-row input function,
on the actual quotient circle rather than a different trace convention. -/
theorem transfer_rowFunction (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain)
    (field : ACore parameters 3) (cell : ℤ) :
    rowFunction parameters (rowField parameters second insideSecond
      (seedTransfer parameters first insideFirst second insideSecond field)) cell =
      rowFunction parameters (rowField parameters first insideFirst field) cell := by
  funext angle
  refine Quotient.inductionOn angle ?_
  intro angle
  rw [rowFunction_coe_radial, rowFunction_coe_radial]
  exact seedTransfer_radial parameters first insideFirst second insideSecond field cell 1 (by norm_num) angle

/-- Literal N18 preserves the exact high-angular physical outer row. -/
theorem seedTransfer_physicalRow (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain)
    (field : ACore parameters 3) :
    physicalRow parameters second insideSecond (seedTransfer parameters first insideFirst second insideSecond field) =
      physicalRow parameters first insideFirst field := by
  apply Subtype.ext
  funext mode
  change physicalRowFamily parameters second insideSecond
    (seedTransfer parameters first insideFirst second insideSecond field) mode =
      physicalRowFamily parameters first insideFirst field mode
  simp only [physicalRowFamily, transfer_rowFunction]

theorem seedTransfer_vectorConstraints (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain)
    (field : ACore parameters 3) (constraints : VectorConstraints parameters first insideFirst field) :
    VectorConstraints parameters second insideSecond (seedTransfer parameters first insideFirst second insideSecond field) := by
  refine ⟨seedTransfer_zero_first_jets parameters first insideFirst second insideSecond field constraints.1,
    seedTransfer_poloidal_gauge parameters first insideFirst second insideSecond field,
    seedTransfer_toroidal_gauge parameters first insideFirst second insideSecond field, ?_⟩
  rw [seedTransfer_physicalRow]
  exact constraints.2.2.2

end Grad.ConstrainedTransfer

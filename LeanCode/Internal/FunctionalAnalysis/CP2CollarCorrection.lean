import CP1SupportJets

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Cor18

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Gauges Grad.BoundaryLift Grad.BoundaryTrace

/-- The two literal component insertions of scalars into the plane. -/
def scalarInsertion (coordinate : Fin 2) : ComplexEuclidean 1 →L[ℂ] ComplexEuclidean 2 :=
  ContinuousLinearMap.smulRight (EuclideanSpace.proj (0 : Fin 1))
    (EuclideanSpace.single coordinate (1 : ℂ))

theorem scalarInsertion_apply (coordinate : Fin 2) (value : ComplexEuclidean 1) :
    scalarInsertion coordinate value =
      value 0 • EuclideanSpace.single coordinate (1 : ℂ) := rfl

@[simp] theorem scalarInsertion_zero (coordinate : Fin 2) :
    scalarInsertion coordinate 0 = 0 := map_zero _

/-- The literal collar coordinate field `y • L` of a scalar core field:
componentwise coordinate multiplication inserted into the plane. -/
def coordinateVector (parameters : PhaseParameters) :
    ACore parameters 1 →ₗ[ℂ] ACore parameters 2 :=
  (valueMapCore (scalarInsertion 0) parameters).comp
      (coordinateCore parameters 0) +
    (valueMapCore (scalarInsertion 1) parameters).comp
      (coordinateCore parameters 1)

theorem coordinateVector_value (parameters : PhaseParameters)
    (field : ACore parameters 1) (cell : ℤ) (point : ClosedDisk) :
    ((coordinateVector parameters field).1 cell).value point =
      scalarInsertion 0 (point.val 0 • (field.1 cell).value point) +
        scalarInsertion 1 (point.val 1 • (field.1 cell).value point) := by
  show ((valueMapCore (scalarInsertion 0) parameters
      (coordinateCore parameters 0 field) +
    valueMapCore (scalarInsertion 1) parameters
      (coordinateCore parameters 1 field)).1 cell).value point = _
  rw [Submodule.coe_add, Pi.add_apply, closedJet_value_add]
  show (valueMapJet (scalarInsertion 0)
      ((coordinateCore parameters 0 field).1 cell)).value point +
    (valueMapJet (scalarInsertion 1)
      ((coordinateCore parameters 1 field).1 cell)).value point = _
  rw [valueMapJet_value, valueMapJet_value, coordinateCore_apply,
    coordinateCore_apply, realCoordinateJet_value, realCoordinateJet_value]

theorem coordinateVector_vanishes (parameters : PhaseParameters)
    (field : ACore parameters 1) (cell : ℤ) (point : ClosedDisk)
    (vanishing : (field.1 cell).value point = 0) :
    ((coordinateVector parameters field).1 cell).value point = 0 := by
  rw [coordinateVector_value, vanishing, smul_zero, smul_zero, map_zero,
    map_zero, add_zero]

/-- The literal N29 collar correction `C_∂ b = ι M (y • E_∂ b)` over the
accepted scalar boundary lift, seed multiplication and planar inclusion. -/
def collarCorrection (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) :
    BoundaryCore parameters 1 →ₗ[ℂ] ACore parameters 3 :=
  (planarInclusionCore parameters).comp
    ((seedMatrixCore parameters parameter inside).comp
      ((coordinateVector parameters).comp (boundaryLift parameters)))

/-- The seed multiplication preserves pointwise vanishing across all cells. -/
theorem seedMatrixCore_vanishes (parameters : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (field : ACore parameters 2) (point : ClosedDisk)
    (vanishing : ∀ cell : ℤ, (field.1 cell).value point = 0) (cell : ℤ) :
    ((seedMatrixCore parameters parameter inside field).1 cell).value point = 0 := by
  have expand : seedMatrixCore parameters parameter inside field =
      field + seedDeviationCore parameters parameter inside 0 field := rfl
  rw [expand, Submodule.coe_add, Pi.add_apply, closedJet_value_add,
    ContinuousMap.add_apply, vanishing cell, zero_add]
  have literal := seedDeviationCore_literal_derivatives parameters parameter
    inside 0 field cell 0 emptyCartesianWord point
  rw [closedDerivative_zero_order] at literal
  have zeroSummand : (fun shift : ℤ => Seed.actualCells 0 parameter shift
      (closedDerivative (field.1 (cell - shift)) 0 emptyCartesianWord point)) =
      fun _ => 0 := by
    funext shift
    rw [closedDerivative_zero_order, vanishing (cell - shift), map_zero]
  rw [zeroSummand] at literal
  exact literal.unique hasSum_zero

/-- The collar correction vanishes on the inner three-quarter ball. -/
theorem collarCorrection_vanishes (parameters : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (values : BoundaryCore parameters 1) (cell : ℤ) (point : ClosedDisk)
    (inner : ‖point.val‖ ≤ (3 / 4 : ℝ)) :
    ((collarCorrection parameters parameter inside values).1 cell).value point = 0 := by
  show (valueMapJet planarInclusionMap
    ((seedMatrixCore parameters parameter inside
      (coordinateVector parameters (boundaryLift parameters values))).1 cell)).value
        point = 0
  rw [valueMapJet_value]
  rw [seedMatrixCore_vanishes parameters parameter inside _ point (fun inner_cell =>
    coordinateVector_vanishes parameters _ inner_cell point
      (boundaryLift_zero_inner parameters values inner_cell point inner)) cell]
  exact map_zero _

/-- The collar correction has zero value and zero first Cartesian jet at
the axis, in both accepted jet vocabularies. -/
theorem collarCorrection_originValue (parameters : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (values : BoundaryCore parameters 1) (cell : ℤ) :
    Grad.AxisSplit.originValue
      ((collarCorrection parameters parameter inside values).1 cell) = 0 :=
  vanishing_ball_originValue _ (3 / 4) (by norm_num)
    (fun point inner => collarCorrection_vanishes parameters parameter inside
      values cell point inner)

theorem collarCorrection_originPartial (parameters : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (values : BoundaryCore parameters 1) (cell : ℤ) (direction : Fin 2) :
    Grad.AxisSplit.originPartial direction
      ((collarCorrection parameters parameter inside values).1 cell) = 0 :=
  vanishing_ball_originPartial _ (3 / 4) (by norm_num) (by norm_num)
    (fun point inner => collarCorrection_vanishes parameters parameter inside
      values cell point inner) direction

theorem collarCorrection_zeroCartesianFirstJets (parameters : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (values : BoundaryCore parameters 1) (cell : ℤ) :
    ZeroCartesianFirstJets
      ((collarCorrection parameters parameter inside values).1 cell) :=
  vanishing_ball_zeroCartesianFirstJets _ (3 / 4) (by norm_num) (by norm_num)
    (fun point inner => collarCorrection_vanishes parameters parameter inside
      values cell point inner)

end Grad.Cor18

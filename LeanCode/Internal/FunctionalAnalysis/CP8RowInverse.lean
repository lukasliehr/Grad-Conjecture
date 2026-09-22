import CP7RowOperator

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Cor18

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Gauges Grad.BoundaryTrace Grad.BoundaryLift

/-! # N30: the physical row inverts the collar correction

`B_M C_{∂,M} b = b` on high-angular boundary data: the seed-inverted planar
field of the collar correction is the coordinate field `y • E_∂ b` of the
accepted lift, whose radial contraction at the unit circle is the boundary
value of the lift, whose Fourier coefficients are exactly `b` by the accepted
right-inverse law of the lift. -/

/-- The seed-inverted planar field of the collar correction is the
coordinate field of the lift (`M⁻¹ M = I` at the multiplier level). -/
theorem rowField_collarCorrection (parameters : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (values : BoundaryCore parameters 1) :
    rowField parameters parameter inside
        (collarCorrection parameters parameter inside values) =
      coordinateVector parameters (boundaryLift parameters values) := by
  unfold rowField collarCorrection
  simp only [LinearMap.comp_apply]
  rw [planarPartCore_planarInclusionCore, seedInverse_seedMatrix_core]

/-- The circle point has unit Euclidean length: `c₀² + c₁² = 1`. -/
theorem boundaryCirclePoint_sq_sum (angle : CellCircle) :
    boundaryCirclePoint angle 0 ^ 2 + boundaryCirclePoint angle 1 ^ 2 = 1 := by
  have norm := boundaryCirclePoint_norm angle
  have sq : ‖boundaryCirclePoint angle‖ ^ 2 = ∑ index, ‖boundaryCirclePoint angle index‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 _ (boundaryCirclePoint angle)
  rw [norm, one_pow, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs] at sq
  exact sq.symm

/-- The radial contraction of a coordinate field at the unit circle is the
boundary value of the scalar field. -/
theorem rowFunction_coordinateVector (parameters : PhaseParameters)
    (field : ACore parameters 1) (cell : ℤ) (angle : CellCircle) :
    rowFunction parameters (coordinateVector parameters field) cell angle =
      ((field.1 cell).value (boundaryDiskPoint angle)) 0 := by
  unfold rowFunction
  rw [coordinateVector_value]
  have pointLaw : (boundaryDiskPoint angle).val = boundaryCirclePoint angle := rfl
  simp only [scalarInsertion_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply,
    smul_eq_mul, pointLaw, Complex.real_smul]
  simp
  have unit := boundaryCirclePoint_sq_sum angle
  have unitC : ((boundaryCirclePoint angle 0 : ℝ) : ℂ) ^ 2 +
      ((boundaryCirclePoint angle 1 : ℝ) : ℂ) ^ 2 = 1 := by
    have cast := congrArg (fun r : ℝ => (r : ℂ)) unit
    push_cast at cast
    exact cast
  linear_combination (((field.1 cell).value (boundaryDiskPoint angle)) 0) * unitC

/-- N30 at the level of boundary families. -/
theorem physicalRowFamily_collarCorrection (parameters : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (values : BoundaryCore parameters 1) (high : HighBoundarySupport parameters values)
    (mode : ℤ × ℤ) :
    physicalRowFamily parameters parameter inside
        (collarCorrection parameters parameter inside values) mode = values.1 mode := by
  obtain ⟨angular, cell⟩ := mode
  unfold physicalRowFamily
  split_ifs with low
  · exact (high (angular, cell) low).symm
  · rw [rowField_collarCorrection]
    have functions : rowFunction parameters
        (coordinateVector parameters (boundaryLift parameters values)) cell =
        fun angle => (((boundaryLift parameters values).1 cell).value (boundaryDiskPoint angle)) 0 :=
      funext fun angle => rowFunction_coordinateVector parameters _ cell angle
    rw [functions, fourierCoeff_component parameters (boundaryLift parameters values) cell angular 0,
      boundaryLift_coefficient]
    ext index
    fin_cases index
    simp

/-- N30: `B_M C_{∂,M} b = b` on high-angular boundary data. -/
theorem physicalRow_collarCorrection (parameters : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (values : BoundaryCore parameters 1) (high : HighBoundarySupport parameters values) :
    physicalRow parameters parameter inside
        (collarCorrection parameters parameter inside values) = values := by
  apply Subtype.ext
  funext mode
  exact physicalRowFamily_collarCorrection parameters parameter inside values high mode

/-- The physical row always has high angular support. -/
theorem physicalRow_highSupport (parameters : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (state : ACore parameters 3) :
    HighBoundarySupport parameters (physicalRow parameters parameter inside state) :=
  fun mode low => physicalRowFamily_high parameters parameter inside state mode low

/-- The literal outer correction `I - C_{∂,M} B_M`. -/
def outerCorrection (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) : ACore parameters 3 →ₗ[ℂ] ACore parameters 3 :=
  LinearMap.id - (collarCorrection parameters parameter inside).comp
    (physicalRow parameters parameter inside)

theorem outerCorrection_apply (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (state : ACore parameters 3) :
    outerCorrection parameters parameter inside state =
      state - collarCorrection parameters parameter inside
        (physicalRow parameters parameter inside state) := rfl

/-- The outer correction annihilates the physical row. -/
theorem physicalRow_outerCorrection (parameters : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (state : ACore parameters 3) :
    physicalRow parameters parameter inside (outerCorrection parameters parameter inside state) = 0 := by
  rw [outerCorrection_apply, map_sub, physicalRow_collarCorrection parameters parameter inside _
    (physicalRow_highSupport parameters parameter inside state), sub_self]

/-- Fields with zero physical row are fixed by the outer correction. -/
theorem outerCorrection_fixes (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (state : ACore parameters 3)
    (rowZero : physicalRow parameters parameter inside state = 0) :
    outerCorrection parameters parameter inside state = state := by
  rw [outerCorrection_apply, rowZero, map_zero, sub_zero]

end Grad.Cor18

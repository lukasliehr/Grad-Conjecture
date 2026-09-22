import TameChartSum
import QuotientValueMap
import GaugeMultiplierPhysical
import GaugeSeed

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct
open Grad.Constraints.Multipliers Grad.Constraints.Gauges

/-! The fixed fields of the normalized chart: the literal reference
inclusions `ι(y₁,y₂) = y₁ e₁ + y₂ e₃` and `e_T = e₂`, the planar coordinate
field, the seed field `ι M_p y`, the literal Q17 seed scalar
`w_M = -(1/4) R (|R(ι M y)|² - r²)`, and the scalar coefficient multiplier
with its coefficient linearity. -/

variable {parameters : PhaseParameters}

/-- The literal reference planar inclusion `ι(y₁,y₂) = y₁ e₁ + y₂ e₃`. -/
def tamePlanarInclusion : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun value => WithLp.toLp 2 ![value 0, 0, value 1]
      map_add' := by
        intro first second
        apply PiLp.ext
        intro coordinate
        fin_cases coordinate <;> simp
      map_smul' := by
        intro scalar value
        apply PiLp.ext
        intro coordinate
        fin_cases coordinate <;> simp }

/-- The literal reference tangential inclusion `e_T = e₂`. -/
def tameTangentInclusion : ComplexEuclidean 1 →L[ℂ] ComplexEuclidean 3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun value => WithLp.toLp 2 ![0, value 0, 0]
      map_add' := by
        intro first second
        apply PiLp.ext
        intro coordinate
        fin_cases coordinate <;> simp
      map_smul' := by
        intro scalar value
        apply PiLp.ext
        intro coordinate
        fin_cases coordinate <;> simp }

/-- The scalar coordinate fields `y₁, y₂` at the constant cell mode. -/
def tameCoordinateScalarField (parameters : PhaseParameters) (index : Fin 2) :
    ACore parameters 1 :=
  singletonCore parameters
    (coordinateJet index (constantValueJet (EuclideanSpace.single 0 1)))

/-- The planar coordinate field `y` at the constant cell mode. -/
def tamePlanarCoordinateField (parameters : PhaseParameters) : ACore parameters 2 :=
  singletonCore parameters
    (coordinateJet 0 (constantValueJet (EuclideanSpace.single 0 1))) +
  singletonCore parameters
    (coordinateJet 1 (constantValueJet (EuclideanSpace.single 1 1)))

/-- The seed planar field `M_p y`. -/
def tameSeedPlanarField (parameters : PhaseParameters)
    (seed : Grad.Constraints.Seed.Parameters)
    (inside : seed ∈ Grad.Constraints.Seed.parameterDomain) : ACore parameters 2 :=
  seedMatrixCore parameters seed inside (tamePlanarCoordinateField parameters)

/-- The included seed field `ι M_p y`. -/
def tameSeedField (parameters : PhaseParameters)
    (seed : Grad.Constraints.Seed.Parameters)
    (inside : seed ∈ Grad.Constraints.Seed.parameterDomain) : ACore parameters 3 :=
  valueMapCore parameters tamePlanarInclusion (tameSeedPlanarField parameters seed inside)

/-- The radius-square field `r² = y₁·y₁ + y₂·y₂`. -/
def tameRadiusSquareField (parameters : PhaseParameters) : ACore parameters 1 :=
  coordinateCore parameters 0 (tameCoordinateScalarField parameters 0) +
    coordinateCore parameters 1 (tameCoordinateScalarField parameters 1)

/-- The Q17 gauge energy `E_M = |R(ι M y)|² - r²`. -/
def tameSeedEnergy (parameters : PhaseParameters)
    (seed : Grad.Constraints.Seed.Parameters)
    (inside : seed ∈ Grad.Constraints.Seed.parameterDomain) : ACore parameters 1 :=
  actualMultilinearProduct parameters physicalDotProduct
    ![rotationCore parameters (tameSeedField parameters seed inside),
      rotationCore parameters (tameSeedField parameters seed inside)] -
    tameRadiusSquareField parameters

/-- The literal Q17 seed scalar `w_M = -(1/4) R E_M`. -/
def tameSeedScalar (parameters : PhaseParameters)
    (seed : Grad.Constraints.Seed.Parameters)
    (inside : seed ∈ Grad.Constraints.Seed.parameterDomain) : ACore parameters 1 :=
  (-(4 : ℂ)⁻¹) • rotationCore parameters (tameSeedEnergy parameters seed inside)

/-! ### The scalar coefficient multiplier -/

/-- A scalar coefficient family as diagonal operators. -/
def tameScalarOperator (dimension : ℕ) (family : ℤ → ℂ) :
    ℤ → ComplexEuclidean dimension →L[ℂ] ComplexEuclidean dimension :=
  fun cell => family cell • ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)

theorem tameScalarOperator_norm {dimension : ℕ}
    [Nontrivial (ComplexEuclidean dimension)] (family : ℤ → ℂ) (cell : ℤ) :
    ‖tameScalarOperator dimension family cell‖ = ‖family cell‖ := by
  rw [tameScalarOperator, norm_smul, ContinuousLinearMap.norm_id, mul_one]

theorem tameScalarOperator_envelopeTerm {dimension : ℕ}
    [Nontrivial (ComplexEuclidean dimension)] (grade : ℕ) (family : ℤ → ℂ) (cell : ℤ) :
    envelopeTerm parameters grade (tameScalarOperator dimension family) cell =
      tameEnvelopeTerm parameters grade family cell := by
  rw [envelopeTerm, tameEnvelopeTerm, tameWeight, tameScalarOperator_norm]

theorem tameScalarOperator_summable {dimension : ℕ}
    [Nontrivial (ComplexEuclidean dimension)] (family : TameCoefficient parameters) :
    ∀ grade, Summable (envelopeTerm parameters grade
      (tameScalarOperator dimension family.val)) := by
  intro grade
  apply (family.property grade).congr
  intro cell
  rw [tameScalarOperator_envelopeTerm]

/-- Multiplication of an original field by a scalar coefficient family. -/
def tameScalarMultiplier (dimension : ℕ) [Nontrivial (ComplexEuclidean dimension)]
    (family : TameCoefficient parameters) :
    ACore parameters dimension →ₗ[ℂ] ACore parameters dimension :=
  smoothMultiplier parameters (tameScalarOperator dimension family.val)
    (tameScalarOperator_summable family)

theorem tameScalarMultiplier_bound (dimension : ℕ)
    [Nontrivial (ComplexEuclidean dimension)] (family : TameCoefficient parameters)
    (field : ACore parameters dimension) (grade : ℕ) :
    originalGradeNorm grade (tameScalarMultiplier dimension family field) ≤
      multiplierConstant grade parameters.gamma * coefficientEnvelope grade family *
        originalGradeNorm grade field := by
  have envelope_eq : envelope parameters grade (tameScalarOperator dimension family.val) =
      coefficientEnvelope grade family := by
    rw [envelope, coefficientEnvelope, tameEnvelope]
    exact tsum_congr (fun cell => tameScalarOperator_envelopeTerm grade family.val cell)
  have bound := smoothMultiplier_bound parameters (tameScalarOperator dimension family.val)
    (tameScalarOperator_summable family) field grade
  rw [envelope_eq] at bound
  exact bound

theorem tameScalarMultiplier_value_hasSum (dimension : ℕ)
    [Nontrivial (ComplexEuclidean dimension)] (family : TameCoefficient parameters)
    (field : ACore parameters dimension) (cell : ℤ) (point : ClosedDisk) :
    HasSum (fun shift : ℤ => family.val shift • (field.1 (cell - shift)).value point)
      (((tameScalarMultiplier dimension family field).1 cell).value point) := by
  have base := smoothMultiplier_value_hasSum parameters
    (tameScalarOperator dimension family.val) (tameScalarOperator_summable family)
    field cell point
  have summand_eq : (fun shift : ℤ => tameScalarOperator dimension family.val shift
      ((field.1 (cell - shift)).value point)) =
      fun shift : ℤ => family.val shift • (field.1 (cell - shift)).value point := by
    funext shift
    rw [tameScalarOperator]
    simp
  rwa [summand_eq] at base

/-- Coefficient additivity of the scalar multiplier. -/
theorem tameScalarMultiplier_add (dimension : ℕ)
    [Nontrivial (ComplexEuclidean dimension)]
    (first second : TameCoefficient parameters) (field : ACore parameters dimension) :
    tameScalarMultiplier dimension (first + second) field =
      tameScalarMultiplier dimension first field +
        tameScalarMultiplier dimension second field := by
  apply Subtype.ext
  funext cell
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have first_sum := tameScalarMultiplier_value_hasSum dimension first field cell point
  have second_sum := tameScalarMultiplier_value_hasSum dimension second field cell point
  have combined_sum := tameScalarMultiplier_value_hasSum dimension (first + second)
    field cell point
  have summand_split : (fun shift : ℤ =>
      (first + second).val shift • (field.1 (cell - shift)).value point) =
      fun shift : ℤ => first.val shift • (field.1 (cell - shift)).value point +
        second.val shift • (field.1 (cell - shift)).value point := by
    funext shift
    rw [tameAdd_val, Pi.add_apply, add_smul]
  rw [summand_split] at combined_sum
  have value_eq := combined_sum.unique (first_sum.add second_sum)
  have rhs_eq : (((tameScalarMultiplier dimension first field +
      tameScalarMultiplier dimension second field) :
        ACore parameters dimension).1 cell).value point =
      ((tameScalarMultiplier dimension first field).1 cell).value point +
        ((tameScalarMultiplier dimension second field).1 cell).value point := by
    show (((tameScalarMultiplier dimension first field).1 cell) +
      ((tameScalarMultiplier dimension second field).1 cell)).value point = _
    rw [closedJet_value_add, ContinuousMap.add_apply]
  rw [rhs_eq]
  exact value_eq

/-- Coefficient scalar compatibility of the scalar multiplier. -/
theorem tameScalarMultiplier_smul (dimension : ℕ)
    [Nontrivial (ComplexEuclidean dimension)] (scalar : ℂ)
    (family : TameCoefficient parameters) (field : ACore parameters dimension) :
    tameScalarMultiplier dimension (scalar • family) field =
      scalar • tameScalarMultiplier dimension family field := by
  apply Subtype.ext
  funext cell
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have base_sum := tameScalarMultiplier_value_hasSum dimension family field cell point
  have scaled_sum := tameScalarMultiplier_value_hasSum dimension (scalar • family)
    field cell point
  have summand_scale : (fun shift : ℤ =>
      (scalar • family).val shift • (field.1 (cell - shift)).value point) =
      fun shift : ℤ => scalar •
        (family.val shift • (field.1 (cell - shift)).value point) := by
    funext shift
    rw [tameSmul_val, Pi.smul_apply, smul_smul, smul_eq_mul]
  rw [summand_scale] at scaled_sum
  have value_eq := scaled_sum.unique (base_sum.const_smul scalar)
  have rhs_eq : (((scalar • tameScalarMultiplier dimension family field) :
      ACore parameters dimension).1 cell).value point =
      scalar • ((tameScalarMultiplier dimension family field).1 cell).value point := by
    show ((scalar • (tameScalarMultiplier dimension family field).1 cell)).value point = _
    rw [closedJet_value_smul, ContinuousMap.smul_apply]
  rw [rhs_eq]
  exact value_eq

end Grad.NonlinearQuotientBounds

import QuotientPolynomialTerms
import AveragesConsumer
import AngularProjectionDerivatives
import AW2Consumers

noncomputable section

open scoped BigOperators ContDiff

namespace Grad.AxisSplit

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds

/-- The origin of the closed unit disk, the axis point of every cell. -/
def originPoint : ClosedDisk := ⟨0, by simp [closedUnitDisk]⟩

@[simp] theorem originPoint_val : originPoint.val = (0 : SpatialPlane) := rfl

@[simp] theorem originPoint_coordinate (coordinate : Fin 2) :
    originPoint.val coordinate = 0 := rfl

/-- The closed-jet value at the axis. -/
def originValue {dimension : ℕ} (field : ClosedJet dimension) :
    ComplexEuclidean dimension :=
  field.value originPoint

/-- The closed-jet first Cartesian derivative at the axis, through the
actual closed derivative extension, not an ambient derivative. -/
def originPartial {dimension : ℕ} (direction : Fin 2) (field : ClosedJet dimension) :
    ComplexEuclidean dimension :=
  (partialJet direction field).value originPoint

theorem originPartial_eq_closedDerivative {dimension : ℕ} (direction : Fin 2)
    (field : ClosedJet dimension) :
    originPartial direction field =
      closedDerivative field 1 (fun _ => direction) originPoint := rfl

@[simp] theorem originValue_add {dimension : ℕ} (first second : ClosedJet dimension) :
    originValue (first + second) = originValue first + originValue second := by
  unfold originValue
  rw [closedJet_value_add]
  rfl

@[simp] theorem originValue_neg {dimension : ℕ} (field : ClosedJet dimension) :
    originValue (-field) = -originValue field := by
  unfold originValue
  rw [closedJet_value_neg]
  rfl

@[simp] theorem originValue_sub {dimension : ℕ} (first second : ClosedJet dimension) :
    originValue (first - second) = originValue first - originValue second := by
  rw [sub_eq_add_neg, originValue_add, originValue_neg, ← sub_eq_add_neg]

@[simp] theorem originValue_smul {dimension : ℕ} (scalar : ℂ) (field : ClosedJet dimension) :
    originValue (scalar • field) = scalar • originValue field := by
  unfold originValue
  rw [closedJet_value_smul]
  rfl

@[simp] theorem originValue_zero {dimension : ℕ} :
    originValue (0 : ClosedJet dimension) = 0 := by
  unfold originValue
  rw [closedJet_value_zero]
  rfl

theorem originPartial_add {dimension : ℕ} (direction : Fin 2)
    (first second : ClosedJet dimension) :
    originPartial direction (first + second) =
      originPartial direction first + originPartial direction second := by
  have expand : closedDerivative (first + second) 1 (fun _ => direction) =
      closedDerivative first 1 (fun _ => direction) +
        closedDerivative second 1 (fun _ => direction) :=
    (closedDerivativeLinear (dimension := dimension) 1 (fun _ => direction)).map_add
      first second
  rw [originPartial_eq_closedDerivative, originPartial_eq_closedDerivative,
    originPartial_eq_closedDerivative, expand]
  rfl

theorem originPartial_smul {dimension : ℕ} (direction : Fin 2) (scalar : ℂ)
    (field : ClosedJet dimension) :
    originPartial direction (scalar • field) = scalar • originPartial direction field := by
  have expand : closedDerivative (scalar • field) 1 (fun _ => direction) =
      scalar • closedDerivative field 1 (fun _ => direction) :=
    (closedDerivativeLinear (dimension := dimension) 1 (fun _ => direction)).map_smul
      scalar field
  rw [originPartial_eq_closedDerivative, originPartial_eq_closedDerivative, expand]
  rfl

theorem originPartial_neg {dimension : ℕ} (direction : Fin 2) (field : ClosedJet dimension) :
    originPartial direction (-field) = -originPartial direction field := by
  have expand := originPartial_smul direction (-1 : ℂ) field
  rwa [neg_one_smul, neg_one_smul] at expand

theorem originPartial_sub {dimension : ℕ} (direction : Fin 2)
    (first second : ClosedJet dimension) :
    originPartial direction (first - second) =
      originPartial direction first - originPartial direction second := by
  rw [sub_eq_add_neg, originPartial_add, originPartial_neg, ← sub_eq_add_neg]

theorem originPartial_zero {dimension : ℕ} (direction : Fin 2) :
    originPartial direction (0 : ClosedJet dimension) = 0 := by
  have expand := originPartial_smul direction (0 : ℂ) (0 : ClosedJet dimension)
  rwa [zero_smul, zero_smul] at expand

/-- The literal first-derivative Leibniz value of a smooth-scalar-weighted
jet at an arbitrary closed point. -/
theorem smoothScalar_partial_value {dimension : ℕ}
    (scalar : SpatialPlane → ℝ) (scalarSmooth : ContDiff ℝ ∞ scalar)
    (field : ClosedJet dimension) (direction : Fin 2) (point : ClosedDisk) :
    partialCoefficient direction (smoothScalarWeightedJet scalar scalarSmooth field) point =
      spatialPartial direction scalar point.val • field.value point +
        scalar point.val • partialCoefficient direction field point := by
  let weighted := fun source => scalar source • smoothClosedExtension field source
  have weightedSmooth : ContDiff ℝ ∞ weighted :=
    scalarSmooth.smul (smoothClosedExtension_smooth field)
  have restriction : globalClosedJet weighted weightedSmooth =
      smoothScalarWeightedJet scalar scalarSmooth field := by
    apply globalClosedJet_eq_of_restriction
    intro source
    dsimp only [weighted]
    rw [smoothClosedExtension_value]
    rfl
  unfold partialCoefficient
  rw [← restriction, globalClosedJet_derivative, ← spatialPartial_eq_ordered]
  change fderiv ℝ weighted point.val (spatialBasis direction) = _
  rw [fderiv_fun_smul (scalarSmooth.differentiable (by simp)).differentiableAt
    ((smoothClosedExtension_smooth field).differentiable (by simp)).differentiableAt]
  change scalar point.val • spatialPartial direction (smoothClosedExtension field) point.val +
      spatialPartial direction scalar point.val • smoothClosedExtension field point.val = _
  rw [spatialPartial_eq_ordered direction (smoothClosedExtension field),
    smoothClosedExtension_derivative field (fun _ => direction) point,
    smoothClosedExtension_value field point]
  change scalar point.val • closedDerivative field 1 (fun _ => direction) point +
      spatialPartial direction scalar point.val • field.value point = _
  abel

theorem smoothScalarWeightedJet_value_point {dimension : ℕ}
    (scalar : SpatialPlane → ℝ) (scalarSmooth : ContDiff ℝ ∞ scalar)
    (field : ClosedJet dimension) (point : ClosedDisk) :
    (smoothScalarWeightedJet scalar scalarSmooth field).value point =
      scalar point.val • field.value point := rfl

/-- Coordinate multiplication has axis value zero. -/
theorem coordinateJet_originValue {dimension : ℕ} (coordinate : Fin 2)
    (field : ClosedJet dimension) :
    originValue (coordinateJet coordinate field) = 0 := by
  unfold originValue
  rw [coordinateJet_value, originPoint_coordinate, zero_smul]

/-- The exact axis first derivative of coordinate multiplication. -/
theorem coordinateJet_originPartial {dimension : ℕ} (direction coordinate : Fin 2)
    (field : ClosedJet dimension) :
    originPartial direction (coordinateJet coordinate field) =
      if direction = coordinate then originValue field else 0 := by
  unfold originPartial originValue
  rw [partialJet_value]
  unfold coordinateJet
  rw [smoothScalar_partial_value]
  have coordinateZero : coordinateLinear coordinate originPoint.val = 0 :=
    originPoint_coordinate coordinate
  rw [coordinateZero, zero_smul, add_zero]
  have linearPartial : spatialPartial direction (⇑(coordinateLinear coordinate))
      originPoint.val = if direction = coordinate then (1 : ℝ) else 0 := by
    unfold spatialPartial
    rw [(coordinateLinear coordinate).fderiv]
    change spatialBasis direction coordinate = _
    unfold spatialBasis
    by_cases equal : direction = coordinate
    · rw [if_pos equal, ← equal]
      change Pi.single (M := fun _ : Fin 2 => ℝ) direction 1 direction = 1
      exact Pi.single_eq_same direction 1
    · rw [if_neg equal]
      change Pi.single (M := fun _ : Fin 2 => ℝ) direction 1 coordinate = 0
      exact Pi.single_eq_of_ne (fun h => equal h.symm) 1
  rw [linearPartial]
  by_cases equal : direction = coordinate
  · rw [if_pos equal, if_pos equal, one_smul]
  · rw [if_neg equal, if_neg equal, zero_smul]

/-- The phase weight value at the axis. -/
theorem cartesianWeight_origin (parameters : PhaseParameters) (cell : ℤ) :
    cartesianWeight parameters cell originPoint.val =
      Real.exp (parameters.sigma0 * cellFrequency cell) :=
  (Grad.AnalyticWeights.Calculus.Consumer.axisWeightValuesAndDerivatives
    parameters.sigma0 parameters.gamma 1 cell).1

theorem cartesianInverseWeight_origin (parameters : PhaseParameters) (cell : ℤ) :
    cartesianInverseWeight parameters cell originPoint.val =
      Real.exp (-parameters.sigma0 * cellFrequency cell) :=
  (Grad.AnalyticWeights.Calculus.Consumer.axisWeightValuesAndDerivatives
    parameters.sigma0 parameters.gamma 1 cell).2.1

theorem cartesianWeight_origin_pos (parameters : PhaseParameters) (cell : ℤ) :
    0 < cartesianWeight parameters cell originPoint.val := by
  rw [cartesianWeight_origin]
  exact Real.exp_pos _

theorem cartesianWeight_originPartial (parameters : PhaseParameters) (cell : ℤ)
    (direction : Fin 2) :
    spatialPartial direction (cartesianWeight parameters cell) originPoint.val = 0 := by
  unfold spatialPartial
  rw [originPoint_val]
  rw [show fderiv ℝ (cartesianWeight parameters cell) (0 : SpatialPlane) = 0 from
    (Grad.AnalyticWeights.Calculus.Consumer.axisWeightValuesAndDerivatives
      parameters.sigma0 parameters.gamma 1 cell).2.2.1]
  rfl

theorem cartesianInverseWeight_originPartial (parameters : PhaseParameters) (cell : ℤ)
    (direction : Fin 2) :
    spatialPartial direction (cartesianInverseWeight parameters cell) originPoint.val = 0 := by
  unfold spatialPartial
  rw [originPoint_val]
  rw [show fderiv ℝ (cartesianInverseWeight parameters cell) (0 : SpatialPlane) = 0 from
    (Grad.AnalyticWeights.Calculus.Consumer.axisWeightValuesAndDerivatives
      parameters.sigma0 parameters.gamma 1 cell).2.2.2]
  rfl

/-- At the axis the phase gradient vanishes, so the weighted first
derivative is the weighted value of the first derivative. -/
theorem phaseWeightedJet_originPartial {dimension : ℕ} (parameters : PhaseParameters)
    (cell : ℤ) (direction : Fin 2) (field : ClosedJet dimension) :
    originPartial direction (phaseWeightedJet parameters cell field) =
      cartesianWeight parameters cell originPoint.val • originPartial direction field := by
  unfold originPartial
  rw [partialJet_value, partialJet_value]
  unfold phaseWeightedJet
  rw [smoothScalar_partial_value, cartesianWeight_originPartial, zero_smul, zero_add]

theorem phaseWeightedJet_originValue {dimension : ℕ} (parameters : PhaseParameters)
    (cell : ℤ) (field : ClosedJet dimension) :
    originValue (phaseWeightedJet parameters cell field) =
      cartesianWeight parameters cell originPoint.val • originValue field := rfl

theorem phaseInverseWeightedJet_originPartial {dimension : ℕ} (parameters : PhaseParameters)
    (cell : ℤ) (direction : Fin 2) (field : ClosedJet dimension) :
    originPartial direction (phaseInverseWeightedJet parameters cell field) =
      cartesianInverseWeight parameters cell originPoint.val •
        originPartial direction field := by
  unfold originPartial
  rw [partialJet_value, partialJet_value]
  unfold phaseInverseWeightedJet
  rw [smoothScalar_partial_value, cartesianInverseWeight_originPartial, zero_smul, zero_add]

theorem phaseInverseWeightedJet_originValue {dimension : ℕ} (parameters : PhaseParameters)
    (cell : ℤ) (field : ClosedJet dimension) :
    originValue (phaseInverseWeightedJet parameters cell field) =
      cartesianInverseWeight parameters cell originPoint.val • originValue field := rfl

/-- The value-map jet acts on the axis value through the fixed linear map. -/
theorem valueMapJet_originValue {sourceDimension targetDimension : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : ClosedJet sourceDimension) :
    originValue (valueMapJet mapping field) = mapping (originValue field) := by
  unfold originValue
  rw [valueMapJet_value]

theorem valueMapJet_originPartial {sourceDimension targetDimension : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : ClosedJet sourceDimension) (direction : Fin 2) :
    originPartial direction (valueMapJet mapping field) =
      mapping (originPartial direction field) := by
  rw [originPartial_eq_closedDerivative, originPartial_eq_closedDerivative]
  rw [valueMapJet_derivative]
  rfl

end Grad.AxisSplit

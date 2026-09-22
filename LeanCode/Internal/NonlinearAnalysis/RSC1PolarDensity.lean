import SCD31DivisionConsumer

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.SourceCollarRestriction

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.BoundaryTrace
open Grad.SourceCollarDivision

/-- Literal nonsingular restriction of a closed jet. The auxiliary smooth
extension is used only outside the closed physical disk. -/
def originalPolarValue {dimension : ℕ} (field : ClosedJet dimension) :
    ℝ × ℝ → ComplexEuclidean dimension := smoothClosedExtension field ∘ polarPlane

theorem originalPolarValue_smooth {dimension : ℕ} (field : ClosedJet dimension) :
    ContDiff ℝ ∞ (originalPolarValue field) :=
  (smoothClosedExtension_smooth field).comp polarPlane_smooth

theorem originalPolarValue_periodic {dimension : ℕ} (field : ClosedJet dimension) :
    Function.Periodic (originalPolarValue field) (0, 2 * Real.pi) := by
  intro point
  exact congrArg (smoothClosedExtension field) (polarPlane_periodic point)

theorem originalPolarValue_closed {dimension : ℕ} (field : ClosedJet dimension)
    (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    originalPolarValue field (radius, angle) =
      field.value (polarClosedPoint radius angle nonnegative bounded) :=
  smoothClosedExtension_value field (polarClosedPoint radius angle nonnegative bounded)

def polarDerivativeConstant (order : ℕ) : ℝ :=
  order.factorial * polarGeometryBound order ^ order

theorem polarDerivativeConstant_nonnegative (order : ℕ) : 0 ≤ polarDerivativeConstant order := by
  have geometry := zero_le_one.trans (polarGeometryBound_one_le order)
  unfold polarDerivativeConstant
  positivity

theorem originalPolar_derivative_bound {dimension : ℕ} (field : ClosedJet dimension)
    (order : ℕ) (point : ℝ × ℝ) (inside : point ∈ polarRectangle) :
    ‖iteratedFDeriv ℝ order (originalPolarValue field) point‖ ≤
      polarDerivativeConstant order * spatialJetEnvelope (smoothClosedExtension field) order (polarPlane point) := by
  have estimate := polarComposite_derivative_bound (smoothClosedExtension field)
    (smoothClosedExtension_smooth field) order order le_rfl point inside
  exact estimate.trans_eq (by unfold polarDerivativeConstant; ring)

theorem originalPolar_derivative_sq_bound {dimension : ℕ} (field : ClosedJet dimension)
    (order : ℕ) (point : ℝ × ℝ) (inside : point ∈ polarRectangle) :
    ‖iteratedFDeriv ℝ order (originalPolarValue field) point‖ ^ 2 ≤
      (polarDerivativeConstant order ^ 2 * (order + 1 : ℝ)) *
        spatialJetSquaredDensity (smoothClosedExtension field) order (polarPlane point) := by
  calc
    _ ≤ (polarDerivativeConstant order *
        spatialJetEnvelope (smoothClosedExtension field) order (polarPlane point)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (originalPolar_derivative_bound field order point inside) 2
    _ = polarDerivativeConstant order ^ 2 *
        spatialJetEnvelope (smoothClosedExtension field) order (polarPlane point) ^ 2 := mul_pow _ _ _
    _ ≤ polarDerivativeConstant order ^ 2 * ((order + 1 : ℝ) *
        spatialJetSquaredDensity (smoothClosedExtension field) order (polarPlane point)) :=
      mul_le_mul_of_nonneg_left (spatialJetEnvelope_sq_le _ _ _) (sq_nonneg _)
    _ = _ := by ring

def polarOrderConstant (order : ℕ) : ℝ :=
  polarDerivativeConstant order ^ 2 * (order + 1 : ℝ) * planarTensorConstant order

theorem polarOrderConstant_nonnegative (order : ℕ) : 0 ≤ polarOrderConstant order := by
  have tensorNonnegative : 0 ≤ planarTensorConstant order := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  unfold polarOrderConstant
  positivity

/-- No M4 loss is taken: exact original Cartesian L2 derivative density
pays all polar derivatives and the remaining cell frequency powers. -/
theorem weighted_polar_derivative_sq_le_density {dimension grade order : ℕ}
    (frequency : ℝ) (oneLe : 1 ≤ frequency) (upper : order ≤ grade)
    (field : ClosedJet dimension) (point : ℝ × ℝ) (inside : point ∈ polarRectangle) :
    frequency ^ (2 * (grade - order)) *
      ‖iteratedFDeriv ℝ order (originalPolarValue field) point‖ ^ 2 ≤
      polarOrderConstant order * cartesianPointDensity frequency grade field
        (polarClosedPoint point.1 point.2 inside.1.1 inside.1.2) := by
  have polarBound := originalPolar_derivative_sq_bound field order point inside
  have sourceBound := weighted_spatialJetSquaredDensity_le frequency oneLe upper field
    (polarClosedPoint point.1 point.2 inside.1.1 inside.1.2)
  calc
    _ ≤ frequency ^ (2 * (grade - order)) *
        ((polarDerivativeConstant order ^ 2 * (order + 1 : ℝ)) *
          spatialJetSquaredDensity (smoothClosedExtension field) order (polarPlane point)) :=
      mul_le_mul_of_nonneg_left polarBound (pow_nonneg (zero_le_one.trans oneLe) _)
    _ = (polarDerivativeConstant order ^ 2 * (order + 1 : ℝ)) *
        (frequency ^ (2 * (grade - order)) *
          spatialJetSquaredDensity (smoothClosedExtension field) order (polarPlane point)) := by ring
    _ ≤ (polarDerivativeConstant order ^ 2 * (order + 1 : ℝ)) *
        (planarTensorConstant order * cartesianPointDensity frequency grade field
          (polarClosedPoint point.1 point.2 inside.1.1 inside.1.2)) :=
      mul_le_mul_of_nonneg_left sourceBound (by positivity)
    _ = _ := by unfold polarOrderConstant; ring

theorem weighted_polar_mixed_sq_le_density {dimension grade radial angular power : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (paid : angular + radial + power ≤ grade)
    (point : ℝ × ℝ) (inside : point ∈ polarRectangle) :
    cellFrequency cell ^ (2 * power) *
      ‖angularJet angular (radialIter radial (originalPolarValue (phaseWeightedJet parameters cell field))) point‖ ^ 2 ≤
      polarOrderConstant (angular + radial) *
        cartesianDensityGlobal (cellFrequency cell) grade (phaseWeightedJet parameters cell field) (polarPlane point) := by
  have normBound := radialAngular_norm_le radial angular
    (originalPolarValue (phaseWeightedJet parameters cell field)) (originalPolarValue_smooth _) point
  have frequencyBound : cellFrequency cell ^ (2 * power) ≤
      cellFrequency cell ^ (2 * (grade - (angular + radial))) :=
    pow_le_pow_right₀ (cellFrequency_one_le cell) (by omega)
  apply (mul_le_mul frequencyBound (pow_le_pow_left₀ (norm_nonneg _) normBound 2)
    (sq_nonneg _) (pow_nonneg (cellFrequency_pos cell).le _)).trans
  have estimate := weighted_polar_derivative_sq_le_density (cellFrequency cell) (cellFrequency_one_le cell)
    (by omega : angular + radial ≤ grade) (phaseWeightedJet parameters cell field) point inside
  apply estimate.trans_eq
  exact congrArg (fun value => polarOrderConstant (angular + radial) * value)
    (cartesianDensityGlobal_closed (cellFrequency cell) grade
      (phaseWeightedJet parameters cell field)
      (polarClosedPoint point.1 point.2 inside.1.1 inside.1.2)).symm

end Grad.SourceCollarRestriction

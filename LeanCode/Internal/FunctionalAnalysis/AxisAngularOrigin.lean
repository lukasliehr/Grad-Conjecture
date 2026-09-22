import AxisOriginBasics

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Grad.AxisSplit

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds
open Grad.RepresentedKernel.SpatialProduct Grad.GaugeCoefficients.Radial
open Grad.PDEBootstrap

theorem planeRotation_zero_point (angle : ℝ) :
    planeRotation angle (0 : SpatialPlane) = 0 := by
  have rotationZero := (planeRotationEquiv angle).map_zero
  rwa [planeRotationEquiv_apply] at rotationZero

theorem rotatedPoint_origin (angle : ℝ) :
    rotatedPoint angle originPoint = originPoint := by
  apply Subtype.ext
  change planeRotation angle originPoint.val = originPoint.val
  rw [originPoint_val, planeRotation_zero_point]

theorem orthogonalClosedPoint_rotation_origin (angle : ℝ) :
    orthogonalClosedPoint (planeRotationEquiv angle) originPoint = originPoint := by
  apply Subtype.ext
  change planeRotationEquiv angle originPoint.val = originPoint.val
  rw [originPoint_val]
  exact (planeRotationEquiv angle).map_zero

/-- N1's angular mode-zero projection keeps the exact axis value. -/
theorem angularJet_zero_originValue {dimension : ℕ} (field : ClosedJet dimension) :
    originValue (angularClosedJet 0 field) = originValue field := by
  unfold originValue
  rw [angularClosedJet_value]
  have integrandConstant : (fun angle : ℝ => angularCharacter 0 angle •
      field.value (rotatedPoint angle originPoint)) =
      fun _ : ℝ => field.value originPoint := by
    funext angle
    rw [angularCharacter_zero_mode, one_smul, rotatedPoint_origin]
  rw [integrandConstant, intervalIntegral.integral_const, sub_zero, smul_smul,
    inv_mul_cancel₀ Real.two_pi_pos.ne', one_smul]

/-- The single planar rotation entry appearing in the first-order chain factor. -/
theorem chainFactor_one_rotation (angle : ℝ) (direction : Fin 2)
    (target : CartesianWord 1) :
    chainFactor 1 (planeRotationEquiv angle) (fun _ => direction) target =
      planeRotation angle (spatialDirection direction) (target 0) := by
  unfold chainFactor Grad.TensorCoefficients.tensorCoefficient
  rw [Fin.prod_univ_one]
  unfold Grad.OrthogonalCoefficients.coefficient
  rw [planeRotationEquiv_apply]

theorem spatialDirection_component (direction component : Fin 2) :
    spatialDirection direction component = if component = direction then (1 : ℝ) else 0 := by
  change Pi.single (M := fun _ : Fin 2 => ℝ) direction 1 component = _
  by_cases equal : component = direction
  · rw [if_pos equal, equal]
    exact Pi.single_eq_same direction 1
  · rw [if_neg equal]
    exact Pi.single_eq_of_ne equal 1

theorem planeRotation_component_zero (angle : ℝ) (direction : Fin 2) :
    planeRotation angle (spatialDirection direction) 0 =
      (if (0 : Fin 2) = direction then Real.cos angle else 0) -
        (if (1 : Fin 2) = direction then Real.sin angle else 0) := by
  change Real.cos angle * spatialDirection direction 0 -
      Real.sin angle * spatialDirection direction 1 = _
  rw [spatialDirection_component, spatialDirection_component]
  fin_cases direction <;> simp

theorem planeRotation_component_one (angle : ℝ) (direction : Fin 2) :
    planeRotation angle (spatialDirection direction) 1 =
      (if (0 : Fin 2) = direction then Real.sin angle else 0) +
        (if (1 : Fin 2) = direction then Real.cos angle else 0) := by
  change Real.sin angle * spatialDirection direction 0 +
      Real.cos angle * spatialDirection direction 1 = _
  rw [spatialDirection_component, spatialDirection_component]
  fin_cases direction <;> simp

theorem integral_cos_two_pi : ∫ angle in (0 : ℝ)..2 * Real.pi, Real.cos angle = 0 := by
  rw [integral_cos, Real.sin_two_pi, Real.sin_zero, sub_zero]

theorem integral_sin_two_pi : ∫ angle in (0 : ℝ)..2 * Real.pi, Real.sin angle = 0 := by
  rw [integral_sin, Real.cos_two_pi, Real.cos_zero, sub_self]

theorem continuous_if_trig (P : Prop) [Decidable P] (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous (fun angle : ℝ => if P then f angle else 0) := by
  by_cases h : P
  · simpa [h] using hf
  · simp only [if_neg h]; exact continuous_const

theorem integral_if_trig (P : Prop) [Decidable P] (f : ℝ → ℝ)
    (hf : (∫ angle in (0 : ℝ)..2 * Real.pi, f angle) = 0) :
    (∫ angle in (0 : ℝ)..2 * Real.pi, (if P then f angle else 0)) = 0 := by
  by_cases h : P
  · simpa [h] using hf
  · simp only [if_neg h]
    exact intervalIntegral.integral_zero

/-- Every entry of the planar rotation matrix has zero full-circle mean. -/
theorem integral_rotation_entry (direction component : Fin 2) :
    (∫ angle in (0 : ℝ)..2 * Real.pi,
      planeRotation angle (spatialDirection direction) component) = 0 := by
  fin_cases component
  · have rewriteEntry : (fun angle : ℝ =>
        planeRotation angle (spatialDirection direction) 0) = fun angle =>
          (if (0 : Fin 2) = direction then Real.cos angle else 0) -
            (if (1 : Fin 2) = direction then Real.sin angle else 0) := by
      funext angle
      exact planeRotation_component_zero angle direction
    rw [show (fun angle : ℝ => planeRotation angle (spatialDirection direction)
        (⟨0, by omega⟩ : Fin 2)) = fun angle : ℝ =>
          planeRotation angle (spatialDirection direction) 0 from rfl, rewriteEntry]
    rw [intervalIntegral.integral_sub
      ((continuous_if_trig _ _ Real.continuous_cos).intervalIntegrable _ _)
      ((continuous_if_trig _ _ Real.continuous_sin).intervalIntegrable _ _)]
    rw [integral_if_trig _ _ integral_cos_two_pi,
      integral_if_trig _ _ integral_sin_two_pi, sub_zero]
  · have rewriteEntry : (fun angle : ℝ =>
        planeRotation angle (spatialDirection direction) 1) = fun angle =>
          (if (0 : Fin 2) = direction then Real.sin angle else 0) +
            (if (1 : Fin 2) = direction then Real.cos angle else 0) := by
      funext angle
      exact planeRotation_component_one angle direction
    rw [show (fun angle : ℝ => planeRotation angle (spatialDirection direction)
        (⟨1, by omega⟩ : Fin 2)) = fun angle : ℝ =>
          planeRotation angle (spatialDirection direction) 1 from rfl, rewriteEntry]
    rw [intervalIntegral.integral_add
      ((continuous_if_trig _ _ Real.continuous_sin).intervalIntegrable _ _)
      ((continuous_if_trig _ _ Real.continuous_cos).intervalIntegrable _ _)]
    rw [integral_if_trig _ _ integral_sin_two_pi,
      integral_if_trig _ _ integral_cos_two_pi, add_zero]

theorem continuous_rotation_entry (direction component : Fin 2) :
    Continuous (fun angle : ℝ =>
      planeRotation angle (spatialDirection direction) component) := by
  fin_cases component
  · have rewriteEntry : (fun angle : ℝ =>
        planeRotation angle (spatialDirection direction) 0) = fun angle =>
          (if (0 : Fin 2) = direction then Real.cos angle else 0) -
            (if (1 : Fin 2) = direction then Real.sin angle else 0) := by
      funext angle
      exact planeRotation_component_zero angle direction
    rw [show (fun angle : ℝ => planeRotation angle (spatialDirection direction)
        (⟨0, by omega⟩ : Fin 2)) = fun angle : ℝ =>
          planeRotation angle (spatialDirection direction) 0 from rfl, rewriteEntry]
    exact (continuous_if_trig _ _ Real.continuous_cos).sub
      (continuous_if_trig _ _ Real.continuous_sin)
  · have rewriteEntry : (fun angle : ℝ =>
        planeRotation angle (spatialDirection direction) 1) = fun angle =>
          (if (0 : Fin 2) = direction then Real.sin angle else 0) +
            (if (1 : Fin 2) = direction then Real.cos angle else 0) := by
      funext angle
      exact planeRotation_component_one angle direction
    rw [show (fun angle : ℝ => planeRotation angle (spatialDirection direction)
        (⟨1, by omega⟩ : Fin 2)) = fun angle : ℝ =>
          planeRotation angle (spatialDirection direction) 1 from rfl, rewriteEntry]
    exact (continuous_if_trig _ _ Real.continuous_sin).add
      (continuous_if_trig _ _ Real.continuous_cos)

theorem integrable_rotation_entry_smul {dimension : ℕ} (direction component : Fin 2)
    (vector : ComplexEuclidean dimension) :
    IntegrableOn (fun angle : ℝ =>
      planeRotation angle (spatialDirection direction) component • vector)
      (Set.Icc 0 (2 * Real.pi)) := by
  apply Continuous.integrableOn_Icc
  exact (continuous_rotation_entry direction component).smul continuous_const

/-- AL5: the angular mode-zero projection has zero first Cartesian
derivatives at the axis, for every input jet. -/
theorem angularJet_zero_originPartial {dimension : ℕ} (direction : Fin 2)
    (field : ClosedJet dimension) :
    originPartial direction (angularClosedJet 0 field) = 0 := by
  rw [originPartial_eq_closedDerivative]
  rw [angularClosedJet_derivative]
  have integrandExpand : (fun angle : ℝ => angularCharacter 0 angle •
      orthogonalDerivative (planeRotationEquiv angle) field 1 (fun _ => direction)
        originPoint) = fun angle : ℝ =>
        ∑ target : CartesianWord 1,
          planeRotation angle (spatialDirection direction) (target 0) •
            closedDerivative field 1 target originPoint := by
    funext angle
    rw [angularCharacter_zero_mode, one_smul]
    change (∑ target : CartesianWord 1,
      chainFactor 1 (planeRotationEquiv angle) (fun _ => direction) target •
        closedDerivative field 1 target
          (orthogonalClosedPoint (planeRotationEquiv angle) originPoint)) = _
    apply Finset.sum_congr rfl
    intro target _
    rw [chainFactor_one_rotation, orthogonalClosedPoint_rotation_origin]
  rw [show (∫ angle in Set.Icc (0 : ℝ) (2 * Real.pi), angularCharacter 0 angle •
      orthogonalDerivative (planeRotationEquiv angle) field 1 (fun _ => direction)
        originPoint) = ∫ angle in Set.Icc (0 : ℝ) (2 * Real.pi),
        ∑ target : CartesianWord 1,
          planeRotation angle (spatialDirection direction) (target 0) •
            closedDerivative field 1 target originPoint from
    congrArg _ (by rw [integrandExpand])]
  rw [MeasureTheory.integral_finsetSum _ (fun target _ =>
    integrable_rotation_entry_smul direction (target 0)
      (closedDerivative field 1 target originPoint))]
  have eachZero : ∀ target : CartesianWord 1,
      (∫ angle in Set.Icc (0 : ℝ) (2 * Real.pi),
        planeRotation angle (spatialDirection direction) (target 0) •
          closedDerivative field 1 target originPoint) = 0 := by
    intro target
    rw [integral_smul_const]
    rw [show (∫ angle in Set.Icc (0 : ℝ) (2 * Real.pi),
        planeRotation angle (spatialDirection direction) (target 0)) =
      ∫ angle in (0 : ℝ)..2 * Real.pi,
        planeRotation angle (spatialDirection direction) (target 0) by
      rw [intervalIntegral.integral_of_le (by positivity), integral_Icc_eq_integral_Ioc]]
    rw [integral_rotation_entry, zero_smul]
  rw [Finset.sum_congr rfl (fun target _ => eachZero target), Finset.sum_const_zero,
    smul_zero]

end Grad.AxisSplit

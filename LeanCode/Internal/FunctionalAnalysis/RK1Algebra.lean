import RK1Realization

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open scoped BigOperators ContDiff Topology

namespace Grad.RepresentedKernel

def radialEnvelope (width : ℝ → ℝ) (output input : ℤ) (point : Spatial) : ℝ :=
  Real.exp (width ‖point‖ * |((output - input : ℤ) : ℝ)|)

theorem radialEnvelope_pos (width : ℝ → ℝ) (output input : ℤ) (point : Spatial) :
    0 < radialEnvelope width output input point := Real.exp_pos _

theorem radialEnvelope_one_le (width : ℝ → ℝ) (output input : ℤ) (point : Spatial)
    (nonnegative : 0 ≤ width ‖point‖) : 1 ≤ radialEnvelope width output input point :=
  Real.one_le_exp (mul_nonneg nonnegative (abs_nonneg _))

theorem radialEnvelope_orthogonal (width : ℝ → ℝ) (output input : ℤ)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (point : Spatial) :
    radialEnvelope width output input (orthogonal point) =
      radialEnvelope width output input point := by
  simp only [radialEnvelope, orthogonal.norm_map]

theorem radialEnvelope_composition (width : ℝ → ℝ) (output middle input : ℤ)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (point : Spatial)
    (nonnegative : 0 ≤ width ‖point‖) :
    radialEnvelope width output input point ≤
      radialEnvelope width output middle point * radialEnvelope width middle input (orthogonal point) := by
  rw [radialEnvelope_orthogonal]
  unfold radialEnvelope
  rw [← Real.exp_add, ← mul_add]
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ nonnegative
  simpa only [Int.cast_sub] using abs_sub_le (output : ℝ) (middle : ℝ) (input : ℝ)

theorem derivativeFactor_displacement (moment : ℕ) (output middle input : ℤ) :
    Grad.CellWeights.derivativeFactor moment (output - input) =
      ∑ allocation ∈ Finset.range (moment + 1),
        (moment.choose allocation : ℂ) *
          Grad.CellWeights.derivativeFactor allocation (output - middle) *
          Grad.CellWeights.derivativeFactor (moment - allocation) (middle - input) := by
  have split : Complex.I * ((output - input : ℤ) : ℂ) =
      Complex.I * ((output - middle : ℤ) : ℂ) +
        Complex.I * ((middle - input : ℤ) : ℂ) := by
    push_cast
    ring
  simp only [Grad.CellWeights.derivativeFactor]
  rw [split, add_pow]
  apply Finset.sum_congr rfl
  intro allocation _
  ring

def composedCoefficient {Outer Inner : Type*} {inputDimension middleDimension outputDimension : ℕ}
    (orthogonal : Outer → Spatial ≃ₗᵢ[ℝ] Spatial)
    (outer : ℤ → ℤ → Outer × Spatial →
      PhysicalValue middleDimension →L[ℂ] PhysicalValue outputDimension)
    (inner : ℤ → ℤ → Inner × Spatial →
      PhysicalValue inputDimension →L[ℂ] PhysicalValue middleDimension)
    (output input : ℤ) (parameter : ℤ × Outer × Inner) (point : Spatial) :
    PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension :=
  (outer output parameter.1 (parameter.2.1, point)).comp
    (inner parameter.1 input (parameter.2.2, orthogonal parameter.2.1 point))

def composedOrthogonal {Outer Inner : Type*}
    (outer : Outer → Spatial ≃ₗᵢ[ℝ] Spatial) (inner : Inner → Spatial ≃ₗᵢ[ℝ] Spatial)
    (parameter : ℤ × Outer × Inner) : Spatial ≃ₗᵢ[ℝ] Spatial :=
  (outer parameter.2.1).trans (inner parameter.2.2)

theorem composedOrthogonal_apply {Outer Inner : Type*}
    (outer : Outer → Spatial ≃ₗᵢ[ℝ] Spatial) (inner : Inner → Spatial ≃ₗᵢ[ℝ] Spatial)
    (parameter : ℤ × Outer × Inner) (point : Spatial) :
    composedOrthogonal outer inner parameter point =
      inner parameter.2.2 (outer parameter.2.1 point) := rfl

theorem coefficient_moment_allocation {inputDimension middleDimension outputDimension : ℕ}
    (outer : PhysicalValue middleDimension →L[ℂ] PhysicalValue outputDimension)
    (inner : PhysicalValue inputDimension →L[ℂ] PhysicalValue middleDimension)
    (moment : ℕ) (output middle input : ℤ) :
    Grad.CellWeights.derivativeFactor moment (output - input) • outer.comp inner =
      ∑ allocation ∈ Finset.range (moment + 1), (moment.choose allocation : ℂ) •
        ((Grad.CellWeights.derivativeFactor allocation (output - middle) • outer).comp
          (Grad.CellWeights.derivativeFactor (moment - allocation) (middle - input) • inner)) := by
  apply ContinuousLinearMap.ext
  intro value
  simp only [smul_apply, ContinuousLinearMap.comp_apply, sum_apply, map_smul, smul_smul]
  rw [derivativeFactor_displacement moment output middle input, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro allocation _
  congr 1
  ring

theorem composition_envelope_bound {inputDimension middleDimension outputDimension : ℕ}
    (outer : PhysicalValue middleDimension →L[ℂ] PhysicalValue outputDimension)
    (inner : PhysicalValue inputDimension →L[ℂ] PhysicalValue middleDimension)
    (width : ℝ → ℝ) (output middle input : ℤ)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (point : Spatial)
    (nonnegative : 0 ≤ width ‖point‖) (outerBound innerBound : ℝ)
    (outerEstimate : ‖outer‖ * radialEnvelope width output middle point ≤ outerBound)
    (innerEstimate : ‖inner‖ * radialEnvelope width middle input (orthogonal point) ≤ innerBound) :
    ‖outer.comp inner‖ * radialEnvelope width output input point ≤ outerBound * innerBound := by
  calc
    _ ≤ (‖outer‖ * ‖inner‖) *
        (radialEnvelope width output middle point *
          radialEnvelope width middle input (orthogonal point)) :=
      mul_le_mul (ContinuousLinearMap.opNorm_comp_le outer inner)
        (radialEnvelope_composition width output middle input orthogonal point nonnegative)
        (radialEnvelope_pos width output input point).le
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (‖outer‖ * radialEnvelope width output middle point) *
        (‖inner‖ * radialEnvelope width middle input (orthogonal point)) := by ring
    _ ≤ outerBound * innerBound :=
      mul_le_mul outerEstimate innerEstimate
        (mul_nonneg (norm_nonneg _) (radialEnvelope_pos width middle input (orthogonal point)).le)
        ((mul_nonneg (norm_nonneg _) (radialEnvelope_pos width output middle point).le).trans
          outerEstimate)

end Grad.RepresentedKernel

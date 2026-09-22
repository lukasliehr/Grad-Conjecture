import SCS27FourierProductCoefficient

noncomputable section
open Set
open scoped BigOperators

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarAngular
open Grad.SourceCollarDivision

/-- Genuine two-frequency product convolution. The kernel is not restricted
to finite support; the source is identified through its actual axial cells. -/
theorem doubleCoefficient_series_product {dimension : ℕ}
    (coefficients : ℤ × ℤ → ℂ) (norms : Summable (fun mode => ‖coefficients mode‖))
    (kernel : ℝ × ℝ → ℂ) (source : ℝ × ℝ → ComplexEuclidean dimension)
    (sourceCells : ℤ → ℝ → ComplexEuclidean dimension)
    (continuousSource : ∀ polar, Continuous (fun axial => source (polar, axial)))
    (continuousCells : ∀ cell, Continuous (sourceCells cell))
    (sourceCoefficient : ∀ polar cell,
      angularCoefficient (fun axial => source (polar, axial)) cell = sourceCells cell polar)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (dominated : ∀ polar ∈ Icc (-Real.pi) Real.pi, ∀ axial ∈ Icc (-Real.pi) Real.pi,
      ‖source (polar, axial)‖ ≤ bound)
    (kernelSeries : ∀ polar ∈ Icc (-Real.pi) Real.pi, ∀ axial ∈ Icc (-Real.pi) Real.pi,
      HasSum (fun shift : ℤ × ℤ => cellExponential shift.2 axial *
        (cellExponential shift.1 polar * coefficients shift)) (kernel (polar, axial)))
    (mode : ℤ × ℤ) :
    HasSum (fun shift : ℤ × ℤ => coefficients shift •
      angularCoefficient (sourceCells (mode.2 - shift.2)) (mode.1 - shift.1))
      (angularCoefficient (fun polar => angularCoefficient
        (fun axial => kernel (polar, axial) • source (polar, axial)) mode.2) mode.1) := by
  let fields : (ℤ × ℤ) → ℝ → ComplexEuclidean dimension := fun shift polar =>
    (cellExponential shift.1 polar * coefficients shift) • sourceCells (mode.2 - shift.2) polar
  have innerSeries (polar : ℝ) (inside : polar ∈ Icc (-Real.pi) Real.pi) :
      HasSum (fun shift => fields shift polar)
        (angularCoefficient (fun axial => kernel (polar, axial) • source (polar, axial)) mode.2) := by
    have phasedNorms : Summable (fun shift : ℤ × ℤ => ‖cellExponential shift.1 polar * coefficients shift‖) := by
      simpa only [norm_mul, cellExponential_norm, one_mul] using norms
    have result := angularCoefficient_series_product
      (fun shift : ℤ × ℤ => cellExponential shift.1 polar * coefficients shift) Prod.snd phasedNorms
      (fun axial => kernel (polar, axial)) (fun axial => source (polar, axial)) (continuousSource polar)
      bound (dominated polar inside) (kernelSeries polar inside) mode.2
    apply result.congr_fun
    intro shift
    rw [sourceCoefficient]
  have cellBound (cell : ℤ) (polar : ℝ) (inside : polar ∈ Icc (-Real.pi) Real.pi) :
      ‖sourceCells cell polar‖ ≤ bound := by
    rw [← sourceCoefficient]
    exact angularCoefficient_norm_le _ (continuousSource polar) bound boundNonnegative (dominated polar inside) cell
  have result := angularCoefficient_hasSum fields
    (fun polar => angularCoefficient (fun axial => kernel (polar, axial) • source (polar, axial)) mode.2)
    (fun shift => ((cellExponential_smooth shift.1).continuous.mul continuous_const).smul
      (continuousCells (mode.2 - shift.2)))
    (fun shift => ‖coefficients shift‖ * bound) (norms.mul_right bound)
    (fun shift polar inside => by
      simpa only [fields, norm_smul, norm_mul, cellExponential_norm, one_mul] using
        mul_le_mul_of_nonneg_left (cellBound (mode.2 - shift.2) polar inside) (norm_nonneg (coefficients shift)))
    innerSeries mode.1
  apply result.congr_fun
  intro shift
  have expression : fields shift = coefficients shift •
      (fun polar => cellExponential shift.1 polar • sourceCells (mode.2 - shift.2) polar) := by
    funext polar
    simp only [fields, Pi.smul_apply, smul_smul]
    rw [mul_comm]
  rw [expression, angularCoefficient_smul_continuous, angularCoefficient_character_mul]

end Grad.SourceCollarFullSource

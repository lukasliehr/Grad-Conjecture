import SCC27RadialProductBound

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarAngular Grad.PhaseAlgebra

def CellRowsCompatible {dimension : ℕ} (power : ℕ) (high low : CellL2 dimension) : Prop :=
  ∀ mode : ℤ × ℤ, high mode = ((annularFrequency mode.1 mode.2 : ℂ) ^ power) • low mode

theorem balancedSingleProduct_literal {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
    (shift : ℤ × ℤ) (coefficient : ℂ) (high low : CellL2 dimension)
    (compatible : CellRowsCompatible power high low) (mode : ℤ × ℤ) :
    balancedSingleProduct parameters power radius nonnegative bounded shift coefficient high low mode =
      ((Real.exp (radialPhase parameters radius mode.2 - radialPhase parameters radius (mode - shift).2) : ℂ) *
        (annularFrequency mode.1 mode.2 : ℂ) ^ power * coefficient) • low (mode - shift) := by
  rw [balancedSingleProduct_value, compatible (mode - shift), ← add_smul, smul_smul]
  congr 1
  have denominatorReal : 0 < annularFrequency (mode - shift).1 (mode - shift).2 ^ power +
      annularFrequency shift.1 shift.2 ^ power :=
    add_pos (pow_pos (annularFrequency_pos _ _) _) (pow_pos (annularFrequency_pos _ _) _)
  have denominator : (annularFrequency (mode - shift).1 (mode - shift).2 : ℂ) ^ power +
      (annularFrequency shift.1 shift.2 : ℂ) ^ power ≠ 0 := by exact_mod_cast denominatorReal.ne'
  unfold balancedProductRatio
  push_cast
  field_simp [denominator]

/-- On compatible weighted rows the constructed operator is the actual
weighted full-cell convolution, not merely an operator with the same bound. -/
theorem pointwiseProduct_literal {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
    (coefficient : ℤ × ℤ → ℂ)
    (lowMoment : Summable (productMoment parameters 0 radius coefficient))
    (highMoment : Summable (productMoment parameters power radius coefficient)) (high low : CellL2 dimension)
    (compatible : CellRowsCompatible power high low) (mode : ℤ × ℤ) :
    HasSum (fun shift : ℤ × ℤ =>
      ((Real.exp (radialPhase parameters radius mode.2 - radialPhase parameters radius (mode - shift).2) : ℂ) *
        (annularFrequency mode.1 mode.2 : ℂ) ^ power * coefficient shift) • low (mode - shift))
      (pointwiseProduct parameters power radius nonnegative bounded coefficient high low mode) := by
  have series := (pointwiseProduct_summable_norm parameters power radius nonnegative bounded coefficient
    lowMoment highMoment high low).of_norm.hasSum
  have evaluated := (lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode).hasSum series
  exact evaluated.congr_fun (fun shift =>
    (balancedSingleProduct_literal parameters power radius nonnegative bounded shift (coefficient shift)
      high low compatible mode).symm)

end Grad.SourceCollarCoefficients

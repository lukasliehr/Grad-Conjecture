import SCC30OriginalRowCoordinates

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.PhaseAlgebra

theorem originalRow_product_decode {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ) (lower radius : ℝ)
    (positive : 0 < radius) (input output : DivisionRow dimension lower) (coefficient : ℤ × ℤ → ℂ) (mode : ℤ × ℤ)
    (weighted : HasSum (fun shift : ℤ × ℤ =>
      ((Real.exp (radialPhase parameters radius mode.2 - radialPhase parameters radius (mode - shift).2) : ℂ) *
        (annularFrequency mode.1 mode.2 : ℂ) ^ power * coefficient shift) • input (mode - shift) radius)
      (output mode radius)) :
    HasSum (fun shift : ℤ × ℤ => coefficient shift • originalRowCoefficient parameters 0 lower input radius (mode - shift))
      (originalRowCoefficient parameters power lower output radius mode) := by
  have scaled := ((originalRowWeight parameters power radius mode : ℂ)⁻¹ •
    ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)).hasSum weighted
  refine scaled.congr_fun (fun shift => ?_)
  simp only [smul_apply, ContinuousLinearMap.id_apply,
    originalRowCoefficient, smul_smul]
  rw [originalRow_product_scalar parameters power radius positive mode shift (coefficient shift)]

theorem originalRow_compatible {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ) (lower : ℝ)
    (positive : 0 < lower) (high low : DivisionRow dimension lower)
    (compatible : RadialRowsCompatible lower power high low) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      originalRowCoefficient parameters power lower high radius mode =
        originalRowCoefficient parameters 0 lower low radius mode := by
  have representatives : ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      ∀ mode : ℤ × ℤ, high mode radius = ((annularFrequency mode.1 mode.2 : ℂ) ^ power) • low mode radius := by
    apply ae_all_iff.mpr
    intro mode
    rw [compatible mode]
    exact Lp.coeFn_smul _ _
  filter_upwards [representatives, ae_restrict_mem measurableSet_Icc] with radius literal inside
  intro mode
  have scalar := originalRow_product_scalar parameters power radius (positive.trans_le inside.1) mode 0 1
  simp only [sub_zero, sub_self, Real.exp_zero, Complex.ofReal_one, one_mul, mul_one] at scalar
  simp only [originalRowCoefficient, literal mode, smul_smul, scalar]

/-- Exact BS42: full-cell multiplication on the literal completed radial
norm, uniformly in the annulus, with the radiuswise envelope sums and
one-high allocation. Coefficients need only be measurable with these moments. -/
theorem exactRadialProduct {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (lower : ℝ) (positive : 0 < lower)
    (coefficient : ℝ → ℤ × ℤ → ℂ)
    (coefficientMeasurable : ∀ shift, AEStronglyMeasurable (fun radius => coefficient radius shift) (volume.restrict (Icc lower 1)))
    (lowBound highBound : ℝ) (lowNonnegative : 0 ≤ lowBound) (highNonnegative : 0 ≤ highBound)
    (moments : ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      Summable (productMoment parameters 0 radius (coefficient radius)) ∧
      Summable (productMoment parameters power radius (coefficient radius)) ∧
      (∑' shift, productMoment parameters 0 radius (coefficient radius) shift) ≤ lowBound ∧
      (∑' shift, productMoment parameters power radius (coefficient radius) shift) ≤ highBound)
    (high low : DivisionRow dimension lower) (compatible : RadialRowsCompatible lower power high low) :
    ∃ product : DivisionRow dimension lower,
      ‖product‖ ≤ productPhaseConstant parameters power * (lowBound * ‖high‖ + highBound * ‖low‖) ∧
      (∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
        HasSum (fun shift : ℤ × ℤ => coefficient radius shift •
          originalRowCoefficient parameters 0 lower low radius (mode - shift))
          (originalRowCoefficient parameters power lower product radius mode)) := by
  refine ⟨completedRadialProduct parameters power lower positive.le coefficient coefficientMeasurable
    lowBound highBound lowNonnegative highNonnegative moments high low,
    completedRadialProduct_norm parameters power lower positive.le coefficient coefficientMeasurable
      lowBound highBound lowNonnegative highNonnegative moments high low, ?_⟩
  filter_upwards [completedRadialProduct_literal parameters power lower positive.le coefficient coefficientMeasurable
    lowBound highBound lowNonnegative highNonnegative moments high low compatible,
    ae_restrict_mem measurableSet_Icc] with radius literal inside
  intro mode
  exact originalRow_product_decode parameters power lower radius (positive.trans_le inside.1) low _
    (coefficient radius) mode (literal mode)

end Grad.SourceCollarCoefficients

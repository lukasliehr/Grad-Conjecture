import SCC28LiteralCellProduct

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.PhaseAlgebra

def RadialRowsCompatible {dimension : ℕ} (lower : ℝ) (power : ℕ)
    (high low : DivisionRow dimension lower) : Prop :=
  ∀ mode : ℤ × ℤ, high mode = ((annularFrequency mode.1 mode.2 : ℂ) ^ power) • low mode

theorem collectRadial_compatible {dimension : ℕ} (lower : ℝ) (power : ℕ)
    (high low : DivisionRow dimension lower) (compatible : RadialRowsCompatible lower power high low) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      CellRowsCompatible power (collectRadial lower high radius) (collectRadial lower low radius) := by
  have representative : ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      ∀ mode : ℤ × ℤ, high mode radius = ((annularFrequency mode.1 mode.2 : ℂ) ^ power) • low mode radius := by
    apply ae_all_iff.mpr
    intro mode
    rw [compatible mode]
    exact Lp.coeFn_smul _ _
  filter_upwards [representative, collectRadial_ae lower high, collectRadial_ae lower low]
    with radius literal highLiteral lowLiteral
  intro mode
  rw [highLiteral mode, lowLiteral mode, literal mode]

variable {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
  (lower : ℝ) (lowerNonnegative : 0 ≤ lower)
  (coefficient : ℝ → ℤ × ℤ → ℂ)
  (coefficientMeasurable : ∀ shift, AEStronglyMeasurable (fun radius => coefficient radius shift) (volume.restrict (Icc lower 1)))
  (lowBound highBound : ℝ) (lowNonnegative : 0 ≤ lowBound) (highNonnegative : 0 ≤ highBound)
  (moments : ∀ᵐ radius ∂volume.restrict (Icc lower 1),
    Summable (productMoment parameters 0 radius (coefficient radius)) ∧
    Summable (productMoment parameters power radius (coefficient radius)) ∧
    (∑' shift, productMoment parameters 0 radius (coefficient radius) shift) ≤ lowBound ∧
    (∑' shift, productMoment parameters power radius (coefficient radius) shift) ≤ highBound)

def completedRadialProduct (high low : DivisionRow dimension lower) : DivisionRow dimension lower :=
  separateRadial lower (radialProductLp parameters power lower lowerNonnegative coefficient coefficientMeasurable
    lowBound highBound lowNonnegative highNonnegative moments (collectRadial lower high) (collectRadial lower low))

/-- BS42 on the entire original completed full-cell radial carrier. The
constants bound the radiuswise sums, not sums of individual suprema. -/
theorem completedRadialProduct_norm (high low : DivisionRow dimension lower) :
    ‖completedRadialProduct parameters power lower lowerNonnegative coefficient coefficientMeasurable
      lowBound highBound lowNonnegative highNonnegative moments high low‖ ≤
        productPhaseConstant parameters power * (lowBound * ‖high‖ + highBound * ‖low‖) := by
  rw [completedRadialProduct, separateRadial_norm]
  simpa only [collectRadial_norm] using
    radialProductLp_norm parameters power lower lowerNonnegative coefficient coefficientMeasurable
      lowBound highBound lowNonnegative highNonnegative moments (collectRadial lower high) (collectRadial lower low)

theorem completedRadialProduct_literal (high low : DivisionRow dimension lower)
    (compatible : RadialRowsCompatible lower power high low) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      HasSum (fun shift : ℤ × ℤ =>
        ((Real.exp (radialPhase parameters radius mode.2 - radialPhase parameters radius (mode - shift).2) : ℂ) *
          (annularFrequency mode.1 mode.2 : ℂ) ^ power * coefficient radius shift) • low (mode - shift) radius)
        (completedRadialProduct parameters power lower lowerNonnegative coefficient coefficientMeasurable
          lowBound highBound lowNonnegative highNonnegative moments high low mode radius) := by
  filter_upwards [ae_restrict_mem measurableSet_Icc, moments, collectRadial_compatible lower power high low compatible,
    collectRadial_ae lower low,
    radialProductLp_ae parameters power lower lowerNonnegative coefficient coefficientMeasurable
      lowBound highBound lowNonnegative highNonnegative moments (collectRadial lower high) (collectRadial lower low),
    separateRadial_ae lower (radialProductLp parameters power lower lowerNonnegative coefficient coefficientMeasurable
      lowBound highBound lowNonnegative highNonnegative moments (collectRadial lower high) (collectRadial lower low))]
    with radius inside moment coherent lowLiteral productLiteral separated
  intro mode
  have disk : radius ∈ Icc (0 : ℝ) 1 := ⟨lowerNonnegative.trans inside.1, inside.2⟩
  have output : completedRadialProduct parameters power lower lowerNonnegative coefficient coefficientMeasurable
      lowBound highBound lowNonnegative highNonnegative moments high low mode radius =
        pointwiseProduct parameters power radius disk.1 disk.2 (coefficient radius)
          (collectRadial lower high radius) (collectRadial lower low radius) mode := by
    change separateRadial lower _ mode radius = _
    rw [separated mode, productLiteral, radialProductValue_inside parameters power coefficient
      (collectRadial lower high) (collectRadial lower low) radius disk]
  rw [output]
  simpa only [lowLiteral] using pointwiseProduct_literal parameters power radius disk.1 disk.2
    (coefficient radius) moment.1 moment.2.1 (collectRadial lower high radius) (collectRadial lower low radius) coherent mode

end Grad.SourceCollarCoefficients

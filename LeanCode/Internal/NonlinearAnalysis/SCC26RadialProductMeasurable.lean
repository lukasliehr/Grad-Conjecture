import SCC25BalancedCellProduct

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision

theorem cellL2_measurable_of_coordinates {dimension : ℕ} (measure : Measure ℝ)
    (field : ℝ → CellL2 dimension)
    (coordinates : ∀ mode : ℤ × ℤ, AEStronglyMeasurable (fun radius => field radius mode) measure) :
    AEStronglyMeasurable field measure := by
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset (ℤ × ℤ)))
    (f := fun modes radius => ∑ mode ∈ modes, (lp.single 2 mode (field radius mode) : CellL2 dimension))
  · intro modes
    apply Finset.aestronglyMeasurable_fun_sum
    intro mode _
    exact (lp.singleContinuousLinearMap ℂ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode).continuous.comp_aestronglyMeasurable
      (coordinates mode)
  · filter_upwards with radius
    exact lp.hasSum_single (by norm_num) (field radius)

/-- Outside the original disk interval the representative is set to zero;
no original radius, weight, or input domain is changed. -/
def radialProductTerm {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (coefficient : ℝ → ℤ × ℤ → ℂ) (high low : ℝ → CellL2 dimension)
    (shift : ℤ × ℤ) (radius : ℝ) : CellL2 dimension :=
  if inside : radius ∈ Icc (0 : ℝ) 1 then
    balancedSingleProduct parameters power radius inside.1 inside.2 shift (coefficient radius shift)
      (high radius) (low radius)
  else 0

theorem radialProductTerm_measurable {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (measure : Measure ℝ) (coefficient : ℝ → ℤ × ℤ → ℂ)
    (coefficientMeasurable : ∀ shift, AEStronglyMeasurable (fun radius => coefficient radius shift) measure)
    (high low : ℝ → CellL2 dimension) (highMeasurable : AEStronglyMeasurable high measure)
    (lowMeasurable : AEStronglyMeasurable low measure) (shift : ℤ × ℤ) :
    AEStronglyMeasurable (radialProductTerm parameters power coefficient high low shift) measure := by
  classical
  apply cellL2_measurable_of_coordinates
  intro mode
  have literal : (fun radius => radialProductTerm parameters power coefficient high low shift radius mode) =
      (Icc (0 : ℝ) 1).indicator (fun radius =>
        ((balancedProductRatio parameters power radius shift mode : ℂ) * coefficient radius shift) •
          (high radius (mode - shift) + ((annularFrequency shift.1 shift.2 : ℂ) ^ power) • low radius (mode - shift))) := by
    funext radius
    by_cases inside : radius ∈ Icc (0 : ℝ) 1
    · simp only [radialProductTerm, dif_pos inside, Set.indicator_of_mem inside, balancedSingleProduct_value]
    · simp only [radialProductTerm, dif_neg inside, Set.indicator_of_notMem inside, lp.coeFn_zero, Pi.zero_apply]
  rw [literal]
  apply AEStronglyMeasurable.indicator _ measurableSet_Icc
  have scalar : AEStronglyMeasurable (fun radius =>
      (balancedProductRatio parameters power radius shift mode : ℂ) * coefficient radius shift) measure :=
    (Complex.continuous_ofReal.comp (balancedProductRatio_continuous parameters power shift mode)).aestronglyMeasurable.mul
      (coefficientMeasurable shift)
  have highCoordinate : AEStronglyMeasurable (fun radius => high radius (mode - shift)) measure :=
    (lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 (mode - shift)).continuous.comp_aestronglyMeasurable highMeasurable
  have lowCoordinate : AEStronglyMeasurable (fun radius => low radius (mode - shift)) measure :=
    (lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 (mode - shift)).continuous.comp_aestronglyMeasurable lowMeasurable
  have vector := highCoordinate.add
    (lowCoordinate.const_smul ((annularFrequency shift.1 shift.2 : ℂ) ^ power))
  exact scalar.smul vector

def radialProductValue {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (coefficient : ℝ → ℤ × ℤ → ℂ) (high low : ℝ → CellL2 dimension) (radius : ℝ) : CellL2 dimension :=
  ∑' shift, radialProductTerm parameters power coefficient high low shift radius

theorem radialProductValue_inside {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (coefficient : ℝ → ℤ × ℤ → ℂ) (high low : ℝ → CellL2 dimension)
    (radius : ℝ) (inside : radius ∈ Icc (0 : ℝ) 1) :
    radialProductValue parameters power coefficient high low radius =
      pointwiseProduct parameters power radius inside.1 inside.2 (coefficient radius) (high radius) (low radius) := by
  simp only [radialProductValue, radialProductTerm, dif_pos inside, pointwiseProduct]

theorem radialProductValue_measurable {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (measure : Measure ℝ) (coefficient : ℝ → ℤ × ℤ → ℂ)
    (coefficientMeasurable : ∀ shift, AEStronglyMeasurable (fun radius => coefficient radius shift) measure)
    (moments : ∀ᵐ radius ∂measure, radius ∈ Icc (0 : ℝ) 1 →
      Summable (productMoment parameters 0 radius (coefficient radius)) ∧
      Summable (productMoment parameters power radius (coefficient radius)))
    (high low : ℝ → CellL2 dimension) (highMeasurable : AEStronglyMeasurable high measure)
    (lowMeasurable : AEStronglyMeasurable low measure) :
    AEStronglyMeasurable (radialProductValue parameters power coefficient high low) measure := by
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset (ℤ × ℤ)))
    (f := fun shifts radius => ∑ shift ∈ shifts, radialProductTerm parameters power coefficient high low shift radius)
  · intro shifts
    exact Finset.aestronglyMeasurable_fun_sum shifts (fun shift _ =>
      radialProductTerm_measurable parameters power measure coefficient coefficientMeasurable high low highMeasurable lowMeasurable shift)
  · filter_upwards [moments] with radius moment
    by_cases inside : radius ∈ Icc (0 : ℝ) 1
    · have summable := (pointwiseProduct_summable_norm parameters power radius inside.1 inside.2
        (coefficient radius) (moment inside).1 (moment inside).2 (high radius) (low radius)).of_norm
      change HasSum (fun shift => radialProductTerm parameters power coefficient high low shift radius)
        (radialProductValue parameters power coefficient high low radius)
      simpa only [radialProductValue, radialProductTerm, dif_pos inside] using summable.hasSum
    · simp only [radialProductValue, radialProductTerm, dif_neg inside, tsum_zero, Finset.sum_const_zero]
      exact tendsto_const_nhds

end Grad.SourceCollarCoefficients

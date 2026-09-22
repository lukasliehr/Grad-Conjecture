import AKR5GenuineHighEnergyModeRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularOriginalSmoothCore Grad.AnnularReconstruction Grad.AnnularVariational Grad.CircularHighRegularity
open Grad.AnnularOriginalLow Grad.AnnularStrongData
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem actualPotentialWeight_frequency_bound (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius| ≤
      Real.sqrt (annularPotentialUpperConstant lower length) * Grad.SourceCollarDivision.annularFrequency mode.val.1 mode.val.2 := by
  have frequency : 0 ≤ Grad.SourceCollarDivision.annularFrequency mode.val.1 mode.val.2 := by unfold Grad.SourceCollarDivision.annularFrequency; positivity
  have constant : 0 ≤ annularPotentialUpperConstant lower length := by unfold annularPotentialUpperConstant; positivity
  have scalar := annularPotential_upper lower length positive mode radius inside
  change |Real.sqrt (annularPotential length (max lower radius) mode.val.1 mode.val.2)| ≤ _
  rw [max_eq_right inside.1,abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ Real.sqrt (annularPotentialUpperConstant lower length * Grad.SourceCollarDivision.annularFrequency mode.val.1 mode.val.2 ^ 2) :=
      Real.sqrt_le_sqrt scalar
    _ = _ := by rw [Real.sqrt_mul constant,Real.sqrt_sq frequency]

def originalEnergyRealizationConstant (lower length : ℝ) : ℝ :=
  1 + Real.sqrt (annularPotentialUpperConstant lower length) + Real.sqrt 2 * sourceEndpointConstant lower

theorem originalEnergyRealizationConstant_nonnegative (lower length : ℝ) :
    0 ≤ originalEnergyRealizationConstant lower length := by
  unfold originalEnergyRealizationConstant sourceEndpointConstant
  positivity

/-- Only one polynomial Fourier grade and fixed-collar constants are
needed to realize the literal original energy graph. -/
theorem radialGraphEnergyMode_bound (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : HighAnnularMode) (field : WeightedRadialH1 1 lower) :
    ‖radialGraphEnergyMode lower length positive bounded mode field‖ ≤
      originalEnergyRealizationConstant lower length * Grad.SourceCollarDivision.annularFrequency mode.val.1 mode.val.2 * ‖field‖ := by
  have outer := hilbert_norm_le_add (radialGraphEnergyMode lower length positive bounded mode field)
  have inner := hilbert_norm_le_add (radialGraphEnergyMode lower length positive bounded mode field).ofLp.2
  have first := weightedRadialCoordinate_bound 1 lower 1 field
  have zero := weightedRadialCoordinate_bound 1 lower 0 field
  have mass := originalLow_scalar_bound lower
    (annularPotentialWeight lower length positive mode.val.1 mode.val.2)
    (Real.sqrt (annularPotentialUpperConstant lower length) * Grad.SourceCollarDivision.annularFrequency mode.val.1 mode.val.2)
    (actualPotentialWeight_frequency_bound lower length positive mode) (weightedRadialCoordinate 1 lower 0 field)
  have trace := weightedRadialTrace_bound 1 lower positive bounded 1 field
  have frequency : 1 ≤ Grad.SourceCollarDivision.annularFrequency mode.val.1 mode.val.2 := by
    unfold Grad.SourceCollarDivision.annularFrequency
    linarith [abs_nonneg (mode.val.1 : ℝ),abs_nonneg (mode.val.2 : ℝ)]
  have mass' := mass.trans (mul_le_mul_of_nonneg_left zero
    (mul_nonneg (Real.sqrt_nonneg _) (zero_le_one.trans frequency)))
  have trace' := mul_le_mul_of_nonneg_left trace (Real.sqrt_nonneg 2)
  change ‖radialGraphEnergyMode lower length positive bounded mode field‖ ≤
    ‖weightedRadialCoordinate 1 lower 1 field‖ +
      ‖WithLp.toLp 2 (collarScalar 1 lower (annularPotentialWeight lower length positive mode.val.1 mode.val.2)
        (weightedRadialCoordinate 1 lower 0 field),Real.sqrt 2 • weightedRadialTrace 1 lower positive bounded 1 field)‖ at outer
  change ‖WithLp.toLp 2 (collarScalar 1 lower (annularPotentialWeight lower length positive mode.val.1 mode.val.2)
    (weightedRadialCoordinate 1 lower 0 field),Real.sqrt 2 • weightedRadialTrace 1 lower positive bounded 1 field)‖ ≤
      ‖collarScalar 1 lower (annularPotentialWeight lower length positive mode.val.1 mode.val.2)
        (weightedRadialCoordinate 1 lower 0 field)‖ + ‖Real.sqrt 2 • weightedRadialTrace 1 lower positive bounded 1 field‖ at inner
  rw [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg 2)] at inner
  have combined := outer.trans (add_le_add first (inner.trans (add_le_add mass' trace')))
  simp only [one_mul] at combined
  have valueLe : ‖field‖ ≤ Grad.SourceCollarDivision.annularFrequency mode.val.1 mode.val.2 * ‖field‖ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right frequency (norm_nonneg field)
  have traceLe := mul_le_mul_of_nonneg_left valueLe
    (mul_nonneg (Real.sqrt_nonneg 2) (show 0 ≤ sourceEndpointConstant lower by unfold sourceEndpointConstant; positivity))
  unfold originalEnergyRealizationConstant
  nlinarith

end Grad.AnnularOriginalCoreRealization

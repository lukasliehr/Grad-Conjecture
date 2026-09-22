import AID6LiteralNormalizedSecondRow

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set MeasureTheory Filter
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularCurrentGreen
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularCircularForm
open Grad.AnnularTiltedReference Grad.AnnularGrades Grad.CircularHighRegularity Grad.AnnularSourceGraph
open Grad.AnnularOmegaGraph Grad.CircularHighWeak Grad.ActualReferenceAssembly

theorem actualPotential_le_omega_square (L radius : ℝ) (mode : HighAnnularMode) :
    annularPotential L radius mode.val.1 mode.val.2 ≤ annularOmega L radius mode ^ 2 := by
  have bound := (highMultiplier_bounds mode.val.1 (highMode_not_low _ mode.property)).2
  have cell := mul_le_mul_of_nonneg_right bound (sq_nonneg ((mode.val.2 : ℝ) / L))
  rw [annularOmega_sq, annularPotential]
  calc
    _ = ((mode.val.1 : ℝ) / radius) ^ 2 + highMultiplier mode.val.1 * ((mode.val.2 : ℝ) / L) ^ 2 := by ring
    _ ≤ ((mode.val.1 : ℝ) / radius) ^ 2 + 1 * ((mode.val.2 : ℝ) / L) ^ 2 := add_le_add le_rfl cell
    _ = _ := by ring

theorem actualTiltSlope_le_omega (parameters : PhaseParameters) (L radius : ℝ)
    (lengthPositive : 0 < L) (radiusPositive : 0 < radius) (radiusUpper : radius ≤ 1)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (mode : HighAnnularMode) :
    |annularPhaseSlope parameters mode.val.2 radius - annularTiltExponent / radius| ≤ annularOmega L radius mode := by
  have slope := annularTiltSlope_dominated parameters L radius mode.val.1 mode.val.2
    lengthPositive radiusPositive radiusUpper mode.property widthHalf widthLength
  have potential := actualPotential_le_omega_square L radius mode
  have nonnegative := annularOmega_nonneg L radius mode
  have absolute := sq_abs (annularPhaseSlope parameters mode.val.2 radius - annularTiltExponent / radius)
  nlinarith [abs_nonneg (annularPhaseSlope parameters mode.val.2 radius - annularTiltExponent / radius),
    sq_nonneg (annularOmega L radius mode)]

theorem reciprocalRadius_le_omega (L radius : ℝ) (positive : 0 < radius) (mode : HighAnnularMode) :
    radius⁻¹ ≤ (1 / 3 : ℝ) * annularOmega L radius mode := by
  have angular := (div_le_iff₀ positive).mp (annularOmega_angular L radius positive mode)
  have high : (3 : ℝ) ≤ |(mode.val.1 : ℝ)| := by exact_mod_cast mode.property
  rw [inv_eq_one_div]
  apply (div_le_iff₀ positive).mpr
  nlinarith

/-- All BF14 normalized output factors are bounded on the original physical collar, independently of its inner radius. -/
theorem physicalOmega_factors (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (mode : HighAnnularMode) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |annularTiltCurve parameters lower positive mode.val.2 radius / annularOmegaCurve lower L positive mode radius| ≤ 1 ∧
    |highReciprocalRadius lower positive radius / annularOmegaCurve lower L positive mode radius| ≤ 1 / 3 ∧
    |((mode.val.2 : ℝ) / L) / annularOmegaCurve lower L positive mode radius| ≤ 1 ∧
    |((mode.val.1 : ℝ) / max lower radius) / annularOmegaCurve lower L positive mode radius| ≤ 1 := by
  have rp := positive.trans_le inside.1
  have op := annularOmega_pos L radius rp mode
  have phase := actualTiltSlope_le_omega parameters L radius lengthPositive rp inside.2 widthHalf widthLength mode
  have inverse := reciprocalRadius_le_omega L radius rp mode
  have cell := annularOmega_cell L radius lengthPositive mode
  have angular := annularOmega_angular L radius rp mode
  change |(annularPhaseSlope parameters mode.val.2 radius - annularTiltExponent / max lower radius) /
    annularOmega L (max lower radius) mode| ≤ 1 ∧
    |(max lower radius)⁻¹ / annularOmega L (max lower radius) mode| ≤ 1 / 3 ∧
    |((mode.val.2 : ℝ) / L) / annularOmega L (max lower radius) mode| ≤ 1 ∧
    |((mode.val.1 : ℝ) / max lower radius) / annularOmega L (max lower radius) mode| ≤ 1
  rw [max_eq_right inside.1]
  simp only [abs_div, abs_of_pos op, abs_of_pos rp, abs_of_pos lengthPositive,
    abs_of_pos (inv_pos.mpr rp)]
  constructor
  · exact (div_le_iff₀ op).mpr (by simpa using phase)
  constructor
  · exact (div_le_iff₀ op).mpr inverse
  constructor
  · exact (div_le_iff₀ op).mpr (by simpa using cell)
  · exact (div_le_iff₀ op).mpr (by simpa using angular)

end Grad.AnnularCurrentGreen

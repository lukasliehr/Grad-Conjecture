import ANR50LiteralOuterDerivative

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.WeightedTrace

private theorem radialSecond_algebra (dimension : ℕ) (radius angular : ℝ) (nonzero : radius ≠ 0)
    (mass : ℂ) (value flux forcing : ComplexEuclidean dimension) :
    - (radius⁻¹ • ((angular ^ 2 / radius) • value + radius • (mass • value - forcing)) +
      -(radius ^ 2)⁻¹ • flux) -
      radius⁻¹ • (radius⁻¹ • flux) + (angular ^ 2 / radius ^ 2) • value + mass • value = forcing := by
  have square : (radius ^ 2)⁻¹ = radius⁻¹ * radius⁻¹ := by ring
  have angularLaw : radius⁻¹ * (angular ^ 2 / radius) = angular ^ 2 / radius ^ 2 := by ring
  simp only [smul_add, smul_smul, inv_mul_cancel₀ nonzero, one_smul, angularLaw, square]
  module

/-- The classical first-order flux system implies the literal AN19
second-order equation, with derivatives within the original closed collar. -/
theorem radialSystem_secondEquation (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (mode : ℤ) (mass : ℂ)
    (value flux forcing : C(ℝ, ComplexEuclidean dimension))
    (first : ∀ radius ∈ Icc lower 1, HasDerivWithinAt value (radius⁻¹ • flux radius) (Icc lower 1) radius)
    (second : ∀ radius ∈ Icc lower 1, HasDerivWithinAt flux
      (((mode : ℝ) ^ 2 / radius) • value radius + radius • (mass • value radius - forcing radius))
      (Icc lower 1) radius) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    -derivWithin (derivWithin value (Icc lower 1)) (Icc lower 1) radius -
      radius⁻¹ • derivWithin value (Icc lower 1) radius +
      ((mode : ℝ) ^ 2 / radius ^ 2) • value radius + mass • value radius = forcing radius := by
  have unique := uniqueDiffOn_Icc bounded
  have firstLaw (point : ℝ) (member : point ∈ Icc lower 1) :
      derivWithin value (Icc lower 1) point = point⁻¹ • flux point :=
    (first point member).derivWithin (unique point member)
  have nonzero : radius ≠ 0 := (positive.trans_le inside.1).ne'
  have differentiated := (hasDerivWithinAt_inv nonzero (Icc lower 1)).smul (second radius inside)
  have actualDerivative := differentiated.congr firstLaw (firstLaw radius inside)
  have secondLaw := actualDerivative.derivWithin (unique radius inside)
  rw [secondLaw, firstLaw radius inside]
  exact radialSecond_algebra dimension radius (mode : ℝ) nonzero mass (value radius) (flux radius) (forcing radius)

/-- Exact original AN19 for the same inverse and smooth original source.
All coefficients and the radial source are the literal Fourier coefficients. -/
theorem weakInverse_literal_radialEquation (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (source : highDiskL2) (mode : ℤ) (high : mode ∉ lowAngularModes)
    (core : ClosedJet 1) (same : source.val = closedL2Core core)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    let value := radialSectionExtension 1 lower bounded.le
      (diskRadialValueSection lower positive bounded mode (highRobinWeakInverse parameter source).val);
    -derivWithin (derivWithin value (Icc lower 1)) (Icc lower 1) radius -
      radius⁻¹ • derivWithin value (Icc lower 1) radius +
      ((mode : ℝ) ^ 2 / radius ^ 2) • value radius +
      (((parameter ^ 2 * (1 - 4 / (mode : ℝ) ^ 2) : ℝ)) : ℂ) • value radius =
        diskCoreRadialCurve mode core radius := by
  have existence := weakInverse_classical_radial_system lower positive bounded mode high parameter source core same
  obtain ⟨flux, _actual, first, second⟩ := existence
  exact radialSystem_secondEquation 1 lower positive bounded mode
    (((parameter ^ 2 * (1 - 4 / (mode : ℝ) ^ 2) : ℝ)) : ℂ)
    (radialSectionExtension 1 lower bounded.le
      (diskRadialValueSection lower positive bounded mode (highRobinWeakInverse parameter source).val))
    flux (diskCoreRadialCurve mode core) first second radius inside

end Grad.CircularHighRegularity

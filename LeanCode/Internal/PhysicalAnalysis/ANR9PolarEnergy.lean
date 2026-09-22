import ANR8WeakDistribution
import RSC3AnnularBessel

noncomputable section
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ContDiff Interval BigOperators

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.BoundaryTrace

/-- Exact ordinary H1 energy density; no auxiliary positive analytic phase
is inserted into the AN18 single-disk space. -/
theorem diskCore_density (field : ClosedJet 1) :
    (∫ point in closedUnitDisk, cartesianDensityGlobal 1 1 field point) = ‖diskCoreInto field‖ ^ 2 := by
  have formula := cartesianDensityGlobal_integral 1 1 field
  exact formula.trans (by
    simpa only [one_pow, one_mul, GradeMultiIndex.toCartesian,
      Grad.GaugeCoefficients.Algebra.derivativeMultiIndex] using (diskCore_norm_sq field).symm)

theorem diskPolar_derivative_sq (field : ClosedJet 1) (radial : ℕ) (upper : radial ≤ 1)
    (point : ℝ × ℝ) (inside : point ∈ polarRectangle) :
    ‖radialIter radial (originalPolarValue field) point‖ ^ 2 ≤
      polarOrderConstant radial * cartesianDensityGlobal 1 1 field (polarPlane point) := by
  have normBound := radialAngular_norm_le radial 0 (originalPolarValue field) (originalPolarValue_smooth field) point
  have density := weighted_polar_derivative_sq_le_density 1 le_rfl upper field point inside
  have estimate : ‖iteratedFDeriv ℝ radial (originalPolarValue field) point‖ ^ 2 ≤
      polarOrderConstant radial * cartesianPointDensity 1 1 field
        (polarClosedPoint point.1 point.2 inside.1.1 inside.1.2) := by
    simpa only [one_pow, one_mul] using density
  have normBound' : ‖radialIter radial (originalPolarValue field) point‖ ≤
      ‖iteratedFDeriv ℝ radial (originalPolarValue field) point‖ := by
    have indexNorm := congrArg (fun order : ℕ =>
      ‖iteratedFDeriv ℝ order (originalPolarValue field) point‖) (Nat.zero_add radial)
    have raw : ‖radialIter radial (originalPolarValue field) point‖ ≤
        ‖iteratedFDeriv ℝ (0 + radial) (originalPolarValue field) point‖ := by
      simpa only [angularJet_zero] using normBound
    exact raw.trans_eq indexNorm
  exact (pow_le_pow_left₀ (norm_nonneg _) normBound' 2).trans
    (estimate.trans_eq (congrArg (fun value : ℝ => polarOrderConstant radial * value)
      (cartesianDensityGlobal_closed 1 1 field
        (polarClosedPoint point.1 point.2 inside.1.1 inside.1.2)).symm))

/-- The existing full polar Jacobian theorem bounds the genuine radial
value and derivative energy on every closed collar a≤r≤1. -/
theorem diskPolar_energy (field : ClosedJet 1) (radial : ℕ) (upper : radial ≤ 1)
    (lower : ℝ) (nonnegative : 0 ≤ lower) (bounded : lower ≤ 1) :
    annularIntegral lower (fun point => ‖radialIter radial (originalPolarValue field) point‖ ^ 2) ≤
      polarOrderConstant radial * ‖diskCoreInto field‖ ^ 2 := by
  let density := cartesianDensityGlobal 1 1 field
  have densityContinuous := cartesianDensityGlobal_continuous 1 1 field
  have comparison := annularIntegral_mono lower nonnegative bounded
    (fun point => ‖radialIter radial (originalPolarValue field) point‖ ^ 2)
    (fun point => polarOrderConstant radial * density (polarPlane point))
    ((radialIter_smooth radial _ (originalPolarValue_smooth field)).continuous.norm.pow 2)
    (continuous_const.mul (densityContinuous.comp polarPlane_smooth.continuous))
    (diskPolar_derivative_sq field radial upper)
  rw [annularIntegral_const_mul] at comparison
  have area := annularIntegral_le_disk lower nonnegative bounded density densityContinuous
    (fun point => cartesianPointDensity_nonnegative _ zero_le_one _ _ _)
  have integral := diskCore_density field
  exact comparison.trans ((mul_le_mul_of_nonneg_left area (polarOrderConstant_nonnegative radial)).trans_eq
    (congrArg (fun value : ℝ => polarOrderConstant radial * value) integral))

theorem diskPolar_coefficient_energy (field : ClosedJet 1) (mode : ℤ)
    (radial : ℕ) (upper : radial ≤ 1)
    (lower : ℝ) (nonnegative : 0 ≤ lower) (bounded : lower ≤ 1) :
    annularCoefficientEnergy lower (radialIter radial (originalPolarValue field)) mode ≤
      ((2 * Real.pi)⁻¹ * polarOrderConstant radial) * ‖diskCoreInto field‖ ^ 2 := by
  have bessel := annular_angular_bessel lower nonnegative bounded 0
    (radialIter radial (originalPolarValue field))
    (radialIter_smooth radial _ (originalPolarValue_smooth field))
    (radialIter_periodic radial _ (originalPolarValue_periodic field)) {mode}
  have single : annularCoefficientEnergy lower (radialIter radial (originalPolarValue field)) mode ≤
      (2 * Real.pi)⁻¹ * annularIntegral lower (fun point => ‖radialIter radial (originalPolarValue field) point‖ ^ 2) := by
    simpa only [Nat.mul_zero, pow_zero, one_mul, Finset.sum_singleton, angularJet_zero] using bessel
  exact single.trans ((mul_le_mul_of_nonneg_left
    (diskPolar_energy field radial upper lower nonnegative bounded) (by positivity)).trans_eq (mul_assoc _ _ _).symm)

end Grad.CircularHighRegularity

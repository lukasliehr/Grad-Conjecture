import ANR10RadialCore
import ANG24OrdinarySobolevSource

noncomputable section
open Set MeasureTheory
open scoped ContDiff Interval BigOperators
namespace Grad.OrdinarySourceRadial
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.BoundaryTrace
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

/-- Exact density identity at every original ordinary disk Sobolev grade. -/
theorem ordinaryCore_density (grade : ℕ) (field : ClosedJet 1) :
    (∫ point in closedUnitDisk, cartesianDensityGlobal 1 grade field point) =
      ‖unitDiskCoreInto grade field‖ ^ 2 := by
  have density := cartesianDensityGlobal_integral 1 grade field
  have norm := unitDiskSobolev_norm_sq grade (unitDiskCoreInto grade field)
  have normRows : ‖unitDiskCoreInto grade field‖ ^ 2 =
      ∑ index : DerivativeIndex grade, ‖closedDerivativeL2 (derivativeMultiIndex index) field‖ ^ 2 := by
    simpa only [unitDiskDerivative_core] using norm
  exact density.trans (by
    simpa only [one_pow, one_mul, GradeMultiIndex.toCartesian, derivativeMultiIndex] using normRows.symm)

theorem ordinaryPolar_mixed_sq (grade radial angular : ℕ) (paid : angular + radial ≤ grade)
    (field : ClosedJet 1) (point : ℝ × ℝ) (inside : point ∈ polarRectangle) :
    ‖angularJet angular (radialIter radial (originalPolarValue field)) point‖ ^ 2 ≤
      polarOrderConstant (angular + radial) * cartesianDensityGlobal 1 grade field (polarPlane point) := by
  have normBound := radialAngular_norm_le radial angular (originalPolarValue field)
    (originalPolarValue_smooth field) point
  have density := weighted_polar_derivative_sq_le_density 1 le_rfl paid field point inside
  have estimate : ‖iteratedFDeriv ℝ (angular + radial) (originalPolarValue field) point‖ ^ 2 ≤
      polarOrderConstant (angular + radial) * cartesianPointDensity 1 grade field
        (polarClosedPoint point.1 point.2 inside.1.1 inside.1.2) := by
    simpa only [one_pow, one_mul] using density
  exact (pow_le_pow_left₀ (norm_nonneg _) normBound 2).trans
    (estimate.trans_eq (congrArg (fun value : ℝ => polarOrderConstant (angular + radial) * value)
      (cartesianDensityGlobal_closed 1 grade field
        (polarClosedPoint point.1 point.2 inside.1.1 inside.1.2)).symm))

/-- The true polar mixed derivative energy is controlled by the unweighted
Cartesian source norm, on every collar and without analytic-width loss. -/
theorem ordinaryPolar_mixed_energy (grade radial angular : ℕ) (paid : angular + radial ≤ grade)
    (field : ClosedJet 1) (lower : ℝ) (nonnegative : 0 ≤ lower) (bounded : lower ≤ 1) :
    annularIntegral lower (fun point =>
      ‖angularJet angular (radialIter radial (originalPolarValue field)) point‖ ^ 2) ≤
      polarOrderConstant (angular + radial) * ‖unitDiskCoreInto grade field‖ ^ 2 := by
  let density := cartesianDensityGlobal 1 grade field
  have densityContinuous := cartesianDensityGlobal_continuous 1 grade field
  have comparison := annularIntegral_mono lower nonnegative bounded
    (fun point => ‖angularJet angular (radialIter radial (originalPolarValue field)) point‖ ^ 2)
    (fun point => polarOrderConstant (angular + radial) * density (polarPlane point))
    ((angularJet_smooth angular _ (radialIter_smooth radial _ (originalPolarValue_smooth field))).continuous.norm.pow 2)
    (continuous_const.mul (densityContinuous.comp polarPlane_smooth.continuous))
    (ordinaryPolar_mixed_sq grade radial angular paid field)
  rw [annularIntegral_const_mul] at comparison
  have area := annularIntegral_le_disk lower nonnegative bounded density densityContinuous
    (fun point => cartesianPointDensity_nonnegative _ zero_le_one _ _ _)
  exact comparison.trans ((mul_le_mul_of_nonneg_left area (polarOrderConstant_nonnegative _)).trans_eq
    (congrArg (fun value : ℝ => polarOrderConstant (angular + radial) * value) (ordinaryCore_density grade field)))

theorem ordinaryRadial_finite_energy (grade radial angular : ℕ) (paid : angular + radial ≤ grade)
    (field : ClosedJet 1) (lower : ℝ) (nonnegative : 0 ≤ lower) (bounded : lower ≤ 1)
    (modes : Finset ℤ) :
    (∑ mode ∈ modes, |(mode : ℝ)| ^ (2 * angular) *
      annularCoefficientEnergy lower (radialIter radial (originalPolarValue field)) mode) ≤
      ((2 * Real.pi)⁻¹ * polarOrderConstant (angular + radial)) * ‖unitDiskCoreInto grade field‖ ^ 2 := by
  have bessel := annular_angular_bessel lower nonnegative bounded angular
    (radialIter radial (originalPolarValue field))
    (radialIter_smooth radial _ (originalPolarValue_smooth field))
    (radialIter_periodic radial _ (originalPolarValue_periodic field)) modes
  exact bessel.trans ((mul_le_mul_of_nonneg_left
    (ordinaryPolar_mixed_energy grade radial angular paid field lower nonnegative bounded)
    (by positivity : 0 ≤ (2 * Real.pi)⁻¹)).trans_eq (mul_assoc _ _ _).symm)

end Grad.OrdinarySourceRadial

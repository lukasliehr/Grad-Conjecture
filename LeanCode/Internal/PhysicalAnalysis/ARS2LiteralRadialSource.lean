import ARS1OrdinarySourcePolarEnergy
import ANR31LiteralSmoothRadialSource

noncomputable section
open Set MeasureTheory
open scoped ContDiff Interval BigOperators
namespace Grad.OrdinarySourceRadial
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.SourceCollarRestriction Grad.SourceCollarDivision
open Grad.AnnularSourceGraph Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The literal derivative of the original Fourier source coefficient. -/
theorem sourceRadial_iteratedDeriv (field : ClosedJet 1) (mode : ℤ) (order : ℕ) :
    iteratedDeriv order (diskCoreRadialCurve mode field) =
      radialCoefficientJet (originalPolarValue field) mode order := by
  induction order with
  | zero => rfl
  | succ order inductionHypothesis =>
    rw [iteratedDeriv_succ, inductionHypothesis]
    funext radius
    exact (radialCoefficientJet_hasDerivAt _ (originalPolarValue_smooth field) mode order radius).deriv

/-- Within derivatives at both collar endpoints equal the original smooth
Fourier coefficient derivatives, so the ODE consumer uses the same source. -/
theorem sourceRadial_iteratedDerivWithin (field : ClosedJet 1) (mode : ℤ) (order : ℕ)
    (lower : ℝ) (bounded : lower < 1) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    iteratedDerivWithin order (diskCoreRadialCurve mode field) (Icc lower 1) radius =
      radialCoefficientJet (originalPolarValue field) mode order radius := by
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc bounded)
    ((diskCoreRadialCurve_smooth mode field).contDiffAt.of_le (by exact_mod_cast le_top)) inside,
    sourceRadial_iteratedDeriv]

/-- The stored radial derivative energy is the original r dr integral. -/
theorem sourceRadial_energy_literal (field : ClosedJet 1) (mode : ℤ) (radial : ℕ) (lower : ℝ) :
    annularCoefficientEnergy lower (radialIter radial (originalPolarValue field)) mode =
      ∫ radius in lower..1, radius * ‖iteratedDeriv radial (diskCoreRadialCurve mode field) radius‖ ^ 2 := by
  rw [sourceRadial_iteratedDeriv]
  rfl

theorem sourceRadial_energy_within (field : ClosedJet 1) (mode : ℤ) (radial : ℕ)
    (lower : ℝ) (bounded : lower < 1) :
    annularCoefficientEnergy lower (radialIter radial (originalPolarValue field)) mode =
      ∫ radius in lower..1, radius *
        ‖iteratedDerivWithin radial (diskCoreRadialCurve mode field) (Icc lower 1) radius‖ ^ 2 := by
  unfold annularCoefficientEnergy
  apply intervalIntegral.integral_congr
  intro radius inside
  have member : radius ∈ Icc lower 1 := by simpa only [uIcc_of_le bounded.le] using inside
  dsimp only
  rw [sourceRadial_iteratedDerivWithin field mode radial lower bounded radius member]
  rfl

def sourceRadialEnergy (lower : ℝ) (radial angular : ℕ) (field : ClosedJet 1) (mode : ℤ) : ℝ :=
  |(mode : ℝ)| ^ (2 * angular) *
    annularCoefficientEnergy lower (radialIter radial (originalPolarValue field)) mode

theorem sourceRadialEnergy_nonnegative (lower : ℝ) (nonnegative : 0 ≤ lower) (bounded : lower ≤ 1)
    (radial angular : ℕ) (field : ClosedJet 1) (mode : ℤ) :
    0 ≤ sourceRadialEnergy lower radial angular field mode :=
  mul_nonneg (pow_nonneg (abs_nonneg _) _)
    (annularCoefficientEnergy_nonnegative lower nonnegative bounded _ _)

theorem sourceRadialEnergy_finite (grade radial angular : ℕ) (paid : angular + radial ≤ grade)
    (field : ClosedJet 1) (lower : ℝ) (nonnegative : 0 ≤ lower) (bounded : lower ≤ 1)
    (modes : Finset ℤ) :
    (∑ mode ∈ modes, sourceRadialEnergy lower radial angular field mode) ≤
      ((2 * Real.pi)⁻¹ * polarOrderConstant (angular + radial)) * ‖unitDiskCoreInto grade field‖ ^ 2 :=
  ordinaryRadial_finite_energy grade radial angular paid field lower nonnegative bounded modes

/-- All original source radial/angular derivative energies through grade s,
with literal Fourier coefficients and a cutoff-independent collective bound. -/
theorem actualSourceMixedRadialEnergy (grade radial angular : ℕ) (paid : angular + radial ≤ grade)
    (field : ClosedJet 1) (lower : ℝ) (nonnegative : 0 ≤ lower) (bounded : lower ≤ 1) :
    (∀ mode : ℤ, sourceRadialEnergy lower radial angular field mode =
      |(mode : ℝ)| ^ (2 * angular) *
        ∫ radius in lower..1, radius * ‖iteratedDeriv radial (diskCoreRadialCurve mode field) radius‖ ^ 2) ∧
    Summable (sourceRadialEnergy lower radial angular field) ∧
    (∑' mode : ℤ, sourceRadialEnergy lower radial angular field mode) ≤
      ((2 * Real.pi)⁻¹ * polarOrderConstant (angular + radial)) * ‖unitDiskCoreInto grade field‖ ^ 2 := by
  have finite := sourceRadialEnergy_finite grade radial angular paid field lower nonnegative bounded
  have summable := summable_of_sum_le
    (sourceRadialEnergy_nonnegative lower nonnegative bounded radial angular field) finite
  refine ⟨?_, summable, summable.tsum_le_of_sum_le finite⟩
  intro mode
  exact congrArg (fun energy : ℝ => |(mode : ℝ)| ^ (2 * angular) * energy)
    (sourceRadial_energy_literal field mode radial lower)

end Grad.OrdinarySourceRadial

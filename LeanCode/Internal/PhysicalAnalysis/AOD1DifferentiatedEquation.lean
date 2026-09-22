import AQS3ActualWeightedRadialConsumer
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff BigOperators
namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.AnnularSourceGraph Grad.SourceCollarDivision

/-- The genuine derivative Leibniz row, written with derivative count on
its scalar coefficient and on its vector factor. -/
def radialLeibniz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (order : ℕ) (coefficient : ℝ → ℝ) (value : ℝ → E) (domain : Set ℝ) (radius : ℝ) : E :=
  ∑ index ∈ Finset.range (order + 1), order.choose index •
    iteratedDerivWithin index coefficient domain radius • iteratedDerivWithin (order - index) value domain radius

/-- Differentiating an actual second-order equation gives genuine within
jets at both endpoints, before any norm estimate or abstract recurrence. -/
theorem differentiated_radial_equation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (domain : Set ℝ) (unique : UniqueDiffOn ℝ domain)
    (value forcing : ℝ → E) (firstCoefficient secondCoefficient : ℝ → ℝ) (modeSquared scalar : ℝ)
    (valueSmooth : ContDiffOn ℝ ∞ value domain) (forcingSmooth : ContDiffOn ℝ ∞ forcing domain)
    (firstSmooth : ContDiffOn ℝ ∞ firstCoefficient domain)
    (secondSmooth : ContDiffOn ℝ ∞ secondCoefficient domain)
    (equation : EqOn (derivWithin (derivWithin value domain) domain)
      (fun radius => -(firstCoefficient radius • derivWithin value domain radius) +
        modeSquared • (secondCoefficient radius • value radius) + scalar • value radius - forcing radius) domain)
    (order : ℕ) (radius : ℝ) (inside : radius ∈ domain) :
    iteratedDerivWithin (order + 2) value domain radius =
      -radialLeibniz order firstCoefficient (derivWithin value domain) domain radius +
        modeSquared • radialLeibniz order secondCoefficient value domain radius +
        scalar • iteratedDerivWithin order value domain radius - iteratedDerivWithin order forcing domain radius := by
  have slopeSmooth : ContDiffOn ℝ ∞ (derivWithin value domain) domain :=
    valueSmooth.derivWithin unique (by simp)
  have first : ContDiffOn ℝ order (fun radius => -(firstCoefficient radius • derivWithin value domain radius)) domain :=
    (contDiffOn_infty.mp ((firstSmooth.smul slopeSmooth).neg)) order
  have second : ContDiffOn ℝ order (fun radius => modeSquared • (secondCoefficient radius • value radius)) domain :=
    (contDiffOn_infty.mp ((secondSmooth.smul valueSmooth).const_smul modeSquared)) order
  have third : ContDiffOn ℝ order (fun radius => scalar • value radius) domain :=
    (contDiffOn_infty.mp (valueSmooth.const_smul scalar)) order
  have forcingN : ContDiffOn ℝ order (fun radius => -forcing radius) domain := (contDiffOn_infty.mp forcingSmooth.neg) order
  have left : iteratedDerivWithin (order + 2) value domain radius =
      iteratedDerivWithin order (derivWithin (derivWithin value domain) domain) domain radius := by
    rw [show order + 2 = (order + 1) + 1 by omega, iteratedDerivWithin_succ', iteratedDerivWithin_succ']
  have transfer := iteratedDerivWithin_congr (n := order) equation inside
  have expanded : iteratedDerivWithin order
      (fun radius => -(firstCoefficient radius • derivWithin value domain radius) +
        modeSquared • (secondCoefficient radius • value radius) + scalar • value radius - forcing radius) domain radius =
      -radialLeibniz order firstCoefficient (derivWithin value domain) domain radius +
        modeSquared • radialLeibniz order secondCoefficient value domain radius +
        scalar • iteratedDerivWithin order value domain radius - iteratedDerivWithin order forcing domain radius := by
    simp only [sub_eq_add_neg]
    rw [iteratedDerivWithin_fun_add (n := order) inside unique (((first.add second).add third) radius inside)
        (forcingN radius inside),
      iteratedDerivWithin_fun_add (n := order) inside unique ((first.add second) radius inside)
        (third radius inside),
      iteratedDerivWithin_fun_add (n := order) inside unique (first radius inside)
        (second radius inside),
      iteratedDerivWithin_fun_neg, iteratedDerivWithin_fun_neg,
      iteratedDerivWithin_fun_const_smul_field, iteratedDerivWithin_fun_const_smul_field]
    have firstProduct := iteratedDerivWithin_smul (n := order) inside unique
      ((contDiffOn_infty.mp firstSmooth) order radius inside) ((contDiffOn_infty.mp slopeSmooth) order radius inside)
    have secondProduct := iteratedDerivWithin_smul (n := order) inside unique
      ((contDiffOn_infty.mp secondSmooth) order radius inside) ((contDiffOn_infty.mp valueSmooth) order radius inside)
    rw [show (fun radius => firstCoefficient radius • derivWithin value domain radius) =
        firstCoefficient • derivWithin value domain from rfl, firstProduct,
      show (fun radius => secondCoefficient radius • value radius) = secondCoefficient • value from rfl, secondProduct]
    rfl
  exact left.trans (transfer.trans expanded)

/-- AN19 differentiated on the original collar of the same constructed
inverse, with its actual source Fourier coefficient. -/
theorem actualRadial_differentiated_equation (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core)
    (mode : ℤ) (high : mode ∉ lowAngularModes) (order : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    iteratedDerivWithin (order + 2) (actualRadialValue lower positive bounded mode parameter source) (Icc lower 1) radius =
      -radialLeibniz order (fun radius : ℝ => radius⁻¹)
        (derivWithin (actualRadialValue lower positive bounded mode parameter source) (Icc lower 1)) (Icc lower 1) radius +
      (mode : ℝ) ^ 2 • radialLeibniz order (fun radius : ℝ => radius⁻¹ ^ 2)
        (actualRadialValue lower positive bounded mode parameter source) (Icc lower 1) radius +
      (parameter ^ 2 * highMultiplier mode) •
        iteratedDerivWithin order (actualRadialValue lower positive bounded mode parameter source) (Icc lower 1) radius -
      iteratedDerivWithin order (diskCoreRadialCurve mode core) (Icc lower 1) radius := by
  have inverseSmooth : ContDiffOn ℝ ∞ (fun radius : ℝ => radius⁻¹) (Icc lower 1) :=
    contDiffOn_id.inv (fun radius inside => (positive.trans_le inside.1).ne')
  apply differentiated_radial_equation (Icc lower 1) (uniqueDiffOn_Icc bounded)
    (actualRadialValue lower positive bounded mode parameter source) (diskCoreRadialCurve mode core)
    (fun radius : ℝ => radius⁻¹) (fun radius : ℝ => radius⁻¹ ^ 2) ((mode : ℝ) ^ 2)
    (parameter ^ 2 * highMultiplier mode)
    (weakInverse_closedCollar_smooth lower positive bounded mode high parameter source core same)
    (diskCoreRadialCurve_smooth mode core).contDiffOn inverseSmooth (inverseSmooth.pow 2) ?_ order radius inside
  intro point member
  have literal := actualRadial_second_eq lower positive bounded parameter source mode high core same point member
  simpa only [div_eq_mul_inv, inv_pow, mul_smul, highMultiplier_high mode high, Complex.coe_smul] using literal

end Grad.CircularHighRegularity

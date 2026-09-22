import AOD7ActualBaseEnergies

noncomputable section
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped ContDiff BigOperators Interval
namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.AnnularSourceGraph Grad.SourceCollarDivision Grad.SourceCollarRestriction Grad.OrdinarySourceRadial

private structure RadialEstimateInput (ceiling : ℝ) where
  parameter : ℝ
  parameterBound : |parameter| ≤ ceiling
  source : highDiskL2
  core : ClosedJet 1
  same : source.val = closedL2Core core

/-- Uniform all-radial-count induction from proved ANQ/AQS bases, the
literal differentiated AN19 equation, and the actual ARS source estimates.
The constant precedes every parameter, source, radial count and angular set. -/
theorem actualAllRadial_finite (grade : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (ceiling : ℝ) : ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ parameter : ℝ, |parameter| ≤ ceiling → ∀ (source : highDiskL2) (core : ClosedJet 1),
      source.val = closedL2Core core → ∀ radial : ℕ, radial ≤ grade + 2 → ∀ modes : Finset ℤ,
        (∀ mode ∈ modes, mode ∉ lowAngularModes) →
        (∑ mode ∈ modes, mixedRadialEnergy grade radial (actualRadialJetEnergy lower positive bounded parameter source) mode) ≤
          constant * ‖unitDiskCoreInto grade core‖ ^ 2 := by
  let energy (input : RadialEstimateInput ceiling) (radial : ℕ) (mode : ℤ) : ℝ :=
    mixedRadialEnergy grade radial (actualRadialJetEnergy lower positive bounded input.parameter input.source) mode
  let forcing (input : RadialEstimateInput ceiling) (order : ℕ) (mode : ℤ) : ℝ :=
    |(mode : ℝ)| ^ (2 * (grade - order)) * radialWithinEnergy lower order (diskCoreRadialCurve mode input.core)
  let size (input : RadialEstimateInput ceiling) : ℝ := ‖unitDiskCoreInto grade input.core‖ ^ 2
  let base : ℝ := zeroOneCollarConstant grade + weightedSecondRadialConstant lower ceiling grade
  let sourceConstant : ℝ := (2 * Real.pi)⁻¹ * polarOrderConstant grade
  have baseBound (input : RadialEstimateInput ceiling) (radial : ℕ) (small : radial ≤ 2)
      (modes : Finset ℤ) (high : ∀ mode ∈ modes, mode ∉ lowAngularModes) :
      (∑ mode ∈ modes, energy input radial mode) ≤ base * size input :=
    actualRadial_base_finite lower positive bounded ceiling input.parameter input.parameterBound grade
      input.source input.core input.same radial small modes high
  have forcingBound (input : RadialEstimateInput ceiling) (order : ℕ) (paid : order ≤ grade)
      (modes : Finset ℤ) (_high : ∀ mode ∈ modes, mode ∉ lowAngularModes) :
      (∑ mode ∈ modes, forcing input order mode) ≤ sourceConstant * size input := by
    have equal : (∑ mode ∈ modes, forcing input order mode) =
        ∑ mode ∈ modes, sourceRadialEnergy lower order (grade - order) input.core mode := by
      apply Finset.sum_congr rfl
      intro mode _
      exact congrArg (fun scalar : ℝ => |(mode : ℝ)| ^ (2 * (grade - order)) * scalar)
        (sourceRadial_energy_within input.core mode order lower bounded).symm
    have sourceBound := sourceRadialEnergy_finite grade order (grade - order) (by omega)
      input.core lower positive.le bounded.le modes
    exact equal.trans_le (by simpa only [Nat.sub_add_cancel paid] using sourceBound)
  have recurrence (input : RadialEstimateInput ceiling) (order : ℕ) (paid : order ≤ grade)
      (mode : ℤ) (high : mode ∉ lowAngularModes) : energy input (order + 2) mode ≤ 4 *
      (radialProductConstant lower positive bounded order *
        (∑ index ∈ Finset.range (order + 1), energy input (order - index + 1) mode) +
       radialProductConstant lower positive bounded order *
        (∑ index ∈ Finset.range (order + 1), energy input (order - index) mode) +
       ceiling ^ 4 * energy input order mode + forcing input order mode) :=
    mixedRadialEnergy_recurrence grade order paid (radialProductConstant lower positive bounded order) ceiling
      (radialProductConstant_nonnegative lower positive bounded order)
      (actualRadialJetEnergy lower positive bounded input.parameter input.source)
      (actualRadialJetEnergy_nonnegative lower positive bounded input.parameter input.source)
      (fun mode => radialWithinEnergy lower order (diskCoreRadialCurve mode input.core)) mode high
      (actualRadial_energy_recurrence lower positive bounded input.parameter ceiling input.parameterBound
        input.source input.core input.same mode high order)
  obtain ⟨constant, nonnegative, bound⟩ := finiteRadialInduction grade energy forcing size
    (fun mode => mode ∉ lowAngularModes) base sourceConstant ceiling (radialProductConstant lower positive bounded)
    (fun input => sq_nonneg _) (add_nonneg (zeroOneCollarConstant_nonnegative grade)
      (weightedSecondRadialConstant_nonnegative lower ceiling grade))
    (mul_nonneg (by positivity) (polarOrderConstant_nonnegative grade))
    (radialProductConstant_nonnegative lower positive bounded) baseBound forcingBound recurrence
  refine ⟨constant, nonnegative, ?_⟩
  intro parameter parameterBound source core same radial upper modes high
  exact bound ⟨parameter, parameterBound, source, core, same⟩ radial upper modes high

end Grad.CircularHighRegularity

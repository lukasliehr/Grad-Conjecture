import ACB12RadialEnergyInduction

noncomputable section
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators Interval
namespace Grad.ActualCenterBounds
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.ActualCenterVolterra Grad.CircularHighWeak
open Grad.CircularHighRegularity

structure NativeCenterDatum (radius : ℝ) where
  mode : ℤ
  center : mode = 1 ∨ mode = -1
  frequency : ℝ
  bounded : |frequency| ≤ radius
  source : ClosedJet 1
  pure : angularClosedJet mode source = source

/-- Every actual center radial derivative through s+2 is paid by the
original Hs norm, starting with the proved H3-to-H1 estimate only when s≥3. -/
theorem actualCenterProfile_allRadial (grade : ℕ) (large : 3 ≤ grade) (radius : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (mode : ℤ), mode = 1 ∨ mode = -1 →
      ∀ (frequency : ℝ), |frequency| ≤ radius → ∀ (source : ClosedJet 1),
      angularClosedJet mode source = source → ∀ order : ℕ, order ≤ grade + 2 →
      radialWithinEnergy (1 / 2) order (pureProfile mode (pinnedCenterSolution mode frequency source)) ≤
        constant * ‖unitDiskCoreInto grade source‖ ^ 2 := by
  let energy (datum : NativeCenterDatum radius) (order : ℕ) :=
    radialWithinEnergy (1 / 2) order (pureProfile datum.mode (pinnedCenterSolution datum.mode datum.frequency datum.source))
  let forcing (datum : NativeCenterDatum radius) (order : ℕ) :=
    radialWithinEnergy (1 / 2) order (pureProfile datum.mode datum.source)
  let size (datum : NativeCenterDatum radius) := ‖unitDiskCoreInto grade datum.source‖ ^ 2
  obtain ⟨constant, nonnegative, estimates⟩ := centerRadialInduction grade energy forcing size
    (centerProfileBaseConstant radius) (profileSourceConstant grade) (3 * radius ^ 2)
    (radialProductConstant (1 / 2) (by norm_num) (by norm_num))
    (fun _ => sq_nonneg _) (centerProfileBaseConstant_nonnegative radius)
    (profileSourceConstant_nonnegative grade)
    (radialProductConstant_nonnegative (1 / 2) (by norm_num) (by norm_num))
    (fun datum order small => pinnedCenterProfile_base_energy grade large radius datum.mode datum.center
      datum.frequency datum.bounded datum.source datum.pure order small)
    (fun datum order paid => pureProfile_energy_source grade order paid datum.source datum.mode)
    (fun datum order _ => pinnedCenterProfile_energy_recurrence radius datum.mode datum.center
      datum.frequency datum.bounded datum.source datum.pure order)
  refine ⟨constant, nonnegative, ?_⟩
  intro mode center frequency bounded source pure order paid
  exact estimates ⟨mode, center, frequency, bounded, source, pure⟩ order paid

def centerAllRadialConstant (grade : ℕ) (large : 3 ≤ grade) (radius : ℝ) : ℝ :=
  (actualCenterProfile_allRadial grade large radius).choose

theorem centerAllRadialConstant_nonnegative (grade : ℕ) (large : 3 ≤ grade) (radius : ℝ) :
    0 ≤ centerAllRadialConstant grade large radius := (actualCenterProfile_allRadial grade large radius).choose_spec.1

theorem pinnedCenterProfile_allRadial (grade : ℕ) (large : 3 ≤ grade) (radius : ℝ)
    (mode : ℤ) (center : mode = 1 ∨ mode = -1) (frequency : ℝ) (bounded : |frequency| ≤ radius)
    (source : ClosedJet 1) (pure : angularClosedJet mode source = source) (order : ℕ) (paid : order ≤ grade + 2) :
    radialWithinEnergy (1 / 2) order (pureProfile mode (pinnedCenterSolution mode frequency source)) ≤
      centerAllRadialConstant grade large radius * ‖unitDiskCoreInto grade source‖ ^ 2 :=
  (actualCenterProfile_allRadial grade large radius).choose_spec.2 mode center frequency bounded source pure order paid

end Grad.ActualCenterBounds

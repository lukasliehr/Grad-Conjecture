import ACB5OriginalFirstGrade

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterBounds
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.ActualCenterVolterra Grad.CircularHighWeak
open Grad.GaugeCoefficients.Physical.RadialLedger (apSupConstant apSupConstant_nonnegative)

def centerFirstSupConstant (radius : ℝ) : ℝ :=
  2 * (centerValueConstant radius + centerGradientConstant radius) * apSupConstant

def centerH1Constant (radius : ℝ) : ℝ := nativeSupFactor 1 * centerFirstSupConstant radius

theorem centerFirstSupConstant_nonnegative (radius : ℝ) : 0 ≤ centerFirstSupConstant radius := by
  have value := centerValueConstant_nonnegative radius
  have gradient := centerGradientConstant_nonnegative radius
  have source := apSupConstant_nonnegative
  unfold centerFirstSupConstant
  positivity

theorem centerH1Constant_nonnegative (radius : ℝ) : 0 ≤ centerH1Constant radius :=
  mul_nonneg (nativeSupFactor_nonnegative 1) (centerFirstSupConstant_nonnegative radius)

theorem center_parameter_bound (radius frequency : ℝ) (bounded : |frequency| ≤ radius) :
    |-3 * frequency ^ 2| ≤ 3 * radius ^ 2 := by
  have square := pow_le_pow_left₀ (abs_nonneg frequency) bounded 2
  rw [sq_abs] at square
  rw [abs_mul, abs_of_nonneg (sq_nonneg frequency)]
  norm_num
  nlinarith

/-- The original H3 source controls all value and first-derivative rows of
the actual pinned center solution uniformly for |k| ≤ K. -/
theorem pinnedCenterSolution_first_sup (radius : ℝ) (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (frequency : ℝ) (bounded : |frequency| ≤ radius) (source : ClosedJet 1)
    (pure : angularClosedJet mode source = source) :
    ‖(pinnedCenterSolution mode frequency source).value‖ ≤ centerFirstSupConstant radius * ‖unitDiskCoreInto 3 source‖ ∧
    ∀ direction : Fin 2, ‖(partialJet direction (pinnedCenterSolution mode frequency source)).value‖ ≤
      centerFirstSupConstant radius * ‖unitDiskCoreInto 3 source‖ := by
  let forcing := -centerQuotientJet mode source
  let amplitude := volterraResolventJet (-3 * frequency ^ 2) forcing
  have sourceBound : ‖forcing.value‖ ≤ apSupConstant * ‖unitDiskCoreInto 3 source‖ := by
    simpa only [forcing, closedJet_value_neg, norm_neg] using sourceCenterQuotient_sup mode center source
  have radial := radial_neg _ (centerQuotient_radial mode center source pure)
  have valueBound : ‖amplitude.value‖ ≤ centerValueConstant radius *
      (apSupConstant * ‖unitDiskCoreInto 3 source‖) :=
    (volterraResolvent_value_norm radius _ (center_parameter_bound radius frequency bounded) forcing).trans
      (mul_le_mul_of_nonneg_left sourceBound (centerValueConstant_nonnegative radius))
  have partialBound (direction : Fin 2) : ‖(partialJet direction amplitude).value‖ ≤
      centerGradientConstant radius * (apSupConstant * ‖unitDiskCoreInto 3 source‖) :=
    (volterraResolvent_partial_norm radius _ (center_parameter_bound radius frequency bounded) forcing radial direction).trans
      (mul_le_mul_of_nonneg_left sourceBound (centerGradientConstant_nonnegative radius))
  constructor
  · apply (signedCoordinate_value_norm mode center amplitude).trans
    calc
      _ ≤ 2 * (centerValueConstant radius * (apSupConstant * ‖unitDiskCoreInto 3 source‖)) :=
        mul_le_mul_of_nonneg_left valueBound (by norm_num)
      _ ≤ 2 * ((centerValueConstant radius + centerGradientConstant radius) *
          (apSupConstant * ‖unitDiskCoreInto 3 source‖)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (centerGradientConstant_nonnegative radius))
          (mul_nonneg apSupConstant_nonnegative (norm_nonneg _))
      _ = _ := by unfold centerFirstSupConstant; ring
  · intro direction
    apply (signedCoordinate_partial_norm mode center direction amplitude).trans
    exact (mul_le_mul_of_nonneg_left (add_le_add valueBound (partialBound direction)) (by norm_num)).trans_eq
      (by unfold centerFirstSupConstant; ring)

/-- AN6b in the original native Sobolev norms, with no frequency division
and with the constant chosen before frequency, sign, and source. -/
theorem pinnedCenterSolution_H1 (radius : ℝ) (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (frequency : ℝ) (bounded : |frequency| ≤ radius) (source : ClosedJet 1)
    (pure : angularClosedJet mode source = source) :
    ‖unitDiskCoreInto 1 (pinnedCenterSolution mode frequency source)‖ ≤
      centerH1Constant radius * ‖unitDiskCoreInto 3 source‖ := by
  have bounds := pinnedCenterSolution_first_sup radius mode center frequency bounded source pure
  exact (nativeFirstGrade_of_sup _ _
    (mul_nonneg (centerFirstSupConstant_nonnegative radius) (norm_nonneg _)) bounds.1 bounds.2).trans_eq
      (mul_assoc _ _ _).symm

theorem actual_center_native_base (radius : ℝ) : ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (mode : ℤ), mode = 1 ∨ mode = -1 → ∀ (frequency : ℝ), |frequency| ≤ radius →
    ∀ (source : ClosedJet 1), angularClosedJet mode source = source →
      ‖unitDiskCoreInto 1 (pinnedCenterSolution mode frequency source)‖ ≤ constant * ‖unitDiskCoreInto 3 source‖ :=
  ⟨centerH1Constant radius, centerH1Constant_nonnegative radius, pinnedCenterSolution_H1 radius⟩

end Grad.ActualCenterBounds

import ANG22HigherModeEstimates

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace Grad.CircularHighWeak
open Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- Repeated genuine weak Cartesian rotation, with every intermediate
representative in the actual high H1 completion. -/
def HasRepeatedDerivative {E : Type*} (step : E → E → Prop) : ℕ → E → E → Prop
  | 0, field, derivative => derivative = field
  | order + 1, field, derivative => ∃ previous,
      HasRepeatedDerivative step order field previous ∧ step previous derivative

abbrev HasH1AngularPower := HasRepeatedDerivative
  (fun previous derivative : highDiskGrade => highDiskBulk derivative = highRotation previous)

def completedAngularTower (parameter : ℝ) (level : ℕ) (source : apGrade 1 0 0 1 1 level) : ℕ → highDiskGrade
  | 0 => highRobinWeakInverse parameter (sourceHighBulk level source)
  | order + 1 => if ordered : order ≤ level then
      angularWeakSolutionPower parameter order (apLowering 1 0 0 1 ordered source) else 0

theorem completedAngularTower_succ (parameter : ℝ) (level : ℕ) (source : apGrade 1 0 0 1 1 level)
    (order : ℕ) (ordered : order ≤ level) :
    completedAngularTower parameter level source (order + 1) =
      angularWeakSolutionPower parameter order (apLowering 1 0 0 1 ordered source) := dif_pos ordered

theorem completedAngularTower_mode (parameter : ℝ) (level : ℕ) (source : apGrade 1 0 0 1 1 level)
    (order : ℕ) (ordered : order ≤ level + 1) (mode : ℤ) :
    highDiskMode mode (completedAngularTower parameter level source order) =
      (Complex.I * (mode : ℂ)) ^ order • highDiskMode mode
        (highRobinWeakInverse parameter (sourceHighBulk level source)) := by
  cases order with
  | zero => exact (one_smul ℂ _).symm
  | succ order =>
    have lower : order ≤ level := by omega
    exact (congrArg (highDiskMode mode) (completedAngularTower_succ parameter level source order lower)).trans
      ((angularWeakSolutionPower_mode parameter order (apLowering 1 0 0 1 lower source) mode).trans
        (congrArg (fun value : highDiskL2 => (Complex.I * (mode : ℂ)) ^ (order + 1) •
          highDiskMode mode (highRobinWeakInverse parameter value)) (sourceHighBulk_lowering lower source)))

theorem completedAngularTower_bulk_mode (parameter : ℝ) (level : ℕ) (source : apGrade 1 0 0 1 1 level)
    (order : ℕ) (ordered : order ≤ level + 1) (mode : ℤ) :
    diskMode mode (highDiskBulk (completedAngularTower parameter level source order)) =
      (Complex.I * (mode : ℂ)) ^ order • diskMode mode
        (highDiskBulk (highRobinWeakInverse parameter (sourceHighBulk level source))) := by
  have projected := (highDiskMode_bulk mode (completedAngularTower parameter level source order)).symm.trans
    ((congrArg highDiskBulk (completedAngularTower_mode parameter level source order ordered mode)).trans
      (highDiskBulk.map_smul ((Complex.I * (mode : ℂ)) ^ order)
        (highDiskMode mode (highRobinWeakInverse parameter (sourceHighBulk level source)))))
  exact projected.trans (congrArg (fun value : DiskL2 1 => (Complex.I * (mode : ℂ)) ^ order • value)
    (highDiskMode_bulk mode (highRobinWeakInverse parameter (sourceHighBulk level source))))

/-- Every adjacent pair in the constructed tower satisfies the genuine
weak rotation law, through the faithful actual disk L2 realization. -/
theorem completedAngularTower_step (parameter : ℝ) (level : ℕ) (source : apGrade 1 0 0 1 1 level)
    (order : ℕ) (ordered : order ≤ level) :
    highDiskBulk (completedAngularTower parameter level source (order + 1)) =
      highRotation (completedAngularTower parameter level source order) := by
  apply diskFourierIsometry.injective
  apply lp.ext
  funext mode
  change diskMode mode (highDiskBulk (completedAngularTower parameter level source (order + 1))) =
    diskMode mode (highRotation (completedAngularTower parameter level source order))
  have left := completedAngularTower_bulk_mode parameter level source (order + 1) (by omega) mode
  have right := (highRotation_coefficient mode (completedAngularTower parameter level source order)).trans
    ((congrArg (fun value : DiskL2 1 => (Complex.I * (mode : ℂ)) • value)
      (completedAngularTower_bulk_mode parameter level source order (by omega) mode)).trans
      ((smul_smul _ _ _).trans (congrArg (fun scalar : ℂ => scalar • diskMode mode
        (highDiskBulk (highRobinWeakInverse parameter (sourceHighBulk level source)))) (pow_succ' _ order).symm)))
  exact left.trans right.symm

theorem completedAngularTower_hasPower (parameter : ℝ) (level : ℕ) (source : apGrade 1 0 0 1 1 level)
    (order : ℕ) (ordered : order ≤ level + 1) :
    HasH1AngularPower order (highRobinWeakInverse parameter (sourceHighBulk level source))
      (completedAngularTower parameter level source order) := by
  induction order with
  | zero => rfl
  | succ order previous =>
    exact ⟨completedAngularTower parameter level source order, previous (by omega),
      completedAngularTower_step parameter level source order (by omega)⟩

private theorem unitLowering_refl (grade : ℕ) (field : apGrade 1 0 0 1 1 grade) :
    apLowering 1 0 0 1 (le_refl grade) field = field := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := 1) (grade := grade) 1 0 0 1)
    (isClosed_eq (apLowering 1 0 0 1 (le_refl grade)).continuous continuous_id) _ field
  intro core
  exact apLowering_core 1 0 0 1 (le_refl grade) core

/-- AN20 at every positive order: the constructed output is the actual
repeated weak rotation, bounded using precisely source grade a−1. -/
theorem actualAngularRegularity (parameter : ℝ) (order : ℕ) (source : apGrade 1 0 0 1 1 order) :
    HasH1AngularPower (order + 1) (highRobinWeakInverse parameter (sourceHighBulk order source))
      (angularWeakSolutionPower parameter order source) ∧
    ‖angularWeakSolutionPower parameter order source‖ ≤ (2 * unitRotationPowerConstant order) * ‖source‖ := by
  have highest := (completedAngularTower_succ parameter order source order (le_refl order)).trans
    (congrArg (angularWeakSolutionPower parameter order) (unitLowering_refl order source))
  have statement := completedAngularTower_hasPower parameter order source (order + 1) (le_refl _)
  have transfer := congrArg (fun derivative : highDiskGrade => HasH1AngularPower (order + 1)
    (highRobinWeakInverse parameter (sourceHighBulk order source)) derivative) highest
  exact ⟨transfer.mp statement, angularWeakSolutionPower_bound parameter order source⟩

end Grad.CircularHighWeak

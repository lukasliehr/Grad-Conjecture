import AKDW23ActualAffineTensorLowerGraphs
import AKDW21SamePhaseAffineSplit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.NonlinearProduct
open Grad.OriginalCoreRealization Grad.OriginalCartesianTameEstimate Grad.CellWeights

/-- One independent unknown base, its single coefficient budget, and a
separate genuine source payment, at the unchanged original width. -/
def startupOriginalRemainderPayment {State : Type*} (parameters : PhaseParameters) {length radius : ℝ}
    (grade : ℕ) (coefficient : State → OriginalUnitRankState parameters length radius)
    (cores : State → ACore parameters 3) (payment : State → ℝ) (state : State) : ℝ :=
  originalCellNorm parameters grade (cores state)+OriginalUnitRankState.budget grade (coefficient state)*originalGradeNorm 0 (cores state)+payment state

theorem startupOriginalRemainderPayment_source {State : Type*} (parameters : PhaseParameters) {length radius : ℝ}
    (grade : ℕ) (coefficient : State → OriginalUnitRankState parameters length radius)
    (cores : State → ACore parameters 3) (payment : State → ℝ) (state : State) :
    payment state≤startupOriginalRemainderPayment parameters grade coefficient cores payment state := by
  exact le_add_of_nonneg_left (add_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg (OriginalUnitRankState.budget_nonnegative grade (coefficient state)) (originalGradeNorm_nonnegative 0 (cores state))))

theorem startupOriginalRemainderPayment_unknown {State : Type*} (parameters : PhaseParameters) {length radius : ℝ}
    (grade : ℕ) (coefficient : State → OriginalUnitRankState parameters length radius)
    (cores : State → ACore parameters 3) (payment : State → ℝ) (nonnegative : ∀ state,0≤payment state) (state : State) :
    originalCellNorm parameters grade (cores state)+OriginalUnitRankState.budget grade (coefficient state)*originalGradeNorm 0 (cores state)≤
      startupOriginalRemainderPayment parameters grade coefficient cores payment state :=
  le_add_of_nonneg_right (nonnegative state)

def startupOriginalFirstNaturalMoment (parameters : PhaseParameters) (core : ACore parameters 3) : StartupL2 3 :=
  (startupOriginalSignedFamily parameters core 1 1).naturalMoment one_ne_zero one_ne_zero 0 1

theorem startupOriginalFirstNaturalMoment_same (parameters : PhaseParameters) (core : ACore parameters 3) :
    StartupRadialRelated (fun cell _ => cellWeight cell) (startupOriginalFirstNaturalMoment parameters core)
      (originalSourceFieldLinear parameters core) := by
  have same := (startupOriginalSignedFamily parameters core 1 1).naturalMoment_same one_ne_zero one_ne_zero 0 1
  simp only [pow_one,StartupSignedFamily.zero] at same
  change StartupRadialRelated (fun cell _ => cellWeight cell)
    ((startupOriginalSignedFamily parameters core 1 1).naturalMoment one_ne_zero one_ne_zero 0 1)
    (startupOriginalSignedFamily parameters core 1 1).field
  exact same

end Grad.CartesianStartup

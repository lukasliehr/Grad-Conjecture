import AKDA10OriginalGammaInverseEuler
import AHP27RadialGaugePhysicalMoments

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.AnnularRadialSmoothness
open Grad.GaugeCoefficients.Physical.Allocation

def gammaEulerMomentConstant (parameters : PhaseParameters) (L compact : ℝ) (rank moment : ℕ) : ℝ :=
  Nat.casesOn rank (gammaJetMomentConstant parameters L compact 0 moment)
    (fun order => rawEulerMomentConstant (fun raw => gammaJetMomentConstant parameters L compact raw moment) (positiveEulerTerms order))

theorem gammaEulerMomentConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) (rank moment : ℕ) :
    0 ≤ gammaEulerMomentConstant parameters L compact rank moment := by
  cases rank with
  | zero => exact gammaJetMomentConstant_nonnegative parameters L compact 0 moment
  | succ rank => exact rawEulerMomentConstant_nonnegative _ (fun raw => gammaJetMomentConstant_nonnegative parameters L compact raw moment) _

theorem originalNegativeGammaEulerKernel_moment (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact) (radius : RadialPoint) (rank moment : ℕ) :
    fullKernelMoment (radialKernelParameters parameters radius) moment
      (actualRawEulerKernel radius (fun raw => fullKernelNeg (gammaJetKernel parameters L compact state raw radius)) rank) ≤
      gammaEulerMomentConstant parameters L compact rank moment *
        physicalBudget parameters state.data.field state.data.rho state.data.epsilon (moment+rank+5) := by
  cases rank with
  | zero => exact (fullKernelNeg_moment_le _ moment _).trans (gammaJetKernel_moment_le parameters L compact state 0 radius moment)
  | succ rank =>
      change fullKernelMoment (radialKernelParameters parameters radius) moment
        (rawEulerKernel radius (fun raw => fullKernelNeg (gammaJetKernel parameters L compact state raw radius)) (positiveEulerTerms rank)) ≤
          rawEulerMomentConstant (fun raw => gammaJetMomentConstant parameters L compact raw moment) (positiveEulerTerms rank) *
            physicalBudget parameters state.data.field state.data.rho state.data.epsilon (moment+(rank+1)+5)
      apply rawEulerKernel_moment_bound
      intro term member
      have paid := (fullKernelNeg_moment_le _ moment _).trans
        (gammaJetKernel_moment_le parameters L compact state (term.1+1) radius moment)
      exact paid.trans (mul_le_mul_of_nonneg_left
        (physicalBudget_monotone parameters state.data.field state.data.rho state.data.epsilon
          (by have allocated := positiveEulerTerms_rank rank term member; omega))
        (gammaJetMomentConstant_nonnegative parameters L compact (term.1+1) moment))

def gammaInverseBaseMomentConstant (parameters : PhaseParameters) (L compact : ℝ) (moment : ℕ) : ℝ :=
  Classical.choose (radialNegativeGammaInverseKernel_physicalMoments parameters L compact moment)

theorem gammaInverseBaseMomentConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) (moment : ℕ) :
    0 ≤ gammaInverseBaseMomentConstant parameters L compact moment :=
  (Classical.choose_spec (radialNegativeGammaInverseKernel_physicalMoments parameters L compact moment)).1

theorem gammaInverseBaseMomentConstant_bound (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) (radius : RadialPoint) (moment : ℕ) :
    fullKernelMoment (radialKernelParameters parameters radius) moment
      (radialNegativeGammaInverseKernel parameters L compact state.val radius state.gaugeSmall) ≤
      gammaInverseBaseMomentConstant parameters L compact moment *
        (1+physicalBudget parameters state.val.field state.val.rho state.val.epsilon (7+moment)) := by
  have bounded := (Classical.choose_spec (radialNegativeGammaInverseKernel_physicalMoments parameters L compact moment)).2 state radius
  simpa only [gammaInverseBaseMomentConstant,BoundaryReconstructionState.size,Nat.add_comm] using bounded

def gammaInverseEulerMomentConstant (parameters : PhaseParameters) (L compact : ℝ) (rank moment : ℕ) : ℝ :=
  inverseExpressionMomentConstant 7 (gammaInverseBaseMomentConstant parameters L compact)
    (gammaEulerMomentConstant parameters L compact) (inverseEulerExpression rank) moment

theorem gammaInverseEulerMomentConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) (rank moment : ℕ) :
    0 ≤ gammaInverseEulerMomentConstant parameters L compact rank moment :=
  inverseExpressionMomentConstant_nonnegative 7 _ _
    (gammaInverseBaseMomentConstant_nonnegative parameters L compact)
    (gammaEulerMomentConstant_nonnegative parameters L compact) _ _

/-- The actual original gauge inverse spends the sum of the Euler rank
and displacement moment once. Every ordered inverse factor is retained;
the full phase and the original width remain in fullKernelMoment. -/
theorem originalGammaInverseEulerKernel_oneHigh (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact)
    (low : physicalBudget parameters state.val.field state.val.rho state.val.epsilon 7 ≤ 1)
    (radius : RadialPoint) (rank moment : ℕ) :
    fullKernelMoment (radialKernelParameters parameters radius) moment
      (originalGammaInverseEulerKernel parameters L compact state.val state.gaugeSmall radius rank) ≤
      gammaInverseEulerMomentConstant parameters L compact rank moment *
        (1+physicalBudget parameters state.val.field state.val.rho state.val.epsilon (7+(rank+moment))) := by
  apply inverseEulerWords_oneHigh parameters state.val.field state.val.rho state.val.epsilon radius 7 low
    (radialNegativeGammaInverseKernel parameters L compact state.val radius state.gaugeSmall)
    (actualRawEulerKernel radius (fun raw => fullKernelNeg (gammaJetKernel parameters L compact state.val raw radius)))
    (gammaInverseBaseMomentConstant parameters L compact) (gammaEulerMomentConstant parameters L compact)
    (gammaInverseBaseMomentConstant_nonnegative parameters L compact)
    (gammaEulerMomentConstant_nonnegative parameters L compact)
    (gammaInverseBaseMomentConstant_bound parameters L compact state radius)
  intro raw moment
  apply (originalNegativeGammaEulerKernel_moment parameters L compact state.val radius raw moment).trans
  apply mul_le_mul_of_nonneg_left _ (gammaEulerMomentConstant_nonnegative parameters L compact raw moment)
  exact (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon
    (show moment+raw+5 ≤ 7+(raw+moment) by omega)).trans (by linarith)

end Grad.OriginalCartesianTameEstimate

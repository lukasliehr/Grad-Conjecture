import AKDD11ActualEulerFamilyAssembly
import AJH13ActualSigmaRadialJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.AnnularRadialSmoothness Grad.AnnularKernelContinuity
open Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.GaugeCoefficients.Physical.Allocation

theorem actualRotatedForceEuler_derivativeTower (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact) (kind : Fin 2)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    KernelEulerDerivativeTower parameters lower positive bounded.le
      (fun rank radius => actualRawEulerKernel radius (fun raw => radialRotatedForceKernel parameters L compact state radius kind raw) rank) := by
  apply actualRawEulerKernel_derivativeTower
  intro raw radius inside
  apply actualMatrixKernelAction_hasDerivWithinAt parameters lower positive bounded
    (fun raw radius => radialRotatedForceKernel parameters L compact state radius kind raw)
    (fun raw point shift => rowMultiplicationEntry 3
      (fun component => angularCoefficientSequence (forceScalar parameters L state.data.rho state.data.epsilon state.data.field kind state.low component raw point)) shift (0,0))
    (fun _ _ _ _ => rfl) _ (radialRotatedForceKernel_regular parameters L compact state kind) raw radius inside
  intro order shift radius
  exact rowMultiplicationEntry_hasDerivAt 3 _ _
    (fun component point mode => (actualForceScalar_hasDerivAt parameters L compact state kind component order point mode).const_mul _) radius shift (0,0)

theorem actualRotatedSigmaEuler_derivativeTower (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    KernelEulerDerivativeTower parameters lower positive bounded.le
      (fun rank radius => actualRawEulerKernel radius (fun raw => radialRotatedSigmaKernel parameters L compact state radius raw) rank) := by
  apply actualRawEulerKernel_derivativeTower
  intro raw radius inside
  apply actualMatrixKernelAction_hasDerivWithinAt parameters lower positive bounded
    (fun raw radius => radialRotatedSigmaKernel parameters L compact state radius raw)
    (fun raw point shift => rowMultiplicationEntry 3
      (fun component => angularCoefficientSequence (sigmaScalar parameters L state.data.rho state.data.epsilon state.data.field state.low component raw point)) shift (0,0))
    (fun _ _ _ _ => rfl) _ (rotatedSigmaJet_regular parameters L compact state) raw radius inside
  intro order shift radius
  exact rowMultiplicationEntry_hasDerivAt 3 _ _
    (fun component point mode => (sigmaScalar_hasDerivAt parameters L state.data.rho state.data.epsilon state.data.field state.low component order point mode).const_mul _) radius shift (0,0)

/-- Ordinary primitive jets spend their exact radial rank once when
converted into Euler monomials. -/
theorem rawEulerKernel_originalMoments {parameters : PhaseParameters} {L compact : ℝ} {source target : ℕ}
    (kernels : (state : AnnularReconstructionState parameters L compact) → ℕ →
      (radius : RadialPoint) → RadialKernel parameters radius source target)
    (cost : ℕ) (costBound : cost ≤ 10) (constants : ℕ → ℕ → ℝ)
    (nonnegative : ∀ raw moment, 0 ≤ constants raw moment)
    (bounds : ∀ state raw moment radius,
      fullKernelMoment (radialKernelParameters parameters radius) moment (kernels state raw radius) ≤
        constants raw moment * physicalBudget parameters state.val.field state.val.rho state.val.epsilon (moment+raw+cost)) :
    OriginalEulerMoments parameters L compact
      (fun state rank radius => actualRawEulerKernel radius (fun raw => kernels state raw radius) rank) := by
  intro rank moment
  cases rank with
  | zero =>
      refine ⟨constants 0 moment,nonnegative 0 moment,?_⟩
      intro state _ radius
      apply (bounds state 0 moment radius).trans
      apply mul_le_mul_of_nonneg_left _ (nonnegative 0 moment)
      exact (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon (by omega : moment+0+cost ≤ 10+(0+moment))).trans (by linarith)
  | succ rank =>
      refine ⟨rawEulerMomentConstant (fun raw => constants raw moment) (positiveEulerTerms rank),
        rawEulerMomentConstant_nonnegative _ (fun raw => nonnegative raw moment) _,?_⟩
      intro state _ radius
      apply rawEulerKernel_moment_bound
      intro term member
      have degree := positiveEulerTerms_rank rank term member
      apply (bounds state (term.1+1) moment radius).trans
      apply mul_le_mul_of_nonneg_left _ (nonnegative (term.1+1) moment)
      exact (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon
        (by omega : moment+(term.1+1)+cost ≤ 10+((rank+1)+moment))).trans (by linarith)

def originalRotatedForceEulerFamily (parameters : PhaseParameters) (L compact : ℝ) (kind : Fin 2) :
    ActualEulerFamily parameters L compact (fun state radius => radialRotatedForceKernel parameters L compact state.val radius kind 0) where
  kernels state rank radius := actualRawEulerKernel radius (fun raw => radialRotatedForceKernel parameters L compact state.val radius kind raw) rank
  zero _ _ := rfl
  derivative state lower positive bounded := actualRotatedForceEuler_derivativeTower parameters L compact state.val kind lower positive bounded
  moments := rawEulerKernel_originalMoments _ 7 (by omega)
    (fun raw moment => actualForceRawMomentConstant parameters L kind (moment+1) raw)
    (fun raw moment => actualForceRawMomentConstant_nonnegative parameters L kind (moment+1) raw)
    (fun state raw moment radius => by
      have bound := radialRotatedForceKernel_moment_le parameters L compact state.val radius kind raw moment
      exact bound)

def originalRotatedSigmaEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :
    ActualEulerFamily parameters L compact (fun state radius => radialRotatedSigmaKernel parameters L compact state.val radius 0) where
  kernels state rank radius := actualRawEulerKernel radius (fun raw => radialRotatedSigmaKernel parameters L compact state.val radius raw) rank
  zero _ _ := rfl
  derivative state lower positive bounded := actualRotatedSigmaEuler_derivativeTower parameters L compact state.val lower positive bounded
  moments := rawEulerKernel_originalMoments _ 6 (by omega)
    (fun raw moment => actualSigmaRawMomentConstant parameters L (moment+1) raw)
    (fun raw moment => actualSigmaRawMomentConstant_nonnegative parameters L (moment+1) raw)
    (fun state raw moment radius => rotatedSigmaJet_moment_le parameters L compact state.val raw radius moment)

end Grad.OriginalCartesianTameEstimate

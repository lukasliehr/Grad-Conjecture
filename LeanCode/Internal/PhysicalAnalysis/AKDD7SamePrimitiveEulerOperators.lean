import AKDD6FixedAndAdditiveEulerClosure

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.AnnularRadialSmoothness Grad.AnnularKernelContinuity

theorem actualGaugeEulerKernel_derivativeTower (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    KernelEulerDerivativeTower parameters lower positive bounded.le
      (fun rank radius => actualGaugeEulerKernel parameters L compact state radius rank) := by
  have same : (fun rank radius => actualGaugeEulerKernel parameters L compact state radius rank) =
      (fun rank radius => actualRawEulerKernel radius (fun raw => radialGaugeRowsKernel parameters L compact state radius raw) rank) := by
    funext rank radius
    cases rank <;> rfl
  rw [same]
  apply actualRawEulerKernel_derivativeTower parameters lower positive bounded.le
    (fun raw radius => radialGaugeRowsKernel parameters L compact state radius raw)
  intro raw radius inside
  exact actualMatrixKernelAction_hasDerivWithinAt parameters lower positive bounded
    (fun raw radius => radialGaugeRowsKernel parameters L compact state radius raw)
    (fun raw point shift => actualGaugeMatrixJets parameters L compact state raw point shift (0,0))
    (fun _ _ _ _ => rfl)
    (fun raw shift point => actualGaugeMatrixJets_derivative parameters L compact state raw point shift (0,0))
    (radialGaugeRowsKernel_regular parameters L compact state) raw radius inside

theorem actualForceEulerKernel_derivativeTower (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact) (kind : Fin 2)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    KernelEulerDerivativeTower parameters lower positive bounded.le
      (fun rank radius => actualForceEulerKernel parameters L compact state kind radius rank) := by
  have same : (fun rank radius => actualForceEulerKernel parameters L compact state kind radius rank) =
      (fun rank radius => actualRawEulerKernel radius (fun raw => radialForceKernel parameters L compact state radius kind raw) rank) := by
    funext rank radius
    cases rank <;> rfl
  rw [same]
  apply actualRawEulerKernel_derivativeTower parameters lower positive bounded.le
    (fun raw radius => radialForceKernel parameters L compact state radius kind raw)
  intro raw radius inside
  exact actualMatrixKernelAction_hasDerivWithinAt parameters lower positive bounded
    (fun raw radius => radialForceKernel parameters L compact state radius kind raw)
    (fun raw point shift => actualForceMatrixJets parameters L compact state kind raw point shift (0,0))
    (fun _ _ _ _ => rfl)
    (fun raw shift point => actualForceMatrixJets_derivative parameters L compact state kind raw point shift (0,0))
    (radialForceKernel_regular parameters L compact state kind) raw radius inside

theorem actualSigmaEulerKernel_derivativeTower (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    KernelEulerDerivativeTower parameters lower positive bounded.le
      (fun rank radius => actualSigmaEulerKernel parameters L compact state radius rank) := by
  have same : (fun rank radius => actualSigmaEulerKernel parameters L compact state radius rank) =
      (fun rank radius => actualRawEulerKernel radius (fun raw => radialSigmaKernel parameters L compact state radius raw) rank) := by
    funext rank radius
    cases rank <;> rfl
  rw [same]
  apply actualRawEulerKernel_derivativeTower parameters lower positive bounded.le
    (fun raw radius => radialSigmaKernel parameters L compact state radius raw)
  intro raw radius inside
  exact actualMatrixKernelAction_hasDerivWithinAt parameters lower positive bounded
    (fun raw radius => radialSigmaKernel parameters L compact state radius raw)
    (fun raw point shift => actualSigmaMatrixJets parameters L compact state raw point shift (0,0))
    (fun _ _ _ _ => rfl)
    (fun raw shift point => actualSigmaMatrixJets_derivative parameters L compact state raw point shift (0,0))
    (radialSigmaKernel_regular parameters L compact state) raw radius inside

theorem originalGammaInverseEulerKernel_operatorTower (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact)
    (small : Grad.GaugeCoefficients.Physical.Allocation.physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
      radialGaugeLowRadius parameters L compact)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    KernelEulerDerivativeTower parameters lower positive bounded.le
      (fun rank radius => originalGammaInverseEulerKernel parameters L compact state small radius rank) := by
  have primitive := actualRawEulerKernel_derivativeTower parameters lower positive bounded.le
    (fun raw radius => fullKernelNeg (gammaJetKernel parameters L compact state raw radius))
    (originalNegativeGammaOperator_hasDerivWithinAt parameters L compact state lower positive bounded)
  exact KernelEulerDerivativeTower.negativeInverse parameters lower positive bounded.le
    (fun rank radius => actualRawEulerKernel radius (fun raw => fullKernelNeg (gammaJetKernel parameters L compact state raw radius)) rank)
    primitive (radialGammaDeviationKernel_smooth parameters L compact state lower positive bounded).neg
    (1/2) (by norm_num) (fun radius => radialGammaDeviationKernel_small parameters L compact state radius small)

end Grad.OriginalCartesianTameEstimate

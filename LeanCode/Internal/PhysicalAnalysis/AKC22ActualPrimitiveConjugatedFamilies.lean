import AKC20ActualJetAndFixedFamilies

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Set
open scoped BigOperators ContDiff
namespace Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularKernelContinuity
open Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularRadialSmoothness

variable (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)

theorem radialForceKernel_conjugated_smooth (kind : Fin 2) (order : ℕ) :
    SmoothConjugatedFamily (source := 3) (target := 1) parameters lower positive bounded.le
      (fun radius => radialForceKernel parameters L compact state radius kind order) := by
  apply smoothConjugatedFamily_matrixJets parameters lower positive bounded
    (fun order radius => radialForceKernel parameters L compact state radius kind order)
    (fun order radius shift => rowMultiplicationEntry 3
      (fun component => forceScalar parameters L state.data.rho state.data.epsilon state.data.field kind state.low component order radius) shift (0,0))
    (fun _ _ _ _ => rfl) _ (radialForceKernel_regular parameters L compact state kind) order
  intro order shift radius
  exact rowMultiplicationEntry_hasDerivAt 3 _ _
    (fun component point mode => actualForceScalar_hasDerivAt parameters L compact state kind component order point mode) radius shift (0,0)

theorem radialGaugeRowsKernel_conjugated_smooth (order : ℕ) :
    SmoothConjugatedFamily (source := 3) (target := 2) parameters lower positive bounded.le
      (fun radius => radialGaugeRowsKernel parameters L compact state radius order) := by
  apply smoothConjugatedFamily_matrixJets parameters lower positive bounded
    (fun order radius => radialGaugeRowsKernel parameters L compact state radius order)
    (fun order radius shift => matrixMultiplicationEntry 3 2
      (fun row column => gaugeScalar parameters L state.data.rho state.data.alpha state.data.delta
        state.data.parameter state.data.epsilon state.data.field state.low row column order radius) shift (0,0))
    (fun _ _ _ _ => rfl) _ (radialGaugeRowsKernel_regular parameters L compact state) order
  intro order shift radius
  exact matrixMultiplicationEntry_hasDerivAt 3 2 _ _
    (fun row column point mode => gaugeScalar_hasDerivAt parameters L state.data.rho state.data.alpha state.data.delta
      state.data.parameter state.data.epsilon state.data.field state.low row column order point mode) radius shift (0,0)

theorem radialSigmaKernel_conjugated_smooth (order : ℕ) :
    SmoothConjugatedFamily (source := 3) (target := 1) parameters lower positive bounded.le
      (fun radius => radialSigmaKernel parameters L compact state radius order) := by
  apply smoothConjugatedFamily_matrixJets parameters lower positive bounded
    (fun order radius => radialSigmaKernel parameters L compact state radius order)
    (fun order radius shift => rowMultiplicationEntry 3
      (fun component => sigmaScalar parameters L state.data.rho state.data.epsilon state.data.field state.low component order radius) shift (0,0))
    (fun _ _ _ _ => rfl) _ (radialSigmaKernel_regular parameters L compact state) order
  intro order shift radius
  exact rowMultiplicationEntry_hasDerivAt 3 _ _
    (fun component point mode => sigmaScalar_hasDerivAt parameters L state.data.rho state.data.epsilon
      state.data.field state.low component order point mode) radius shift (0,0)

theorem radialRotatedForceKernel_conjugated_smooth (kind : Fin 2) (order : ℕ) :
    SmoothConjugatedFamily (source := 3) (target := 1) parameters lower positive bounded.le
      (fun radius => radialRotatedForceKernel parameters L compact state radius kind order) := by
  apply smoothConjugatedFamily_matrixJets parameters lower positive bounded
    (fun order radius => radialRotatedForceKernel parameters L compact state radius kind order)
    (fun order radius shift => rowMultiplicationEntry 3
      (fun component => angularCoefficientSequence (forceScalar parameters L state.data.rho state.data.epsilon state.data.field kind state.low component order radius)) shift (0,0))
    (fun _ _ _ _ => rfl) _ (radialRotatedForceKernel_regular parameters L compact state kind) order
  intro order shift radius
  exact rowMultiplicationEntry_hasDerivAt 3 _ _
    (fun component point mode => (actualForceScalar_hasDerivAt parameters L compact state kind component order point mode).const_mul _) radius shift (0,0)


omit lower positive bounded in
theorem radialGammaDeviationKernel_conjugated_smooth (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    SmoothConjugatedFamily (source := 2) (target := 2) parameters lower positive bounded.le
      (fun radius => radialGammaDeviationKernel parameters L compact state radius) := by
  change SmoothConjugatedFamily parameters lower positive bounded.le (gammaJetKernel parameters L compact state 0)
  apply smoothConjugatedFamily_matrixJets parameters lower positive bounded
    (gammaJetKernel parameters L compact state)
    (fun order radius shift => matrixMultiplicationEntry 2 2
      (fun row column mode => if mode.1 = 0 then gaugeScalar parameters L state.data.rho state.data.alpha state.data.delta
        state.data.parameter state.data.epsilon state.data.field state.low row column.succ order radius mode else 0) shift (0,0))
    (fun _ _ _ _ => rfl) _ (gammaJetKernel_regular parameters L compact state) 0
  intro order shift radius
  exact matrixMultiplicationEntry_hasDerivAt 2 2
    (fun row column point mode => if mode.1 = 0 then gaugeScalar parameters L state.data.rho state.data.alpha state.data.delta
      state.data.parameter state.data.epsilon state.data.field state.low row column.succ order point mode else 0)
    (fun row column point mode => if mode.1 = 0 then gaugeScalar parameters L state.data.rho state.data.alpha state.data.delta
      state.data.parameter state.data.epsilon state.data.field state.low row column.succ (order + 1) point mode else 0)
    (fun row column point mode => by
      by_cases zero : mode.1 = 0
      · simp only [if_pos zero]
        exact gaugeScalar_hasDerivAt parameters L state.data.rho state.data.alpha state.data.delta
          state.data.parameter state.data.epsilon state.data.field state.low row column.succ order point mode
      · simp only [if_neg zero]
        exact hasDerivAt_const point 0) radius shift (0,0)


end Grad.AnnularWeightedSmoothness

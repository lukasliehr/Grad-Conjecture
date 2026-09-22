import AJH9ActualRadialMatrixJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
open scoped BigOperators ContDiff
namespace Grad.AnnularRadialSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularKernelContinuity
open Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)

theorem actualForceScalar_hasDerivAt (kind : Fin 2) (component : Fin 3)
    (order : ℕ) (radius : ℝ) (shift : ℤ × ℤ) :
    HasDerivAt (fun point => forceScalar parameters L state.data.rho state.data.epsilon
      state.data.field kind state.low component order point shift)
      (forceScalar parameters L state.data.rho state.data.epsilon
        state.data.field kind state.low component (order + 1) radius shift) radius := by
  exact ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt radius
    (forceFourier_hasDerivAt parameters L state.data.rho state.data.epsilon state.data.field kind state.low component shift order radius)

theorem radialForceKernel_smooth (kind : Fin 2) (order : ℕ) :
    SmoothPolynomialFamily (source := 3) (target := 1) parameters lower positive bounded.le
      (fun radius => radialForceKernel parameters L compact state radius kind order) := by
  apply smoothPolynomialFamily_matrixJets parameters lower positive bounded
    (fun order radius => radialForceKernel parameters L compact state radius kind order)
    (fun order radius shift => rowMultiplicationEntry 3
      (fun component => forceScalar parameters L state.data.rho state.data.epsilon state.data.field kind state.low component order radius) shift (0,0))
    (fun _ _ _ _ => rfl) _ (radialForceKernel_regular parameters L compact state kind) order
  intro order shift radius
  exact rowMultiplicationEntry_hasDerivAt 3 _ _
    (fun component point mode => actualForceScalar_hasDerivAt parameters L compact state kind component order point mode) radius shift (0,0)

theorem radialGaugeRowsKernel_smooth (order : ℕ) :
    SmoothPolynomialFamily (source := 3) (target := 2) parameters lower positive bounded.le
      (fun radius => radialGaugeRowsKernel parameters L compact state radius order) := by
  apply smoothPolynomialFamily_matrixJets parameters lower positive bounded
    (fun order radius => radialGaugeRowsKernel parameters L compact state radius order)
    (fun order radius shift => matrixMultiplicationEntry 3 2
      (fun row column => gaugeScalar parameters L state.data.rho state.data.alpha state.data.delta
        state.data.parameter state.data.epsilon state.data.field state.low row column order radius) shift (0,0))
    (fun _ _ _ _ => rfl) _ (radialGaugeRowsKernel_regular parameters L compact state) order
  intro order shift radius
  exact matrixMultiplicationEntry_hasDerivAt 3 2 _ _
    (fun row column point mode => gaugeScalar_hasDerivAt parameters L state.data.rho state.data.alpha state.data.delta
      state.data.parameter state.data.epsilon state.data.field state.low row column order point mode) radius shift (0,0)

theorem radialSigmaKernel_smooth (order : ℕ) :
    SmoothPolynomialFamily (source := 3) (target := 1) parameters lower positive bounded.le
      (fun radius => radialSigmaKernel parameters L compact state radius order) := by
  apply smoothPolynomialFamily_matrixJets parameters lower positive bounded
    (fun order radius => radialSigmaKernel parameters L compact state radius order)
    (fun order radius shift => rowMultiplicationEntry 3
      (fun component => sigmaScalar parameters L state.data.rho state.data.epsilon state.data.field state.low component order radius) shift (0,0))
    (fun _ _ _ _ => rfl) _ (radialSigmaKernel_regular parameters L compact state) order
  intro order shift radius
  exact rowMultiplicationEntry_hasDerivAt 3 _ _
    (fun component point mode => sigmaScalar_hasDerivAt parameters L state.data.rho state.data.epsilon
      state.data.field state.low component order point mode) radius shift (0,0)

theorem radialRotatedForceKernel_smooth (kind : Fin 2) (order : ℕ) :
    SmoothPolynomialFamily (source := 3) (target := 1) parameters lower positive bounded.le
      (fun radius => radialRotatedForceKernel parameters L compact state radius kind order) := by
  apply smoothPolynomialFamily_matrixJets parameters lower positive bounded
    (fun order radius => radialRotatedForceKernel parameters L compact state radius kind order)
    (fun order radius shift => rowMultiplicationEntry 3
      (fun component => angularCoefficientSequence (forceScalar parameters L state.data.rho state.data.epsilon state.data.field kind state.low component order radius)) shift (0,0))
    (fun _ _ _ _ => rfl) _ (radialRotatedForceKernel_regular parameters L compact state kind) order
  intro order shift radius
  exact rowMultiplicationEntry_hasDerivAt 3 _ _
    (fun component point mode => (actualForceScalar_hasDerivAt parameters L compact state kind component order point mode).const_mul _) radius shift (0,0)

end Grad.AnnularRadialSmoothness

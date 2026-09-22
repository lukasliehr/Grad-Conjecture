import AKBC41SameCorrectedFluxTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.OriginalKernelRetainedDecay
open Grad.SourceCollarFullSource Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.ActualPolarFlux Grad.OriginalKernelGraphRestriction Grad.ActualPolarEquations

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8≤
      originalCoefficientLowRadius parameters length)
    (vector : ACore parameters 3)
    {xiRow : DivisionRow 1 lower} (xi : SmoothLowPhysicalRow parameters lower positive xiRow)
    (radius : Icc lower (1 : ℝ))

theorem originalSignedFluxCurves_samePressure :
    originalCurveNegativeTrace
      (originalSignedFluxCurves parameters length compact lower positive bounded state
        (originalPolarCovariantCurves parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
          lower positive bounded vector) xi) radius=
    originalCurveNegativeTrace
      (originalRawFluxCurves parameters length state.val.val.rho state.val.val.epsilon state.val.val.field small lower positive bounded
        (originalVectorLowCurves parameters lower positive bounded vector) xi).2.meanFree radius := by
  apply originalCurveNegativeTrace_ext _ _ bounded radius
  intro angles
  unfold originalSignedFluxCurves
  rw [SmoothLowPhysicalRow.fullField_meanFree _ bounded radius.val radius.property angles,
    SmoothLowPhysicalRow.fullField_meanFree _ bounded radius.val radius.property angles]
  congr 1
  funext query
  rw [SmoothLowPhysicalRow.fullField_add _ bounded _ radius.val radius.property query,
    fullField_signedCofactorRow_vector parameters length compact lower positive bounded state _ 0 radius.val radius.property query,
    fullField_signedCofactorComponent_offDiagonal parameters length compact lower positive bounded state 0 1
      (originalInverseRadiusCurves lower positive xi) (by decide) radius.val radius.property query,
    originalInverseRadiusCurves_fullField lower positive xi bounded radius.val radius.property query]
  rw [originalSignedFlux_sameRaw parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
    lower positive bounded vector radius (fun query => xi.fullField bounded (radius.val,query)) query,
    originalRawFluxCurves_fullField parameters length state.val.val.rho state.val.val.epsilon state.val.val.field small lower positive bounded
      (originalVectorLowCurves parameters lower positive bounded vector) xi radius.val radius.property query]
  have sameVector : (fun query => (originalVectorLowCurves parameters lower positive bounded vector).fullField bounded (radius.val,query))=
      originalCoreCircle parameters vector (tupleRadius lower positive radius) :=
    funext (originalVectorLowCurves_fullField parameters lower positive bounded vector radius.val radius.property)
  rw [sameVector]
  rfl

/-- AF3's literal corrected flux is exactly the pressure already stored in
the original AKBA tuple. Thus its genuine Rp selects the existing mass inverse. -/
theorem originalCorrectedFlux_samePressure :
    radialCorrectedFluxTrace parameters length compact state.val.val (tupleRadius lower positive radius) 0 0
      (originalCurveNegativeTrace
        (originalPolarCovariantCurves parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
          lower positive bounded vector) radius)
      ((radius.val : ℂ)⁻¹ • originalCurveNegativeTrace xi radius)=
    originalCurveNegativeTrace
      (originalRawFluxCurves parameters length state.val.val.rho state.val.val.epsilon state.val.val.field small lower positive bounded
        (originalVectorLowCurves parameters lower positive bounded vector) xi).2.meanFree radius := by
  rw [← originalSignedFluxCurves_negative parameters length compact lower positive bounded state]
  exact originalSignedFluxCurves_samePressure parameters length compact lower positive bounded state small vector xi radius

end Grad.OriginalKernelCovariantRecovery

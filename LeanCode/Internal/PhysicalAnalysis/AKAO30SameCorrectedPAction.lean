import AKAO29LiteralPhysicalRowConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualPolarFlux
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualBoundaryPrimitives Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.SourceCollar Grad.BoundaryLift Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)

def originalUnprojectedPKernel (r : RadialPoint) : RadialKernel parameters r 7 1 :=
  fullKernelAdd
    (fullKernelComposition (radialSignedCofactorRowKernel parameters length compact state 0 r)
      (radialNormalizedCovariantKernel parameters length compact state.val.val r state.val.property))
    (fullKernelComposition (radialSignedCofactorComponentKernel parameters length compact state 0 1 r)
      (sevenInputSlotKernel (radialKernelParameters parameters r) 3))

/-- The original corrected radial flux always retains its outer angular mean projection. -/
def originalCorrectedPKernel (r : RadialPoint) : RadialKernel parameters r 7 1 :=
  fullKernelComposition (angularMeanFreeKernel (radialKernelParameters parameters r) 1)
    (originalUnprojectedPKernel parameters length compact state r)

theorem originalUnprojectedPKernel_regular :
    RegularKernelFamily (originalUnprojectedPKernel parameters length compact state) :=
  ((radialSignedCofactorRowKernel_regular parameters length compact state 0).comp
    (radialNormalizedCovariantKernel_regular parameters length compact state.val)).add
    ((radialSignedCofactorComponentKernel_regular parameters length compact state 0 1).comp
      (constantMatrixRadialKernel_regular parameters _ _ _))

theorem originalUnprojectedPKernel_smooth :
    SmoothConjugatedFamily parameters lower positive bounded.le (originalUnprojectedPKernel parameters length compact state) :=
  ((actualSignedCofactorRow_conjugated_smooth parameters length compact state lower positive bounded 0).comp
    (radialNormalizedCovariantKernel_conjugated_smooth parameters length compact state.val lower positive bounded)).add
    ((actualSignedCofactorComponent_conjugated_smooth parameters length compact state lower positive bounded 0 1).comp
      (smoothConjugatedFamily_fixed parameters lower positive bounded
        (fun p => sevenInputSlotKernel p 3) (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)))

theorem originalCorrectedPKernel_regular :
    RegularKernelFamily (originalCorrectedPKernel parameters length compact state) :=
  (scalarModeRadialKernel_regular parameters _ _ _ _).comp
    (originalUnprojectedPKernel_regular parameters length compact state)

theorem originalCorrectedPKernel_smooth :
    SmoothConjugatedFamily parameters lower positive bounded.le (originalCorrectedPKernel parameters length compact state) :=
  (smoothConjugatedFamily_fixed parameters lower positive bounded
    (fun p => angularMeanFreeKernel p 1) (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)).comp
    (originalUnprojectedPKernel_smooth parameters length compact lower positive bounded state)

def actualCorrectedPAction : DivisionRow 7 lower →L[ℂ] DivisionRow 1 lower :=
  regularRadialBulkAction parameters 0 lower positive bounded.le
    (originalCorrectedPKernel parameters length compact state)
    (originalCorrectedPKernel_regular parameters length compact state)

def _root_.Grad.ActualSmoothPhysicalField.SmoothLowPhysicalRow.correctedP {row : DivisionRow 7 lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row) :
    SmoothLowPhysicalRow parameters lower positive (actualCorrectedPAction parameters length compact lower positive bounded state row) :=
  curves.action parameters lower positive bounded _
    (originalCorrectedPKernel_regular parameters length compact state)
    (originalCorrectedPKernel_smooth parameters length compact lower positive bounded state)

theorem originalSigma_cofactorRow (r : RadialPoint) :
    radialSigmaKernel parameters length compact state.val.val r 0 =
      radialCofactorJetRowKernel parameters length compact state 0 0 0 r := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift mode
  simp only [radialSigmaKernel,radialCofactorJetRowKernel,radialRowKernel_entry,
    radialSigmaCoefficients,sigmaScalar,radialCofactorJetScalar,cofactorJetSequence_zero]
  rfl

theorem originalSigma_cofactorComponent (r : RadialPoint) :
    radialSigmaComponentKernel parameters length compact state.val.val r 1 =
      radialSignedCofactorComponentKernel parameters length compact state 0 1 r := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift mode
  simp only [radialSigmaComponentKernel,radialSignedCofactorComponentKernel,fullKernelAdd_entry,
    circularCofactorComponentKernel,Fin.reduceEq,ite_false,fullZeroKernel_entry,zero_add,
    radialCofactorJetComponentKernel,radialScalarKernel,
    radialSigmaCoefficients,sigmaScalar,radialCofactorJetScalar,cofactorJetSequence_zero]
  rfl

/-- Exact trace equality to the accepted original corrected-flux formula, with no missing mean. -/
theorem originalCorrectedPKernel_trace (r : RadialPoint) (angular cell : ℕ)
    (input : SevenSlotTrace (radialKernelParameters parameters r) angular cell) :
    fullNegativeKernelAction _ angular cell (originalCorrectedPKernel parameters length compact state r)
      (sevenSlotFlatten _ angular cell input) =
    radialCorrectedFluxTrace parameters length compact state.val.val r angular cell
      (fullNegativeKernelAction _ angular cell
        (radialNormalizedCovariantKernel parameters length compact state.val.val r state.val.property)
        (sevenSlotFlatten _ angular cell input)) (input 3) := by
  rw [radialCorrectedFluxTrace,originalSigma_cofactorRow parameters length compact state r,
    originalSigma_cofactorComponent parameters length compact state r]
  simp only [originalCorrectedPKernel,originalUnprojectedPKernel,radialSignedCofactorRowKernel,
    fullNegativeKernelAction_comp,ContinuousLinearMap.comp_apply,fullNegativeKernelAction_add,
    fullNegativeKernelAction_neg,sevenInputSlotKernel_action]

end Grad.ActualPolarFlux

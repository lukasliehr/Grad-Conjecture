import AKC27ActualCofactorConjugatedFamilies

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Set
open scoped BigOperators ContDiff
namespace Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction
open Grad.AnnularKernelContinuity Grad.AnnularRadialSmoothness Grad.ActualGaugeSigmaPrimitives Grad.ActualCurrentPrimitives
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularSmoothCore

variable (parameters : PhaseParameters) (length compact : ℝ)
    (state : RetainedInverseState parameters length compact)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)

theorem actualRetainedForce_conjugated_smooth :
    SmoothConjugatedFamily (source := 3) (target := 1) parameters lower positive bounded.le
      (fun r => radialRetainedForceKernel parameters length compact state.val.val r) := by
  have base := rowRadialJet_conjugated_smooth parameters 3 lower positive bounded
    (fun order radius column => polarEntryScalar parameters
      (forceMatrixFamily parameters length state.val.val.epsilon state.val.val.field)
      (forceMatrixFamily_coherent parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low)
      0 column order radius)
    (fun order radius column mode => polarEntryScalar_hasDerivAt parameters _ _ 0 column order radius mode)
    (fun order r column moment => polarEntryScalarMoment_summable parameters _ _ 0 column moment order r.val r.property.1 r.property.2)
    (fun order moment column => ⟨_, fun r => polarEntryScalarMoment_bound parameters _ _ 0 column moment order r.val r.property.1 r.property.2⟩) 0
  have projection := smoothConjugatedFamily_fixed parameters lower positive bounded
    (fun p => coordinateProjectionKernel p 3 1) (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)
  exact (SmoothConjugatedFamily.smul base (fun _ => 2) contDiffOn_const).add
    (SmoothConjugatedFamily.smul projection (fun _ => 2) contDiffOn_const)

theorem actualSignedCofactorRow_conjugated_smooth (row : Fin 3) :
    SmoothConjugatedFamily (source := 3) (target := 1) parameters lower positive bounded.le
      (fun r => radialSignedCofactorRowKernel parameters length compact state row r) := by
  have projection := smoothConjugatedFamily_fixed parameters lower positive bounded
    (fun p => coordinateProjectionKernel p 3 row) (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)
  exact projection.neg.add (actualCofactorRow_conjugated_smooth parameters length compact state lower positive bounded row 0 0)

theorem actualSignedCofactorComponent_conjugated_smooth (row column : Fin 3) :
    SmoothConjugatedFamily (source := 1) (target := 1) parameters lower positive bounded.le
      (fun r => radialSignedCofactorComponentKernel parameters length compact state row column r) := by
  have fixed := smoothConjugatedFamily_fixed parameters lower positive bounded
    (fun p => circularCofactorComponentKernel p row column) (fun first second => sameCircularCofactorComponentKernel first second row column)
  exact fixed.add (actualCofactorComponent_conjugated_smooth parameters length compact state lower positive bounded row column 0 0)


end Grad.AnnularWeightedSmoothness

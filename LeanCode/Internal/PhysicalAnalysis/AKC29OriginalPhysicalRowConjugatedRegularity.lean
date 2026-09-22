import AKC28ActualRetainedForceConjugatedFamilies

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
open Grad.AnnularCurrentLow Grad.ActualBoundaryPrimitives

variable (parameters : PhaseParameters) (length compact : ℝ)
    (state : RetainedInverseState parameters length compact)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)

theorem actualOriginalForceZero_conjugated_smooth :
    SmoothConjugatedFamily (source := 3) (target := 1) parameters lower positive bounded.le
      (fun r => radialOriginalForceZeroKernel parameters length compact state r) := by
  have projection := smoothConjugatedFamily_fixed parameters lower positive bounded
    (fun p => fullKernelSmul (-2) (coordinateProjectionKernel p 3 0)) (fun _ _ _ _ => rfl)
  exact projection.add (radialForceKernel_conjugated_smooth parameters length compact state.val.val lower positive bounded 0 0)

theorem actualKV_conjugated_smooth :
    SmoothConjugatedFamily (source := 3) (target := 1) parameters lower positive bounded.le
      (fun r => radialKVKernel parameters length compact state r) := by
  have free := smoothConjugatedFamily_fixed parameters lower positive bounded
    (fun p => angularMeanFreeKernel p 1) (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  exact (((actualCofactorRow_conjugated_smooth parameters length compact state lower positive bounded 1 0 1).add
    ((actualSignedCofactorComponent_conjugated_smooth parameters length compact state lower positive bounded 1 0).comp
      (free.comp (actualRetainedForce_conjugated_smooth parameters length compact state lower positive bounded)))).add
    ((actualSignedCofactorComponent_conjugated_smooth parameters length compact state lower positive bounded 1 1).comp
      (actualOriginalForceZero_conjugated_smooth parameters length compact state lower positive bounded))).sub
    ((actualSignedCofactorComponent_conjugated_smooth parameters length compact state lower positive bounded 1 2).comp
      (free.comp (radialForceKernel_conjugated_smooth parameters length compact state.val.val lower positive bounded 1 0)))

theorem actualFirstPhysicalRow_conjugated_smooth :
    SmoothConjugatedFamily (source := 7) (target := 1) parameters lower positive bounded.le
      (fun r => radialNormalizedUnprojectedFirstRowKernel parameters length compact state r) := by
  have projection := smoothConjugatedFamily_fixed parameters lower positive bounded
    (fun p => coordinateProjectionKernel p 3 0) (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)
  exact (projection.comp
    (radialNormalizedRotatedCovariantKernel_conjugated_smooth parameters length compact state.val lower positive bounded)).sub
    ((actualRetainedForce_conjugated_smooth parameters length compact state lower positive bounded).comp
      (radialNormalizedCovariantKernel_conjugated_smooth parameters length compact state.val lower positive bounded))

theorem actualCPhysicalRow_conjugated_smooth :
    SmoothConjugatedFamily (source := 7) (target := 1) parameters lower positive bounded.le
      (fun r => radialNormalizedUnprojectedCKernel parameters length compact state r) := by
  have slot (component : Fin 7) := smoothConjugatedFamily_fixed parameters lower positive bounded
    (fun p => sevenInputSlotKernel p component) (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)
  exact ((((actualCofactorRow_conjugated_smooth parameters length compact state lower positive bounded 2 0 1).comp
    (radialNormalizedCovariantKernel_conjugated_smooth parameters length compact state.val lower positive bounded)).add
    ((actualSignedCofactorRow_conjugated_smooth parameters length compact state lower positive bounded 2).comp
      (radialNormalizedRotatedCovariantKernel_conjugated_smooth parameters length compact state.val lower positive bounded))).add
    ((actualCofactorComponent_conjugated_smooth parameters length compact state lower positive bounded 1 2 0 1).comp (slot 3))).add
    ((actualSignedCofactorComponent_conjugated_smooth parameters length compact state lower positive bounded 1 2).comp (slot 1))

theorem actualRVPhysicalRow_conjugated_smooth :
    SmoothConjugatedFamily (source := 7) (target := 1) parameters lower positive bounded.le
      (fun r => radialNormalizedPhysicalRVKernel parameters length compact state r) := by
  have free := smoothConjugatedFamily_fixed parameters lower positive bounded
    (fun p => angularMeanFreeKernel p 1) (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  have slot (component : Fin 7) := smoothConjugatedFamily_fixed parameters lower positive bounded
    (fun p => sevenInputSlotKernel p component) (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)
  have radius : ContDiffOn ℝ ∞ (fun radius : ℝ => (radius : ℂ)) (Icc lower 1) := Complex.ofRealCLM.contDiff.contDiffOn
  have radialTerm := SmoothConjugatedFamily.smul
    ((actualCofactorComponent_conjugated_smooth parameters length compact state lower positive bounded 1 0 1 0).comp (slot 3))
    (fun radius : ℝ => (radius : ℂ)) radius
  have axialTerm := SmoothConjugatedFamily.smul
    ((actualCofactorComponent_conjugated_smooth parameters length compact state lower positive bounded 1 2 0 2).comp (slot 3))
    (fun radius : ℝ => (radius : ℂ) * (length : ℂ)⁻¹) (radius.mul contDiffOn_const)
  exact free.comp
    (((((actualSignedCofactorComponent_conjugated_smooth parameters length compact state lower positive bounded 1 1).comp (slot 1)).add
      ((actualKV_conjugated_smooth parameters length compact state lower positive bounded).comp
        (radialNormalizedCovariantKernel_conjugated_smooth parameters length compact state.val lower positive bounded))).sub radialTerm).sub axialTerm)

/-- All three SAME original physical row kernels have every finite radial order at the original analytic width, with a finite input reserve. The third row retains the original mean-free P. -/
theorem sameFullPhysicalRows_conjugated_smooth (row : Fin 3) :
    SmoothConjugatedFamily (source := 7) (target := 1) parameters lower positive bounded.le
      (lowPhysicalRowKernel parameters length compact state row) := by
  fin_cases row
  · exact actualFirstPhysicalRow_conjugated_smooth parameters length compact state lower positive bounded
  · exact actualCPhysicalRow_conjugated_smooth parameters length compact state lower positive bounded
  · exact actualRVPhysicalRow_conjugated_smooth parameters length compact state lower positive bounded


/-- Exact provider for the actual phase-weighted source and solution bootstrap. -/
theorem originalPhysicalRowKernel_finiteOrder (row : Fin 3) (grade order : ℕ) :
    ∃ reserve : ℕ, ContDiffOn ℝ order
      (radialConjugatedAction parameters lower positive bounded.le
        (lowPhysicalRowKernel parameters length compact state row) grade reserve) (Icc lower 1) := by
  obtain ⟨reserve, regular⟩ := sameFullPhysicalRows_conjugated_smooth parameters length compact state lower positive bounded row grade order
  refine ⟨reserve, regular.congr ?_⟩
  intro radius _
  rfl

end Grad.AnnularWeightedSmoothness

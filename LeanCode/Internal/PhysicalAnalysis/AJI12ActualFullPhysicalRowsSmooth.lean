import AJI11ActualRadialScalarAndForce
import AEI14ActualCurrentLowPhysicalRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
open scoped ContDiff
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction
open Grad.AnnularKernelContinuity Grad.AnnularRadialSmoothness Grad.AnnularCurrentLow Grad.ActualBoundaryPrimitives

variable (parameters : PhaseParameters) (length compact : ℝ)
    (state : RetainedInverseState parameters length compact)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)

theorem actualOriginalForceZero_smooth :
    SmoothPolynomialFamily (source := 3) (target := 1) parameters lower positive bounded.le
      (fun r => radialOriginalForceZeroKernel parameters length compact state r) := by
  have projection := smoothPolynomialFamily_fixed parameters lower positive bounded.le
    (fun p => fullKernelSmul (-2) (coordinateProjectionKernel p 3 0)) (fun _ _ _ _ => rfl)
  exact projection.add (radialForceKernel_smooth parameters length compact state.val.val lower positive bounded 0 0)

theorem actualKV_smooth :
    SmoothPolynomialFamily (source := 3) (target := 1) parameters lower positive bounded.le
      (fun r => radialKVKernel parameters length compact state r) := by
  have free := smoothPolynomialFamily_fixed parameters lower positive bounded.le
    (fun p => angularMeanFreeKernel p 1) (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  exact (((actualCofactorRow_smooth parameters length compact state lower positive bounded 1 0 1).add
    ((actualSignedCofactorComponent_smooth parameters length compact state lower positive bounded 1 0).comp
      (free.comp (actualRetainedForce_smooth parameters length compact state lower positive bounded)))).add
    ((actualSignedCofactorComponent_smooth parameters length compact state lower positive bounded 1 1).comp
      (actualOriginalForceZero_smooth parameters length compact state lower positive bounded))).sub
    ((actualSignedCofactorComponent_smooth parameters length compact state lower positive bounded 1 2).comp
      (free.comp (radialForceKernel_smooth parameters length compact state.val.val lower positive bounded 1 0)))

theorem actualFirstPhysicalRow_smooth :
    SmoothPolynomialFamily (source := 7) (target := 1) parameters lower positive bounded.le
      (fun r => radialNormalizedUnprojectedFirstRowKernel parameters length compact state r) := by
  have projection := smoothPolynomialFamily_fixed parameters lower positive bounded.le
    (fun p => coordinateProjectionKernel p 3 0) (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)
  exact (projection.comp
    (radialNormalizedRotatedCovariantKernel_smooth parameters length compact state.val lower positive bounded)).sub
    ((actualRetainedForce_smooth parameters length compact state lower positive bounded).comp
      (radialNormalizedCovariantKernel_smooth parameters length compact state.val lower positive bounded))

theorem actualCPhysicalRow_smooth :
    SmoothPolynomialFamily (source := 7) (target := 1) parameters lower positive bounded.le
      (fun r => radialNormalizedUnprojectedCKernel parameters length compact state r) := by
  have slot (component : Fin 7) := smoothPolynomialFamily_fixed parameters lower positive bounded.le
    (fun p => sevenInputSlotKernel p component) (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)
  exact ((((actualCofactorRow_smooth parameters length compact state lower positive bounded 2 0 1).comp
    (radialNormalizedCovariantKernel_smooth parameters length compact state.val lower positive bounded)).add
    ((actualSignedCofactorRow_smooth parameters length compact state lower positive bounded 2).comp
      (radialNormalizedRotatedCovariantKernel_smooth parameters length compact state.val lower positive bounded))).add
    ((actualCofactorComponent_smooth parameters length compact state lower positive bounded 1 2 0 1).comp (slot 3))).add
    ((actualSignedCofactorComponent_smooth parameters length compact state lower positive bounded 1 2).comp (slot 1))

theorem actualRVPhysicalRow_smooth :
    SmoothPolynomialFamily (source := 7) (target := 1) parameters lower positive bounded.le
      (fun r => radialNormalizedPhysicalRVKernel parameters length compact state r) := by
  have free := smoothPolynomialFamily_fixed parameters lower positive bounded.le
    (fun p => angularMeanFreeKernel p 1) (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  have slot (component : Fin 7) := smoothPolynomialFamily_fixed parameters lower positive bounded.le
    (fun p => sevenInputSlotKernel p component) (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)
  have radius : ContDiffOn ℝ ∞ (fun radius : ℝ => (radius : ℂ)) (Icc lower 1) := Complex.ofRealCLM.contDiff.contDiffOn
  have radialTerm := smoothPolynomialFamily_radial_smul
    ((actualCofactorComponent_smooth parameters length compact state lower positive bounded 1 0 1 0).comp (slot 3))
    (fun radius : ℝ => (radius : ℂ)) radius
  have axialTerm := smoothPolynomialFamily_radial_smul
    ((actualCofactorComponent_smooth parameters length compact state lower positive bounded 1 2 0 2).comp (slot 3))
    (fun radius : ℝ => (radius : ℂ) * (length : ℂ)⁻¹) (radius.mul contDiffOn_const)
  exact free.comp
    (((((actualSignedCofactorComponent_smooth parameters length compact state lower positive bounded 1 1).comp (slot 1)).add
      ((actualKV_smooth parameters length compact state lower positive bounded).comp
        (radialNormalizedCovariantKernel_smooth parameters length compact state.val lower positive bounded))).sub radialTerm).sub axialTerm)

/-- All three original pre-high-projection physical rows are smooth. The
third row retains the literal mean-free P from the physical V equation. -/
theorem sameFullPhysicalRows_smooth (row : Fin 3) :
    SmoothPolynomialFamily (source := 7) (target := 1) parameters lower positive bounded.le
      (lowPhysicalRowKernel parameters length compact state row) := by
  fin_cases row
  · exact actualFirstPhysicalRow_smooth parameters length compact state lower positive bounded
  · exact actualCPhysicalRow_smooth parameters length compact state lower positive bounded
  · exact actualRVPhysicalRow_smooth parameters length compact state lower positive bounded

end Grad.AnnularSmoothCore

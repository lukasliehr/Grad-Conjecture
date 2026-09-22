import AKBH3SameLiteralForceMatrix

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
namespace Grad.ActualForceMoments
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.ActualCurrentPrimitives Grad.AnnularReconstruction
open Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.AnnularWeightedSmoothness Grad.ActualNativeCellMoments
open Grad.ActualPhysicalField Grad.GaugeCoefficients.Physical.Allocation

/-- All-grade control of the actual full force matrix applied to the SAME
native covariant packet, before Fourier cell selection. -/
theorem forceCurve_uniformBound (parameters : PhaseParameters) (length compact : ℝ)
    (state : AnnularReconstructionState parameters length compact)
    (rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
      (row : DivisionRow 7 lower) (curves : SmoothLowPhysicalRow parameters lower positive row) (radius : ℝ),
      ‖(sameForceMatrixCurves parameters length rho epsilon base small lower positive bounded
        (curves.covariant parameters length compact lower positive bounded state)).curve grade radius‖ ≤
          constant * ‖curves.curve grade radius‖ := by
  obtain ⟨C,Cnonnegative,covariantBound⟩ := covariantCurve_uniformBound parameters length compact state grade
  let family := forceMatrixFamily parameters length epsilon base
  have coherent := forceMatrixFamily_coherent parameters length rho epsilon base small
  have regular := originalMatrixRadialKernel_regular parameters family coherent
  obtain ⟨K,Knonnegative,kernelBound⟩ := regular.2 grade
  refine ⟨K*C,mul_nonneg Knonnegative Cnonnegative,?_⟩
  intro lower positive bounded row curves radius
  have matrixBound := actionCurve_norm parameters _ regular grade K kernelBound lower positive bounded
    (originalMatrixRadialKernel_conjugated_smooth parameters family coherent lower positive bounded)
    (curves.covariant parameters length compact lower positive bounded state).cartesianCovariant radius
  exact matrixBound.trans ((mul_le_mul_of_nonneg_left
    (covariantBound lower positive bounded row curves radius) Knonnegative).trans_eq (mul_assoc _ _ _).symm)

end Grad.ActualForceMoments

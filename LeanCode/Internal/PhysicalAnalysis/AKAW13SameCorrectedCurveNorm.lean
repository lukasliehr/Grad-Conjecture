import AKAW12InsertedCurveNativeEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.ActualNativeCellMoments
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.AnnularWeightedSmoothness Grad.AnnularKernelContinuity Grad.AnnularKernelL2
open Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction Grad.ActualPhysicalField Grad.BoundaryKernelAction
open Grad.BoundaryLift
open Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation

def nativeHilbertMatrixUnit (parameters : PhaseParameters) (output input : Fin 3) : CellL2 3 →L[ℂ] CellL2 3 :=
  coefficientOperator parameters 0 (Equiv.refl _) (fun _ => matrixUnit output input)
    (norm_nonneg _) (fun _ => le_rfl)

/-- The existing exact Q rotation, viewed as one bounded operator at the
chosen polynomial grade. This adds no synthesis or alternate physical field. -/
def nativeCovariantRotation (parameters : PhaseParameters) (grade : ℕ) : CellL2 3 →L[ℂ] CellL2 3 :=
  (nativeHilbertMatrixUnit parameters 0 0).comp (weightedHilbertCosine parameters 3 grade) -
    (nativeHilbertMatrixUnit parameters 0 1).comp (weightedHilbertSine parameters 3 grade) +
    (nativeHilbertMatrixUnit parameters 1 0).comp (weightedHilbertSine parameters 3 grade) +
    (nativeHilbertMatrixUnit parameters 1 1).comp (weightedHilbertCosine parameters 3 grade) +
    nativeHilbertMatrixUnit parameters 2 2

theorem nativeCovariantRotation_same {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row) (grade : ℕ) (radius : ℝ) :
    curves.cartesianCovariant.curve grade radius = nativeCovariantRotation parameters grade (curves.curve grade radius) := rfl

theorem actionCurve_norm {input output : ℕ} (parameters : PhaseParameters)
    (kernel : (radius : RadialPoint) → RadialKernel parameters radius input output)
    (regular : RegularKernelFamily kernel) (grade : ℕ) (constant : ℝ)
    (kernelBound : ∀ radius, fullKernelMoment (radialKernelParameters parameters radius) grade (kernel radius) ≤ constant)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (smooth : SmoothConjugatedFamily parameters lower positive bounded.le kernel)
    {row : DivisionRow input lower} (curves : SmoothLowPhysicalRow parameters lower positive row) (radius : ℝ) :
    ‖(curves.action parameters lower positive bounded kernel regular smooth).curve grade radius‖ ≤ constant * ‖curves.curve grade radius‖ := by
  apply (radialConjugatedAction parameters lower positive bounded.le kernel grade 0 radius).le_opNorm _ |>.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (conjugatedKernelAction_norm_le parameters grade 0 (collarRadius lower positive bounded.le radius) _).trans (kernelBound _)

/-- Genuine uniform all-grade norm control of F^-T Q a_c, applied to the SAME
full seven packet. The coefficient moments are existing proved quantities. -/
theorem correctedCurve_uniformBound (parameters : PhaseParameters) (length compact : ℝ)
    (state : AnnularReconstructionState parameters length compact)
    (rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
      (row : DivisionRow 7 lower) (curves : SmoothLowPhysicalRow parameters lower positive row) (radius : ℝ),
      ‖((curves.covariant parameters length compact lower positive bounded state).physicalUFromPolar
        parameters length rho epsilon base small lower positive bounded).curve grade radius‖ ≤
          constant * ‖curves.curve grade radius‖ := by
  have polarRegular := radialNormalizedCovariantKernel_regular parameters length compact state
  obtain ⟨polarBound,polarNonnegative,polarEstimate⟩ := polarRegular.2 grade
  let family := originalInverseTransposeFamily parameters length epsilon base
  have coherent := originalInverseTransposeFamily_coherent parameters length rho epsilon base small
  have vectorRegular := originalMatrixRadialKernel_regular parameters family coherent
  obtain ⟨vectorBound,vectorNonnegative,vectorEstimate⟩ := vectorRegular.2 grade
  let rotation := nativeCovariantRotation parameters grade
  refine ⟨vectorBound * ‖rotation‖ * polarBound,by positivity,?_⟩
  intro lower positive bounded row curves radius
  have polar := actionCurve_norm parameters _ polarRegular grade polarBound polarEstimate lower positive bounded
    (radialNormalizedCovariantKernel_conjugated_smooth parameters length compact state lower positive bounded) curves radius
  let covariant := curves.covariant parameters length compact lower positive bounded state
  have rotated : ‖covariant.cartesianCovariant.curve grade radius‖ ≤ ‖rotation‖ * ‖covariant.curve grade radius‖ := by
    rw [nativeCovariantRotation_same]
    exact rotation.le_opNorm _
  have vector := actionCurve_norm parameters _ vectorRegular grade vectorBound vectorEstimate lower positive bounded
    (originalMatrixRadialKernel_conjugated_smooth parameters family coherent lower positive bounded) covariant.cartesianCovariant radius
  apply vector.trans
  calc
    _ ≤ vectorBound * (‖rotation‖ * ‖covariant.curve grade radius‖) := mul_le_mul_of_nonneg_left rotated vectorNonnegative
    _ ≤ vectorBound * (‖rotation‖ * (polarBound * ‖curves.curve grade radius‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left polar (norm_nonneg _)) vectorNonnegative
    _ = _ := by ring

end Grad.ActualNativeCellMoments

import AAW5ActualFluxDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

section Actual
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem annularSolutionPCurve_eq (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (mode : HighAnnularMode) :
    annularSolutionPCurve parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode =
      (-(annularDSymbol mode)⁻¹) • annularSolutionQCurve parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode := rfl

/-- AG12 finite-mode radial regularity for the same actual variational
inverse. The physical sources are represented a.e.; all three resulting
physical solution curves are smooth through both collar endpoints. -/
theorem annularSameSolution_smooth (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (mode : HighAnnularMode) (f g h : C(ℝ, ComplexEuclidean 1))
    (fSmooth : ContDiffOn ℝ ∞ f (Icc lower 1))
    (gSmooth : ContDiffOn ℝ ∞ g (Icc lower 1))
    (hSmooth : ContDiffOn ℝ ∞ h (Icc lower 1))
    (fActual : annularDecodeMode parameters lower positive mode (source.1 mode) =ᵐ[volume.restrict (Icc lower 1)] f)
    (gActual : annularDecodeMode parameters lower positive mode (source.2.1 mode) =ᵐ[volume.restrict (Icc lower 1)] g)
    (hActual : annularDecodeMode parameters lower positive mode (source.2.2.1 mode) =ᵐ[volume.restrict (Icc lower 1)] h) :
    ContDiffOn ℝ ∞ (annularSolutionXiCurve parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode) (Icc lower 1) ∧
    ContDiffOn ℝ ∞ (annularSolutionQCurve parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode) (Icc lower 1) ∧
    ContDiffOn ℝ ∞ (annularSolutionPCurve parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode) (Icc lower 1) := by
  have pair := annularPhysicalSystem_smooth lower length positive bounded mode f g h fSmooth gSmooth hSmooth
    (annularSolutionXiCurve parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode)
    (annularSolutionQCurve parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode)
    (annularSolutionXi_derivative parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode f fActual)
    (annularSolutionQ_derivative parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode g h gActual hActual)
  refine ⟨pair.1, pair.2, ?_⟩
  rw [annularSolutionPCurve_eq]
  exact pair.2.const_smul (-(annularDSymbol mode)⁻¹)

/-- These are the original boundary values of the very same smooth
representatives; regularity does not substitute a separately solved ODE. -/
theorem annularSolutionCurves_boundary (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (mode : HighAnnularMode) :
    annularSolutionXiCurve parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode lower =
      annularInnerDatum parameters lower mode (innerValue mode) ∧
    annularSolutionPCurve parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode 1 =
      annularOuterDatum parameters mode (source.2.2.2 mode) := by
  constructor
  · change radialSectionExtension 1 lower bounded.le _ lower = _
    rw [annularSectionExtension_eval lower bounded.le _ lower ⟨le_rfl, bounded.le⟩]
    exact annularPhysicalValueSection_inner parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode
  · change radialSectionExtension 1 lower bounded.le _ 1 = _
    rw [annularSectionExtension_eval lower bounded.le _ 1 ⟨bounded.le, le_rfl⟩]
    exact annularPhysicalPSection_outer parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode

end Actual
end Grad.AnnularRegularity

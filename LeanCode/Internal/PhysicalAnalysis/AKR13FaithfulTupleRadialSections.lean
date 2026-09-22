import AKR9OriginalAngularNuGraphRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularOriginalSmoothCore Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The canonical continuous representative is faithful, including both
endpoints of the actual closed collar. -/
theorem radialSectionL2_faithful (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    Function.Injective (radialSectionL2 1 lower positive bounded.le) := by
  intro first second same
  have almost : (radialSectionExtension 1 lower bounded.le first : ℝ → ComplexEuclidean 1) =ᵐ[volume.restrict (Icc lower 1)]
      radialSectionExtension 1 lower bounded.le second := by
    filter_upwards [radialSectionL2_ae 1 lower positive bounded.le first,
      radialSectionL2_ae 1 lower positive bounded.le second] with radius firstLaw secondLaw
    rw [firstLaw,secondLaw,same]
  have actual := collarCurve_eq_of_ae lower bounded _ _
    (radialSectionExtension 1 lower bounded.le first).continuous.continuousOn
    (radialSectionExtension 1 lower bounded.le second).continuous.continuousOn almost
  apply ContinuousMap.ext
  intro radius
  have atRadius := actual radius.property
  change first (radialClamp lower bounded.le radius.val) = second (radialClamp lower bounded.le radius.val) at atRadius
  rw [radialClamp_eq lower bounded.le radius.val radius.property] at atRadius
  exact atRadius

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (tuple : OriginalSmoothTuple parameters lower) (slot : Fin 4)

theorem tupleConjugatedRadialGraph_section (mode : ℤ × ℤ) :
    weightedRadialSection 1 lower positive bounded
      (tupleConjugatedRadialGraph parameters lower positive bounded tuple slot mode) =
        tupleConjugatedJetSection parameters lower bounded tuple slot 0 mode := by
  apply radialSectionL2_faithful lower positive bounded
  rw [weightedRadialSection_bulk]
  exact weakRadialRealization_value 1 lower positive bounded _ _ _

theorem tupleConjugatedJetSection_value (mode : ℤ × ℤ) (radius : Icc lower (1 : ℝ)) :
    tupleConjugatedJetSection parameters lower bounded tuple slot 0 mode radius =
      (Real.exp (radialPhase parameters radius.val mode.2) : ℂ) •
        originalPhysicalCoefficient (tuple.val slot) radius.val mode := by
  change iteratedDerivWithin 0 (tupleWeightedCurve parameters lower tuple slot 0) (Icc lower 1) radius.val mode = _
  rw [iteratedDerivWithin_zero,tupleWeightedCurve_coefficient parameters lower tuple slot 0 radius.val radius.property mode]
  simp only [pow_zero,Complex.ofReal_one,one_smul]

theorem tupleConjugatedRadialGraph_trace (mode : ℤ × ℤ) (endpoint : Fin 2) :
    weightedRadialTrace 1 lower positive bounded endpoint
      (tupleConjugatedRadialGraph parameters lower positive bounded tuple slot mode) =
      (Real.exp (radialPhase parameters (radialEndpointRadius lower endpoint) mode.2) : ℂ) •
        originalPhysicalCoefficient (tuple.val slot) (radialEndpointRadius lower endpoint) mode := by
  rw [← weightedRadialSection_endpoint,tupleConjugatedRadialGraph_section,tupleConjugatedJetSection_value]

end Grad.AnnularOriginalCoreRealization

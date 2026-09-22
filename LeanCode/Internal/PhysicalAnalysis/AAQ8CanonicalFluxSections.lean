import AAQ7SharpFluxTraceFamily
import AAR22PhysicalContinuousSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularFluxTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- A continuous closed-interval representative is determined by its L2 class. -/
theorem radialSectionL2_injective (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    Function.Injective (radialSectionL2 1 lower positive bounded.le) := by
  intro first second same
  have ae : (radialSectionExtension 1 lower bounded.le first) =ᵐ[volume.restrict (Icc lower 1)]
      radialSectionExtension 1 lower bounded.le second := by
    filter_upwards [
      (collarContinuous_memLp (ComplexEuclidean 1) lower
        (radialSectionExtension 1 lower bounded.le first)).coeFn_toLp,
      (collarContinuous_memLp (ComplexEuclidean 1) lower
        (radialSectionExtension 1 lower bounded.le second)).coeFn_toLp] with radius firstLaw secondLaw
    change radialSectionL2 1 lower positive bounded.le first radius = _ at firstLaw
    change radialSectionL2 1 lower positive bounded.le second radius = _ at secondLaw
    rw [same] at firstLaw
    exact firstLaw.symm.trans secondLaw
  have pointwise := MeasureTheory.Measure.eqOn_of_ae_eq ae
    (radialSectionExtension 1 lower bounded.le first).continuous.continuousOn
    (radialSectionExtension 1 lower bounded.le second).continuous.continuousOn
    (by rw [interior_Icc, closure_Ioo bounded.ne])
  apply ContinuousMap.ext
  intro radius
  have atRadius := pointwise radius.property
  change first (radialClamp lower bounded.le radius.val) = second (radialClamp lower bounded.le radius.val) at atRadius
  rw [radialClamp_eq lower bounded.le radius.val radius.property] at atRadius
  exact atRadius

def annularFluxSection (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (data : annularFluxWeakGraph lower positive) (mode : HighAnnularMode) : RadialContinuousSection 1 lower :=
  weightedRadialSection 1 lower positive bounded (annularFluxRadialGraph lower positive bounded data mode)

theorem annularFluxSection_bulk (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (data : annularFluxWeakGraph lower positive) (mode : HighAnnularMode) :
    radialSectionL2 1 lower positive bounded.le (annularFluxSection lower positive bounded data mode) =
      annularFluxGraphValue lower positive mode data.val := by
  unfold annularFluxSection
  rw [weightedRadialSection_bulk, annularFluxRadialGraph_ordinary_value]

theorem annularFluxSection_add (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (first second : annularFluxWeakGraph lower positive) (mode : HighAnnularMode) :
    annularFluxSection lower positive bounded (first + second) mode =
      annularFluxSection lower positive bounded first mode + annularFluxSection lower positive bounded second mode := by
  apply radialSectionL2_injective lower positive bounded
  rw [map_add, annularFluxSection_bulk, annularFluxSection_bulk, annularFluxSection_bulk]
  exact map_add (annularFluxGraphValue lower positive mode) first.val second.val

theorem annularFluxSection_smul (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (scalar : ℂ) (data : annularFluxWeakGraph lower positive) (mode : HighAnnularMode) :
    annularFluxSection lower positive bounded (scalar • data) mode =
      scalar • annularFluxSection lower positive bounded data mode := by
  apply radialSectionL2_injective lower positive bounded
  rw [radialSectionL2_complex_smul, annularFluxSection_bulk, annularFluxSection_bulk]
  exact map_smul (annularFluxGraphValue lower positive mode) scalar data.val

theorem annularFluxTraceCoefficient_section (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (endpoint : Fin 2) (data : annularFluxWeakGraph lower positive) (mode : HighAnnularMode) :
    annularFluxTraceCoefficient lower positive bounded endpoint data mode =
      (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2))⁻¹ •
        annularFluxSection lower positive bounded data mode
          ⟨radialEndpointRadius lower endpoint, radialEndpointRadius_mem lower bounded.le endpoint⟩ := by
  unfold annularFluxTraceCoefficient annularFluxSection
  rw [weightedRadialSection_endpoint]

end Grad.AnnularFluxTrace

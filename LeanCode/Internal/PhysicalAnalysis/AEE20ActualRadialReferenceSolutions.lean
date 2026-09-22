import AEE19ActualRadialL2Representatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators ENNReal
namespace Grad.AnnularLowCompletion
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowVolterra
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

def continuousForcingPair (lower : ℝ) (first second : C(ℝ, ℂ)) : C(Icc lower 1, LowReferencePair) where
  toFun point := ![first point.val, second point.val]
  continuous_toFun := continuous_pi (fun entry => by
    fin_cases entry
    · exact first.continuous.comp continuous_subtype_val
    · exact second.continuous.comp continuous_subtype_val)

abbrev lowRadialValue (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : WeightedRadialH1 1 lower) :=
  collarH1Coordinate (ComplexEuclidean 1) lower 0 (weightedToOrdinary 1 lower positive bounded.le field)

abbrev lowRadialSlope (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : WeightedRadialH1 1 lower) :=
  collarH1Coordinate (ComplexEuclidean 1) lower 1 (weightedToOrdinary 1 lower positive bounded.le field)

/-- Actual reference Cauchy solutions in the already accepted radial graph,
with genuine incoming traces and literal L2 weak rows. -/
theorem lowRadialReferenceSolution_exists (parameters : PhaseParameters) (length lower : ℝ)
    (mode : LowAnnularMode) (positive : 0 < lower) (bounded : lower < 1)
    (forcingFirst forcingSecond : C(ℝ, ℂ)) (initialFirst initialSecond : ℂ) :
    ∃ first second : WeightedRadialH1 1 lower,
      weightedRadialTrace 1 lower positive bounded 0 first = scalarOne initialFirst ∧
      weightedRadialTrace 1 lower positive bounded 0 second = scalarOne initialSecond ∧
      (∀ᵐ radius ∂volume.restrict (Icc lower 1),
        lowRadialSlope lower positive bounded first radius =
          lowReferenceMatrix parameters length radius mode 0 0 • lowRadialValue lower positive bounded first radius +
          lowReferenceMatrix parameters length radius mode 0 1 • lowRadialValue lower positive bounded second radius +
          lowMu length radius mode.val.2 • scalarOne (forcingFirst radius) ∧
        lowRadialSlope lower positive bounded second radius =
          lowReferenceMatrix parameters length radius mode 1 0 • lowRadialValue lower positive bounded first radius +
          lowReferenceMatrix parameters length radius mode 1 1 • lowRadialValue lower positive bounded second radius +
          lowMu length radius mode.val.2 • scalarOne (forcingSecond radius)) := by
  obtain ⟨first, second, firstInitial, secondInitial, derivatives⟩ :=
    lowReferenceModeCauchy_exists parameters length lower 1 mode positive bounded.le
      (continuousForcingPair lower forcingFirst forcingSecond) ![initialFirst, initialSecond]
  have firstContinuous : ContinuousOn first (Icc lower 1) := fun radius member =>
    (derivatives ⟨radius, member⟩).1.continuousAt.continuousWithinAt
  have secondContinuous : ContinuousOn second (Icc lower 1) := fun radius member =>
    (derivatives ⟨radius, member⟩).2.continuousAt.continuousWithinAt
  let firstExtension := scalarClosedExtension lower bounded.le first firstContinuous
  let secondExtension := scalarClosedExtension lower bounded.le second secondContinuous
  let firstCurve := lowClassicalDerivativeCurve parameters length lower positive mode 0 firstExtension secondExtension forcingFirst
  let secondCurve := lowClassicalDerivativeCurve parameters length lower positive mode 1 firstExtension secondExtension forcingSecond
  have firstCurveActual (radius : ℝ) (member : radius ∈ Icc lower 1) :
      firstCurve radius = lowReferenceMatrix parameters length radius mode 0 0 • first radius +
        lowReferenceMatrix parameters length radius mode 0 1 • second radius + lowMu length radius mode.val.2 • forcingFirst radius := by
    dsimp [firstCurve]
    rw [lowClassicalDerivativeCurve_actual parameters length lower positive mode 0 _ _ _ radius member.1,
      scalarClosedExtension_actual lower bounded.le first firstContinuous radius member,
      scalarClosedExtension_actual lower bounded.le second secondContinuous radius member]
    simp only [Complex.real_smul]
  have secondCurveActual (radius : ℝ) (member : radius ∈ Icc lower 1) :
      secondCurve radius = lowReferenceMatrix parameters length radius mode 1 0 • first radius +
        lowReferenceMatrix parameters length radius mode 1 1 • second radius + lowMu length radius mode.val.2 • forcingSecond radius := by
    dsimp [secondCurve]
    rw [lowClassicalDerivativeCurve_actual parameters length lower positive mode 1 _ _ _ radius member.1,
      scalarClosedExtension_actual lower bounded.le first firstContinuous radius member,
      scalarClosedExtension_actual lower bounded.le second secondContinuous radius member]
    simp only [Complex.real_smul]
  have firstDifferentiates : ∀ radius ∈ Ioo lower 1, HasDerivAt first (firstCurve radius) radius := by
    intro radius member
    rw [firstCurveActual radius (Ioo_subset_Icc_self member), ← lowReferenceFirst_matrix]
    exact (derivatives ⟨radius, Ioo_subset_Icc_self member⟩).1
  have secondDifferentiates : ∀ radius ∈ Ioo lower 1, HasDerivAt second (secondCurve radius) radius := by
    intro radius member
    rw [secondCurveActual radius (Ioo_subset_Icc_self member), ← lowReferenceSecond_matrix]
    exact (derivatives ⟨radius, Ioo_subset_Icc_self member⟩).2
  let firstRadial := scalarRadialRealization lower positive bounded (first lower) firstCurve
  let secondRadial := scalarRadialRealization lower positive bounded (second lower) secondCurve
  refine ⟨firstRadial, secondRadial, ?_, ?_, ?_⟩
  · rw [scalarRadialRealization_incoming, firstInitial]
    rfl
  · rw [scalarRadialRealization_incoming, secondInitial]
    rfl
  · have firstValue := weightedRadial_value_ae_of_section lower positive bounded firstRadial (fun radius => scalarOne (first radius))
      (scalarRadialRealization_actual lower positive bounded first firstCurve firstContinuous firstDifferentiates)
    have secondValue := weightedRadial_value_ae_of_section lower positive bounded secondRadial (fun radius => scalarOne (second radius))
      (scalarRadialRealization_actual lower positive bounded second secondCurve secondContinuous secondDifferentiates)
    filter_upwards [firstValue, secondValue,
      scalarRadialRealization_slope_ae lower positive bounded (first lower) firstCurve,
      scalarRadialRealization_slope_ae lower positive bounded (second lower) secondCurve,
      ae_restrict_mem measurableSet_Icc] with radius firstValue secondValue firstSlope secondSlope member
    change lowRadialSlope lower positive bounded firstRadial radius = _ at firstSlope
    change lowRadialSlope lower positive bounded secondRadial radius = _ at secondSlope
    change lowRadialValue lower positive bounded firstRadial radius = _ at firstValue
    change lowRadialValue lower positive bounded secondRadial radius = _ at secondValue
    rw [firstValue, secondValue, firstSlope, secondSlope]
    constructor
    · simpa only [map_add, scalarOne_real_smul] using congrArg scalarOne (firstCurveActual radius member)
    · simpa only [map_add, scalarOne_real_smul] using congrArg scalarOne (secondCurveActual radius member)

end Grad.AnnularLowCompletion

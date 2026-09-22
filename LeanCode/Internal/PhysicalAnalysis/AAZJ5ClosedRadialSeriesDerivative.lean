import AAZJ4TwoExtraGradeSummability

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularJointRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace









open Grad.AnnularRadialJets Grad.AnnularRegularity




/-- Reuse the accepted actual bounded interval-integral and section maps. -/
def annularSectionIntegral (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (radius : Icc lower (1 : ℝ)) : RadialContinuousSection 1 lower →L[ℝ] ComplexEuclidean 1 :=
  (radialIntervalIntegral 1 lower radius).comp (radialSectionL2 1 lower positive bounded)

theorem annularSectionIntegral_complex_smul (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (radius : Icc lower (1 : ℝ)) (scalar : ℂ) (field : RadialContinuousSection 1 lower) :
    annularSectionIntegral lower positive bounded radius (scalar • field) =
      scalar • annularSectionIntegral lower positive bounded radius field := by
  change radialIntervalIntegral 1 lower radius (radialSectionL2 1 lower positive bounded (scalar • field)) = _
  rw [radialSectionL2_complex_smul]
  change radialIntervalIntegral 1 lower radius (scalar • radialSectionL2 1 lower positive bounded field) =
    scalar • radialIntervalIntegral 1 lower radius (radialSectionL2 1 lower positive bounded field)
  unfold radialIntervalIntegral
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul]

def AnnularSectionDerivative (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (value derivative : RadialContinuousSection 1 lower) : Prop :=
  ∀ radius : Icc lower (1 : ℝ), value radius = value ⟨lower, le_rfl, bounded⟩ +
    annularSectionIntegral lower positive bounded radius derivative

theorem annularPhysicalJetSection_integral (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (jet : ℕ → AnnularRawFamily lower)
    (weak : ∀ order, AnnularPhysicalWeakDerivative parameters lower positive (jet order) (jet (order + 1)))
    (order : ℕ) (mode : HighAnnularMode) :
    AnnularSectionDerivative lower positive bounded.le
      (annularPhysicalJetSection parameters lower positive bounded jet weak order mode)
      (annularPhysicalJetSection parameters lower positive bounded jet weak (order + 1) mode) := by
  intro radius
  let graph := annularPhysicalJetGraph parameters lower positive bounded jet weak order mode
  have primitive := weightedRadialSection_primitive 1 lower positive bounded graph radius
  have endpoint := weightedRadialSection_endpoint 1 lower positive bounded 0 graph
  have slope := compactWeakRadialGraph_slope lower positive bounded _ _ (weak order mode)
  have integral : (∫ point in lower..radius.val,
      collarH1Coordinate (ComplexEuclidean 1) lower 1 (weightedToOrdinary 1 lower positive bounded.le graph) point) =
      annularSectionIntegral lower positive bounded.le radius
        (annularPhysicalJetSection parameters lower positive bounded jet weak (order + 1) mode) := by
    rw [← radialIntervalIntegral_apply 1 lower radius]
    change radialIntervalIntegral 1 lower radius _ = radialIntervalIntegral 1 lower radius _
    exact congrArg (radialIntervalIntegral 1 lower radius)
      (slope.trans (annularPhysicalJetSection_bulk parameters lower positive bounded jet weak (order + 1) mode).symm)
  exact primitive.trans (congrArg₂ (fun first second : ComplexEuclidean 1 => first + second) endpoint.symm integral)

theorem annularSectionDerivative_smul (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (value derivative : RadialContinuousSection 1 lower) (law : AnnularSectionDerivative lower positive bounded value derivative)
    (scalar : ℂ) : AnnularSectionDerivative lower positive bounded (scalar • value) (scalar • derivative) := by
  intro radius
  change scalar • value radius = scalar • value ⟨lower, le_rfl, bounded⟩ + _
  rw [law radius, smul_add, annularSectionIntegral_complex_smul]

/-- Uniformly summable section pairs retain the actual integral derivative
identity on the whole closed interval. All integration infrastructure is the
already accepted bounded ASG primitive map. -/
theorem annularSectionDerivative_tsum (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    {Index : Type*} (value derivative : Index → RadialContinuousSection 1 lower)
    (valueSummable : Summable value) (derivativeSummable : Summable derivative)
    (law : ∀ index, AnnularSectionDerivative lower positive bounded (value index) (derivative index)) :
    AnnularSectionDerivative lower positive bounded (∑' index, value index) (∑' index, derivative index) := by
  intro radius
  let evaluate : RadialContinuousSection 1 lower →L[ℝ] ComplexEuclidean 1 := ContinuousMap.evalCLM ℝ radius
  let anchor : RadialContinuousSection 1 lower →L[ℝ] ComplexEuclidean 1 :=
    ContinuousMap.evalCLM ℝ ⟨lower, le_rfl, bounded⟩
  let integrate := annularSectionIntegral lower positive bounded radius
  have evaluated := valueSummable.hasSum.map evaluate.toAddMonoidHom evaluate.continuous
  have anchored := valueSummable.hasSum.map anchor.toAddMonoidHom anchor.continuous
  have integrated := derivativeSummable.hasSum.map integrate.toAddMonoidHom integrate.continuous
  change HasSum (fun index => value index radius) ((∑' index, value index) radius) at evaluated
  have same : (fun index => value index radius) =
      (fun index => value index ⟨lower, le_rfl, bounded⟩ + integrate (derivative index)) :=
    funext (fun index => law index radius)
  rw [same] at evaluated
  exact evaluated.unique (anchored.add integrated)

/-- Termwise radial differentiation of that sum holds at both endpoints. -/
theorem annularSectionDerivative_hasDerivWithinAt (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (value derivative : RadialContinuousSection 1 lower) (law : AnnularSectionDerivative lower positive bounded value derivative)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (radialSectionExtension 1 lower bounded value) (derivative ⟨radius, inside⟩) (Icc lower 1) radius := by
  have same : radialSectionL2 1 lower positive bounded derivative =ᵐ[volume.restrict (Icc lower 1)]
      radialSectionExtension 1 lower bounded derivative := by
    filter_upwards [radialSectionL2_ae 1 lower positive bounded derivative] with point equality
    exact equality.symm
  have primitive (point : Icc lower (1 : ℝ)) :
      value point = value ⟨lower, le_rfl, bounded⟩ + ∫ r in lower..point.val, radialSectionL2 1 lower positive bounded derivative r := by
    rw [law point]
    exact congrArg (fun vector : ComplexEuclidean 1 => value ⟨lower, le_rfl, bounded⟩ + vector)
      (radialIntervalIntegral_apply 1 lower point (radialSectionL2 1 lower positive bounded derivative))
  have differentiated := radialSection_hasDerivWithinAt 1 lower bounded value _
    (radialSectionExtension 1 lower bounded derivative) same primitive radius inside
  rw [annularSectionExtension_eval lower bounded derivative radius inside] at differentiated
  exact differentiated

end Grad.AnnularJointRegularity

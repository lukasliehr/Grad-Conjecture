import AJE1GenuineSourceGraphCharacters
import AEK6CompleteSourceCompatibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource

/-- The actual graph character has the inverse character on the same
complete source graph, with no derivative graph supplied independently. -/
theorem sourceGraphTranslation_inverse (dimension : ℕ) (lower : ℝ) (tau : OrbitParameter)
    (field : lp (fun _ : ℤ × ℤ => WeightedRadialH1 dimension lower) 2) :
    sourceGraphTranslation dimension lower tau (sourceGraphTranslation dimension lower (-tau) field) = field := by
  apply lp.ext
  funext mode
  apply Subtype.ext
  change orbitCharacter tau mode • (orbitCharacter (-tau) mode • (field mode).val) = (field mode).val
  rw [smul_smul,orbitCharacter_inverse,one_smul]

def sourceGraphTranslationEquivalence (dimension : ℕ) (lower : ℝ) (tau : OrbitParameter) :
    lp (fun _ : ℤ × ℤ => WeightedRadialH1 dimension lower) 2 ≃ₗᵢ[ℝ]
      lp (fun _ : ℤ × ℤ => WeightedRadialH1 dimension lower) 2 where
  toLinearEquiv :=
    { (sourceGraphTranslation dimension lower tau).toLinearMap with
      invFun := sourceGraphTranslation dimension lower (-tau)
      left_inv := by
        intro field
        change sourceGraphTranslation dimension lower (-tau) (sourceGraphTranslation dimension lower tau field) = field
        simpa only [neg_neg] using sourceGraphTranslation_inverse dimension lower (-tau) field
      right_inv := sourceGraphTranslation_inverse dimension lower tau }
  norm_map' := sourceGraphTranslation_norm dimension lower tau

theorem totalSourceTrace_translation (parameters : PhaseParameters) (dimension : ℕ)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (angular cell grade : ℕ)
    (endpoint : Fin 2) (tau : OrbitParameter)
    (field : AnnularTotalSourceH1 parameters dimension lower angular cell grade) :
    totalSourceTrace parameters dimension lower positive bounded angular cell grade endpoint
      (sourceGraphTranslation dimension lower tau field) =
      orbitLpAction (ComplexEuclidean dimension) tau
        (totalSourceTrace parameters dimension lower positive bounded angular cell grade endpoint field) :=
  annularSourceTrace_translation parameters dimension lower positive bounded angular cell endpoint tau field

theorem endpointInclusion_translation (parameters : PhaseParameters) (dimension : ℕ) (radius : ℝ)
    (lowAngular lowCell highAngular highCell : ℕ) (angularLe : lowAngular ≤ highAngular)
    (cellLe : lowCell ≤ highCell) (tau : OrbitParameter)
    (field : AnnularEndpointTrace parameters dimension radius highAngular highCell) :
    annularEndpointInclusion parameters dimension radius lowAngular lowCell highAngular highCell angularLe cellLe
      (orbitLpAction (ComplexEuclidean dimension) tau field) =
      orbitLpAction (ComplexEuclidean dimension) tau
        (annularEndpointInclusion parameters dimension radius lowAngular lowCell highAngular highCell angularLe cellLe field) := by
  apply lp.ext
  funext mode
  rw [annularEndpointInclusion_apply,orbitLpAction_apply,orbitLpAction_apply,annularEndpointInclusion_apply]
  exact smul_comm _ _ _

theorem sourceRotationTrace_translation (parameters : PhaseParameters) (dimension : ℕ)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (cell grade : ℕ)
    (endpoint : Fin 2) (tau : OrbitParameter)
    (field : AnnularTotalSourceH1 parameters dimension lower 1 cell grade) :
    sourceRotationTrace parameters dimension lower positive bounded cell grade endpoint
      (sourceGraphTranslation dimension lower tau field) =
      orbitLpAction (ComplexEuclidean dimension) tau
        (sourceRotationTrace parameters dimension lower positive bounded cell grade endpoint field) := by
  change totalEndpointAngular parameters dimension (radialEndpointRadius lower endpoint) cell grade
      (totalSourceTrace parameters dimension lower positive bounded 1 cell grade endpoint
        (sourceGraphTranslation dimension lower tau field)) = _
  rw [totalSourceTrace_translation]
  apply lp.ext
  funext mode
  change sourceAngularRatio mode •
      (orbitCharacter tau mode • totalSourceTrace parameters dimension lower positive bounded 1 cell grade endpoint field mode) =
    orbitCharacter tau mode •
      (sourceAngularRatio mode • totalSourceTrace parameters dimension lower positive bounded 1 cell grade endpoint field mode)
  exact smul_comm _ _ _

def sourceTupleTranslationLinear (tau : OrbitParameter) : SourceBoundaryTuple →ₗ[ℂ] SourceBoundaryTuple where
  toFun source := WithLp.toLp 2 (fun slot => orbitLpAction (ComplexEuclidean 1) tau (source slot))
  map_add' first second := by
    apply PiLp.ext
    intro slot
    exact map_add (orbitLpAction (ComplexEuclidean 1) tau) (first slot) (second slot)
  map_smul' scalar source := by
    apply PiLp.ext
    intro slot
    exact map_smul (orbitLpAction (ComplexEuclidean 1) tau) scalar (source slot)

theorem sourceTupleTranslationLinear_norm (tau : OrbitParameter) (source : SourceBoundaryTuple) :
    ‖sourceTupleTranslationLinear tau source‖ = ‖source‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro slot _
  change ‖orbitLpAction (ComplexEuclidean 1) tau (source slot)‖ ^ 2 = ‖source slot‖ ^ 2
  exact congrArg (fun value : ℝ => value ^ 2) (orbitLpLinear_norm (ComplexEuclidean 1) tau (source slot))

def sourceTupleTranslation (tau : OrbitParameter) : SourceBoundaryTuple →L[ℂ] SourceBoundaryTuple :=
  (sourceTupleTranslationLinear tau).mkContinuous 1
    (fun source => (sourceTupleTranslationLinear_norm tau source).le.trans_eq (one_mul _).symm)

/-- The original source outer tuple (F0,RF0,F2) translates exactly as the
same three endpoint fields; its RF0 component is from the same F0 graph. -/
theorem highGraphOuterTuple_translation (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ) (tau : OrbitParameter)
    (graphs : HighRadialSourceGraphs parameters lower grade) :
    highGraphOuterTuple parameters lower positive bounded grade
      (sourceGraphTranslation 1 lower tau graphs.1,sourceGraphTranslation 1 lower tau graphs.2) =
      sourceTupleTranslation tau (highGraphOuterTuple parameters lower positive bounded grade graphs) := by
  apply PiLp.ext
  intro slot
  change highGraphOuterTuple parameters lower positive bounded grade
      (sourceGraphTranslation 1 lower tau graphs.1,sourceGraphTranslation 1 lower tau graphs.2) slot =
    orbitLpAction (ComplexEuclidean 1) tau (highGraphOuterTuple parameters lower positive bounded grade graphs slot)
  fin_cases slot
  · change annularEndpointInclusion parameters 1 (radialEndpointRadius lower 1) 0 0 1 0 (by omega) (by omega)
        (totalSourceTrace parameters 1 lower positive bounded 1 0 grade 1 (sourceGraphTranslation 1 lower tau graphs.1)) =
      orbitLpAction (ComplexEuclidean 1) tau
        (annularEndpointInclusion parameters 1 (radialEndpointRadius lower 1) 0 0 1 0 (by omega) (by omega)
          (totalSourceTrace parameters 1 lower positive bounded 1 0 grade 1 graphs.1))
    rw [totalSourceTrace_translation,endpointInclusion_translation]
  · exact sourceRotationTrace_translation parameters 1 lower positive bounded 0 grade 1 tau graphs.1
  · exact totalSourceTrace_translation parameters 1 lower positive bounded 0 0 grade 1 tau graphs.2

end Grad.AnnularStrongOrbit

import AAQ5UniformFluxSlopeEstimate
import AAR20ActualMomentGraph

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

abbrev AnnularFluxGraphAmbient (lower : ℝ) := AnnularBulk lower × AnnularBulk lower

def annularFluxGraphValue (lower : ℝ) (positive : 0 < lower) (mode : HighAnnularMode) :
    AnnularFluxGraphAmbient lower →L[ℂ] CollarL2 (ComplexEuclidean 1) lower :=
  (radialOrdinary 1 lower positive).comp
    ((lp.evalCLM ℂ (fun _ : HighAnnularMode => RadialL2 1 lower) 2 mode).comp (ContinuousLinearMap.fst ℂ _ _))

def annularFluxGraphDerivative (lower : ℝ) (positive : 0 < lower) (mode : HighAnnularMode) :
    AnnularFluxGraphAmbient lower →L[ℂ] CollarL2 (ComplexEuclidean 1) lower :=
  (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 : ℝ) •
    ((radialOrdinary 1 lower positive).comp
      ((lp.evalCLM ℂ (fun _ : HighAnnularMode => RadialL2 1 lower) 2 mode).comp (ContinuousLinearMap.snd ℂ _ _)))

/-- Literal graph of q and nu^-1 q' in the original sqrt(r) L2 storage.
Membership is the genuine distributional derivative relation. -/
def annularFluxWeakGraph (lower : ℝ) (positive : 0 < lower) : Submodule ℂ (AnnularFluxGraphAmbient lower) where
  carrier := {data | ∀ mode, CollarWeakDerivative lower
    (annularFluxGraphValue lower positive mode data) (annularFluxGraphDerivative lower positive mode data)}
  zero_mem' := by
    intro mode test vector
    simp only [map_zero, neg_zero]
  add_mem' := by
    intro first second firstWeak secondWeak mode test vector
    simp only [map_add, firstWeak mode test vector, secondWeak mode test vector, neg_add]
  smul_mem' := by
    intro scalar data weak mode
    simp only [map_smul]
    exact collarWeakDerivative_complex_smul lower scalar _ _ (weak mode)

theorem annularFluxWeakGraph_closed (lower : ℝ) (positive : 0 < lower) :
    IsClosed (annularFluxWeakGraph lower positive : Set (AnnularFluxGraphAmbient lower)) := by
  change IsClosed {data | ∀ mode, ∀ test : CollarTest lower, ∀ vector : ComplexEuclidean 1,
    collarPairing lower test.value vector (annularFluxGraphDerivative lower positive mode data) =
      -collarPairing lower test.derivative vector (annularFluxGraphValue lower positive mode data)}
  simp only [ofPred_forall]
  exact isClosed_iInter (fun mode => isClosed_iInter (fun test => isClosed_iInter (fun vector =>
    isClosed_eq ((collarPairing lower test.value vector).continuous.comp
      (annularFluxGraphDerivative lower positive mode).continuous)
      (((collarPairing lower test.derivative vector).continuous.comp
        (annularFluxGraphValue lower positive mode).continuous).neg))))

instance annularFluxWeakGraph_complete (lower : ℝ) (positive : 0 < lower) :
    CompleteSpace (annularFluxWeakGraph lower positive) :=
  (annularFluxWeakGraph_closed lower positive).completeSpace_coe

def annularFluxRadialGraph (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (data : annularFluxWeakGraph lower positive) (mode : HighAnnularMode) : WeightedRadialH1 1 lower :=
  compactWeakRadialGraph lower positive bounded _ _
    (collarWeak_isCompact 1 lower _ _ (data.property mode))

theorem annularFluxRadialGraph_ordinary_value (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (data : annularFluxWeakGraph lower positive) (mode : HighAnnularMode) :
    collarH1Coordinate (ComplexEuclidean 1) lower 0
      (weightedToOrdinary 1 lower positive bounded.le (annularFluxRadialGraph lower positive bounded data mode)) =
      annularFluxGraphValue lower positive mode data.val := compactWeakRadialGraph_value _ _ _ _ _ _

theorem annularFluxRadialGraph_ordinary_slope (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (data : annularFluxWeakGraph lower positive) (mode : HighAnnularMode) :
    collarH1Coordinate (ComplexEuclidean 1) lower 1
      (weightedToOrdinary 1 lower positive bounded.le (annularFluxRadialGraph lower positive bounded data mode)) =
      annularFluxGraphDerivative lower positive mode data.val := compactWeakRadialGraph_slope _ _ _ _ _ _

theorem radialSqrt_ordinary (lower : ℝ) (positive : 0 < lower) (field : RadialL2 1 lower) :
    radialSqrtMap 1 lower (radialOrdinary 1 lower positive field) = field := by
  apply Lp.ext
  filter_upwards [radialSqrtMap_ae 1 lower (radialOrdinary 1 lower positive field),
    radialOrdinary_ae 1 lower positive field, ae_restrict_mem measurableSet_Icc] with radius stored ordinary inside
  rw [stored, ordinary, smul_smul, reciprocalRadialWeight, max_eq_right inside.1, one_div,
    mul_inv_cancel₀ (Real.sqrt_pos.mpr (positive.trans_le inside.1)).ne', one_smul]

theorem annularFluxRadialGraph_value (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (data : annularFluxWeakGraph lower positive) (mode : HighAnnularMode) :
    weightedRadialCoordinate 1 lower 0 (annularFluxRadialGraph lower positive bounded data mode) = data.val.1 mode := by
  rw [weightedRadialCoordinate_eq_sqrt 1 lower positive bounded.le, annularFluxRadialGraph_ordinary_value]
  exact radialSqrt_ordinary lower positive (data.val.1 mode)

theorem annularFluxRadialGraph_slope (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (data : annularFluxWeakGraph lower positive) (mode : HighAnnularMode) :
    weightedRadialCoordinate 1 lower 1 (annularFluxRadialGraph lower positive bounded data mode) =
      (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 : ℝ) • data.val.2 mode := by
  rw [weightedRadialCoordinate_eq_sqrt 1 lower positive bounded.le, annularFluxRadialGraph_ordinary_slope]
  change radialSqrtMap 1 lower ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 : ℝ) •
    radialOrdinary 1 lower positive (data.val.2 mode)) = _
  rw [(radialSqrtMap 1 lower).map_smul_of_tower, radialSqrt_ordinary]

end Grad.AnnularFluxTrace

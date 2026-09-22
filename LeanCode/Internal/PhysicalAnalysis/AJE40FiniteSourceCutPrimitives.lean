import AJE19SharedHighProjectionCovariance
import AJB35OriginalLowDataFiniteApproximation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000
open Set Filter
open scoped Topology BigOperators
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularKernelL2 Grad.AnnularOrbitGenerators

section Cut
variable {ι E : Type*} [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

def sourceLpCut (support : Finset ι) : lp (fun _ : ι => E) 2 →L[ℝ] lp (fun _ : ι => E) 2 :=
  lpTwoMap (fun index => if index ∈ support then ContinuousLinearMap.id ℝ E else 0) 1 zero_le_one
    (fun index field => by split_ifs <;> simp)

theorem sourceLpCut_apply (support : Finset ι) (field : lp (fun _ : ι => E) 2) (index : ι) :
    sourceLpCut support field index = if index ∈ support then field index else 0 := by
  change (if index ∈ support then ContinuousLinearMap.id ℝ E else 0) (field index) = _
  split_ifs <;> rfl

theorem sourceLpCut_eq (support : Finset ι) (field : lp (fun _ : ι => E) 2) :
    sourceLpCut support field = originalLpCut support field := by
  apply lp.ext
  funext index
  rw [sourceLpCut_apply,originalLpCut_apply]

theorem sourceLpCut_bound (support : Finset ι) (field : lp (fun _ : ι => E) 2) :
    ‖sourceLpCut support field‖ ≤ ‖field‖ := by
  rw [sourceLpCut_eq]
  exact originalLpCut_norm support field

theorem sourceLpCut_tendsto (field : lp (fun _ : ι => E) 2) :
    Tendsto (fun support : Finset ι => sourceLpCut support field) atTop (𝓝 field) := by
  simp_rw [sourceLpCut_eq]
  exact originalLpCut_tendsto field

theorem sourceLpCut_realWeighted (support : Finset ι) (field weighted : lp (fun _ : ι => E) 2)
    (symbol : ι → ℝ) (actual : ∀ index, weighted index = symbol index • field index) (index : ι) :
    sourceLpCut support weighted index = symbol index • sourceLpCut support field index := by
  rw [sourceLpCut_apply,sourceLpCut_apply]
  by_cases inside : index ∈ support
  · simp only [inside,if_true,actual]
  · simp only [inside,if_false,smul_zero]
end Cut

section Pair
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

def sourceHilbertPairMap (first : E →L[ℝ] E) (second : F →L[ℝ] F) :
    WithLp 2 (E × F) →L[ℝ] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toContinuousLinearMap.comp
    ((first.prodMap second).comp (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toContinuousLinearMap)

theorem sourceHilbertPairMap_bound (first : E →L[ℝ] E) (second : F →L[ℝ] F)
    (firstBound : ∀ field, ‖first field‖ ≤ ‖field‖) (secondBound : ∀ field, ‖second field‖ ≤ ‖field‖)
    (data : WithLp 2 (E × F)) : ‖sourceHilbertPairMap first second data‖ ≤ ‖data‖ := by
  have source := WithLp.prod_norm_sq_eq_of_L2 (sourceHilbertPairMap first second data)
  have target := WithLp.prod_norm_sq_eq_of_L2 data
  change ‖sourceHilbertPairMap first second data‖ ^ 2 = ‖first data.ofLp.1‖ ^ 2 + ‖second data.ofLp.2‖ ^ 2 at source
  change ‖data‖ ^ 2 = ‖data.ofLp.1‖ ^ 2 + ‖data.ofLp.2‖ ^ 2 at target
  have firstSquare := pow_le_pow_left₀ (norm_nonneg _) (firstBound data.ofLp.1) 2
  have secondSquare := pow_le_pow_left₀ (norm_nonneg _) (secondBound data.ofLp.2) 2
  nlinarith only [source,target,firstSquare,secondSquare,norm_nonneg (sourceHilbertPairMap first second data),norm_nonneg data]

theorem sourceHilbertPairMap_tendsto {ι : Type*} (filter : Filter ι)
    (first : ι → E →L[ℝ] E) (second : ι → F →L[ℝ] F)
    (data : WithLp 2 (E × F))
    (firstLimit : Tendsto (fun index => first index data.ofLp.1) filter (𝓝 data.ofLp.1))
    (secondLimit : Tendsto (fun index => second index data.ofLp.2) filter (𝓝 data.ofLp.2)) :
    Tendsto (fun index => sourceHilbertPairMap (first index) (second index) data) filter (𝓝 data) := by
  have pair : Tendsto (fun index => (first index data.ofLp.1,second index data.ofLp.2)) filter (𝓝 data.ofLp) := by
    rw [nhds_prod_eq]
    exact firstLimit.prodMk secondLimit
  exact ((WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.continuous.tendsto data.ofLp).comp pair
end Pair

section Finite
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ)

def sourceFiniteHilbertMap (mapping : E →L[ℝ] E) :
    PiLp 2 (fun _ : Fin n => E) →L[ℝ] PiLp 2 (fun _ : Fin n => E) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => E)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun slot => mapping.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => E) slot)))

theorem sourceFiniteHilbertMap_bound (mapping : E →L[ℝ] E)
    (bound : ∀ field, ‖mapping field‖ ≤ ‖field‖) (data : PiLp 2 (fun _ : Fin n => E)) :
    ‖sourceFiniteHilbertMap n mapping data‖ ≤ ‖data‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_le_sum (fun slot _ => pow_le_pow_left₀ (norm_nonneg _) (bound (data slot)) 2)
end Finite

end Grad.AnnularStrongOrbit

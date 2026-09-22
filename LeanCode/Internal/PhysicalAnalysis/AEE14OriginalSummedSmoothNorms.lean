import AEE13ExactStoredModeNorms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators ENNReal
namespace Grad.AnnularLowCompletion
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowVolterra
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem lowLp_summable_norm_sq {E : Type*} [NormedAddCommGroup E]
    (field : lp (fun _ : LowAnnularIndex => E) 2) : Summable (fun index => ‖field index‖ ^ 2) := by
  have result := (memℓp_gen_iff (p := 2) (by norm_num)).mp (lp.memℓp field)
  norm_num at result
  exact result

theorem lowLp_norm_sq {E : Type*} [NormedAddCommGroup E]
    (field : lp (fun _ : LowAnnularIndex => E) 2) : ‖field‖ ^ 2 = ∑' index, ‖field index‖ ^ 2 := by
  have result := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at result
  exact result

theorem lowLp_pair_norm_sq {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (first : lp (fun _ : LowAnnularIndex => E) 2) (second : lp (fun _ : LowAnnularIndex => F) 2) :
    ‖first‖ ^ 2 + ‖second‖ ^ 2 = ∑' index, (‖first index‖ ^ 2 + ‖second index‖ ^ 2) := by
  rw [lowLp_norm_sq, lowLp_norm_sq, (lowLp_summable_norm_sq first).tsum_add (lowLp_summable_norm_sq second)]

theorem lowCoreGraphSquare_summable (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) : Summable (lowCoreGraphSquare length lower core) := by
  have sum := (lowLp_summable_norm_sq ((lowSmoothGraph lower length positive bounded core).val 0)).add
    (lowLp_summable_norm_sq ((lowSmoothGraph lower length positive bounded core).val 1))
  exact sum.congr (fun index => (lowCoreGraphSquare_stored lower length positive bounded core index).symm)

theorem lowSmoothGraph_norm_sq (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) :
    ‖lowSmoothGraph lower length positive bounded core‖ ^ 2 = ∑' index, lowCoreGraphSquare length lower core index := by
  rw [lowEnergyGraph_norm_sq, lowLp_pair_norm_sq]
  exact tsum_congr (fun index => (lowCoreGraphSquare_stored lower length positive bounded core index).symm)

theorem lowCoreDataSquare_summable (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) : Summable (lowCoreDataSquare parameters length lower positive core) := by
  let data := lowReferenceDataOperator parameters length lower lengthPositive positive bounded
    (lowSmoothGraph lower length positive bounded core)
  have sum := (lowLp_summable_norm_sq data.ofLp.1).add (lowLp_summable_norm_sq data.ofLp.2)
  exact sum.congr (fun index => (lowCoreDataSquare_stored parameters lower length lengthPositive positive bounded core index).symm)

theorem lowSmoothGraph_data_norm_sq (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) :
    ‖lowReferenceDataOperator parameters length lower lengthPositive positive bounded
      (lowSmoothGraph lower length positive bounded core)‖ ^ 2 =
      ∑' index, lowCoreDataSquare parameters length lower positive core index := by
  rw [WithLp.prod_norm_sq_eq_of_L2, lowLp_pair_norm_sq]
  exact tsum_congr (fun index => (lowCoreDataSquare_stored parameters lower length lengthPositive positive bounded core index).symm)

end Grad.AnnularLowCompletion

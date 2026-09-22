import AIU11CompleteIndependentCoupledData
import AIY4SharedDataSingleNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
set_option synthInstance.maxHeartbeats 400000
namespace Grad.AnnularStrongSolution
open Grad.ClosedJets Grad.CartesianState Grad.AnnularCurrentSource
open Grad.AnnularFullSource Grad.AnnularStrongData Grad.AnnularKnownLow Grad.AnnularCoupledInverse

private theorem sharedPairBound {E F G : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedAddCommGroup G]
    (first : E → F) (second : E → G)
    (firstBound : ∀ field, ‖first field‖ ≤ ‖field‖)
    (secondBound : ∀ field, ‖second field‖ ≤ ‖field‖) (field : E) :
    ‖WithLp.toLp 2 (first field, second field)‖ ≤ 2 * ‖field‖ := by
  have square := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (first field, second field))
  change ‖WithLp.toLp 2 (first field, second field)‖ ^ 2 =
    ‖first field‖ ^ 2 + ‖second field‖ ^ 2 at square
  have firstSq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (firstBound field)
  have secondSq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (secondBound field)
  nlinarith only [square, firstSq, secondSq, norm_nonneg field,
    norm_nonneg (WithLp.toLp 2 (first field, second field)), sq_nonneg ‖field‖]

/-- Both diagonal solver inputs are projections of one original strong
source; their F0/RF0/F2 tuple is shared, rather than independently prescribed. -/
def strongToIndependent (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) :
    StrongDataCarrier parameters lower positive bounded 0 0 →L[ℝ]
      IndependentCoupledData parameters lower positive bounded :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    ((strongToHigh parameters lower positive bounded 0 0).prod
      (strongToLow parameters lower positive bounded 0 0))

theorem strongToIndependent_high (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (data : StrongDataCarrier parameters lower positive bounded 0 0) :
    (strongToIndependent parameters lower positive bounded data).ofLp.1 =
      strongToHigh parameters lower positive bounded 0 0 data := rfl

theorem strongToIndependent_low (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (data : StrongDataCarrier parameters lower positive bounded 0 0) :
    (strongToIndependent parameters lower positive bounded data).ofLp.2 =
      strongToLow parameters lower positive bounded 0 0 data := rfl

theorem strongToIndependent_bound (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (data : StrongDataCarrier parameters lower positive bounded 0 0) :
    let pair : IndependentCoupledData parameters lower positive bounded :=
      strongToIndependent parameters lower positive bounded data
    ‖pair‖ ≤ 2 * ‖data‖ :=
  sharedPairBound (strongToHigh parameters lower positive bounded 0 0)
    (strongToLow parameters lower positive bounded 0 0)
    (strongToHigh_bound parameters lower positive bounded 0 0)
    (strongToLow_bound parameters lower positive bounded 0 0) data

/-- The three original forcing coordinates in both solver projections are
literally identical.  This is independent of the physical state and radius. -/
theorem strongToIndependent_sharedSource (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (data : StrongDataCarrier parameters lower positive bounded 0 0) :
    let pair := strongToIndependent parameters lower positive bounded data
    let high := ActualHighKnownCarrier.toGraphKnownData parameters lower positive bounded 0 0 pair.ofLp.1
    high.weighted 0 = pair.ofLp.2.ofLp.1.ofLp.1 0 ∧
    high.weighted 1 = pair.ofLp.2.ofLp.1.ofLp.1 1 ∧
    high.weighted 2 = pair.ofLp.2.ofLp.1.ofLp.1 2 :=
  ⟨rfl, rfl, rfl⟩

end Grad.AnnularStrongSolution

import AJB30IndependentLowDataGenerators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Filter
open scoped Topology BigOperators
namespace Grad.AnnularOrbitGenerators

section Cut
variable {ι V : Type*} [DecidableEq ι] [NormedAddCommGroup V]

def originalLpCut (support : Finset ι) (field : lp (fun _ : ι => V) 2) : lp (fun _ : ι => V) 2 :=
  ∑ index ∈ support, lp.single 2 index (field index)

theorem originalLpCut_apply (support : Finset ι) (field : lp (fun _ : ι => V) 2) (index : ι) :
    originalLpCut support field index = if index ∈ support then field index else 0 := by
  rw [originalLpCut, lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.single_apply, Pi.single_apply]
  by_cases inside : index ∈ support
  · rw [if_pos inside, Finset.sum_eq_single_of_mem index inside]
    · simp only [ite_true]
    · intro other _ different
      exact if_neg (Ne.symm different)
  · rw [if_neg inside]
    apply Finset.sum_eq_zero
    intro other member
    have different : index ≠ other := by
      intro same
      subst other
      exact inside member
    exact if_neg different

theorem originalLpCut_norm (support : Finset ι) (field : lp (fun _ : ι => V) 2) :
    ‖originalLpCut support field‖ ≤ ‖field‖ := by
  apply lp.norm_mono (by norm_num)
  intro index
  rw [originalLpCut_apply]
  by_cases inside : index ∈ support
  · simp only [inside, if_true, le_refl]
  · simp only [inside, if_false, norm_zero, norm_nonneg]

theorem originalLpCut_tendsto (field : lp (fun _ : ι => V) 2) :
    Tendsto (fun support : Finset ι => originalLpCut support field) atTop (𝓝 field) :=
  lp.hasSum_single (by norm_num) field

theorem originalLpCut_weighted [NormedSpace ℂ V] (support : Finset ι)
    (field weighted : lp (fun _ : ι => V) 2) (coefficient : ι → ℂ)
    (actual : ∀ index, weighted index = coefficient index • field index) (index : ι) :
    originalLpCut support weighted index = coefficient index • originalLpCut support field index := by
  rw [originalLpCut_apply, originalLpCut_apply]
  by_cases inside : index ∈ support
  · simp only [inside, if_true, actual]
  · simp only [inside, if_false, smul_zero]
end Cut
end Grad.AnnularOrbitGenerators
namespace Grad.AnnularLowOrbit
open Grad.AnnularLowEnergy Grad.AnnularOrbitGenerators

/-- Finite cutoffs of both independently prescribed original data entries. -/
def lowDataCut (lower : ℝ) (support : Finset LowAnnularIndex) (data : LowEnergyData lower) : LowEnergyData lower :=
  WithLp.toLp 2 (originalLpCut support data.ofLp.1, originalLpCut support data.ofLp.2)

theorem lowDataCut_norm (lower : ℝ) (support : Finset LowAnnularIndex) (data : LowEnergyData lower) :
    ‖lowDataCut lower support data‖ ≤ ‖data‖ := by
  have first := pow_le_pow_left₀ (norm_nonneg _) (originalLpCut_norm support data.ofLp.1) 2
  have second := pow_le_pow_left₀ (norm_nonneg _) (originalLpCut_norm support data.ofLp.2) 2
  have sourceSquare := WithLp.prod_norm_sq_eq_of_L2 (lowDataCut lower support data)
  have targetSquare := WithLp.prod_norm_sq_eq_of_L2 data
  change ‖lowDataCut lower support data‖ ^ 2 = ‖originalLpCut support data.ofLp.1‖ ^ 2 + ‖originalLpCut support data.ofLp.2‖ ^ 2 at sourceSquare
  change ‖data‖ ^ 2 = ‖data.ofLp.1‖ ^ 2 + ‖data.ofLp.2‖ ^ 2 at targetSquare
  nlinarith only [first, second, sourceSquare, targetSquare, norm_nonneg (lowDataCut lower support data), norm_nonneg data]

theorem lowDataCut_tendsto (lower : ℝ) (data : LowEnergyData lower) :
    Tendsto (fun support : Finset LowAnnularIndex => lowDataCut lower support data) atTop (𝓝 data) := by
  have pair : Tendsto (fun support : Finset LowAnnularIndex =>
      (originalLpCut support data.ofLp.1, originalLpCut support data.ofLp.2)) atTop (𝓝 data.ofLp) := by
    rw [nhds_prod_eq]
    exact (originalLpCut_tendsto data.ofLp.1).prodMk (originalLpCut_tendsto data.ofLp.2)
  exact ((WithLp.prodContinuousLinearEquiv 2 ℂ (LowEnergyBulk lower) LowEnergyBoundary).symm.continuous.tendsto data.ofLp).comp pair

theorem lowDataCut_finite (lower : ℝ) (support : Finset LowAnnularIndex) (data : LowEnergyData lower) :
    (∀ index, index ∉ support → (lowDataCut lower support data).ofLp.1 index = 0) ∧
    (∀ index, index ∉ support → (lowDataCut lower support data).ofLp.2 index = 0) := by
  constructor <;> intro index outside <;> change originalLpCut support _ index = 0 <;>
    rw [originalLpCut_apply, if_neg outside]

theorem lowDataCut_weighted (lower : ℝ) (support : Finset LowAnnularIndex)
    (data weighted : LowEnergyData lower) (coefficient : LowAnnularIndex → ℂ)
    (bulkActual : ∀ index, weighted.ofLp.1 index = coefficient index • data.ofLp.1 index)
    (incomingActual : ∀ index, weighted.ofLp.2 index = coefficient index • data.ofLp.2 index) :
    (∀ index, (lowDataCut lower support weighted).ofLp.1 index = coefficient index • (lowDataCut lower support data).ofLp.1 index) ∧
    (∀ index, (lowDataCut lower support weighted).ofLp.2 index = coefficient index • (lowDataCut lower support data).ofLp.2 index) :=
  ⟨originalLpCut_weighted support data.ofLp.1 weighted.ofLp.1 coefficient bulkActual,
    originalLpCut_weighted support data.ofLp.2 weighted.ofLp.2 coefficient incomingActual⟩

end Grad.AnnularLowOrbit

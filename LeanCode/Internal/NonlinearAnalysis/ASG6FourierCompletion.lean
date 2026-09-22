import ASG5FaithfulWeightedGraph

noncomputable section

set_option maxHeartbeats 800000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- AH10's complete two-frequency source graph. Polynomial and original
phase factors are absorbed only by the explicit coefficient normalization. -/
abbrev AnnularSourceH1 (_parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (_angular _cell : ℕ) := lp (fun _ : ℤ × ℤ => WeightedRadialH1 dimension lower) 2

def sourceModeSingle (dimension : ℕ) (lower : ℝ) (mode : ℤ × ℤ) :
    WeightedRadialH1 dimension lower →L[ℝ]
      lp (fun _ : ℤ × ℤ => WeightedRadialH1 dimension lower) 2 :=
  lp.singleContinuousLinearMap ℝ (fun _ : ℤ × ℤ => WeightedRadialH1 dimension lower) 2 mode

/-- Finite Fourier fields with genuine infinitely smooth radial modes. -/
def finiteSourceCore (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ) (angular cell : ℕ) :
    ((ℤ × ℤ) →₀ SmoothRadialCore dimension) →ₗ[ℝ] AnnularSourceH1 parameters dimension lower angular cell :=
  Finsupp.lsum ℝ (fun mode => (sourceModeSingle dimension lower mode).toLinearMap.comp
    (weightedRadialCoreInto dimension lower))

theorem finiteSourceCore_single (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (angular cell : ℕ) (mode : ℤ × ℤ) (core : SmoothRadialCore dimension) :
    finiteSourceCore parameters dimension lower angular cell (Finsupp.single mode core) =
      sourceModeSingle dimension lower mode (weightedRadialCoreInto dimension lower core) := by
  rw [finiteSourceCore, Finsupp.lsum_single]
  rfl

theorem finiteSourceCore_apply (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (angular cell : ℕ) (core : (ℤ × ℤ) →₀ SmoothRadialCore dimension) (mode : ℤ × ℤ) :
    finiteSourceCore parameters dimension lower angular cell core mode =
      weightedRadialCoreInto dimension lower (core mode) := by
  classical
  rw [finiteSourceCore, Finsupp.lsum_apply, Finsupp.sum, lp.coeFn_sum, Finset.sum_apply]
  change (∑ other ∈ core.support,
    (lp.single 2 other (weightedRadialCoreInto dimension lower (core other)) :
      AnnularSourceH1 parameters dimension lower angular cell) mode) = _
  simp only [lp.single_apply, Pi.single_apply]
  rw [Finset.sum_eq_single mode]
  · simp only [ite_true]
  · intro other _ different
    exact if_neg (Ne.symm different)
  · intro missing
    rw [Finsupp.notMem_support_iff.mp missing, map_zero]
    simp

theorem finiteSourceCore_denseRange (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (angular cell : ℕ) : DenseRange (finiteSourceCore parameters dimension lower angular cell) := by
  let subspace := (LinearMap.range (finiteSourceCore parameters dimension lower angular cell)).topologicalClosure
  have singleMember (mode : ℤ × ℤ) (field : WeightedRadialH1 dimension lower) :
      sourceModeSingle dimension lower mode field ∈ subspace := by
    apply isClosed_property (weightedRadialCoreInto_denseRange dimension lower)
      ((LinearMap.range (finiteSourceCore parameters dimension lower angular cell)).isClosed_topologicalClosure.preimage
        (sourceModeSingle dimension lower mode).continuous) _ field
    intro core
    apply Submodule.le_topologicalClosure
    exact ⟨Finsupp.single mode core, finiteSourceCore_single parameters dimension lower angular cell mode core⟩
  have closureTop : subspace = ⊤ := by
    apply top_unique
    intro field _
    have convergence : HasSum (fun mode : ℤ × ℤ => sourceModeSingle dimension lower mode (field mode)) field :=
      lp.hasSum_single (by norm_num) field
    apply (LinearMap.range (finiteSourceCore parameters dimension lower angular cell)).isClosed_topologicalClosure.mem_of_tendsto convergence
    exact Filter.Eventually.of_forall (fun support => subspace.sum_mem (fun mode _ => singleMember mode (field mode)))
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr closureTop

theorem annularSource_norm_sq (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (angular cell : ℕ) (field : AnnularSourceH1 parameters dimension lower angular cell) :
    ‖field‖ ^ 2 = ∑' mode : ℤ × ℤ,
      (‖weightedRadialCoordinate dimension lower 0 (field mode)‖ ^ 2 +
        ‖weightedRadialCoordinate dimension lower 1 (field mode)‖ ^ 2) := by
  have formula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at formula
  rw [formula]
  apply tsum_congr
  intro mode
  exact weightedRadialH1_norm_sq dimension lower (field mode)

end Grad.AnnularSourceGraph

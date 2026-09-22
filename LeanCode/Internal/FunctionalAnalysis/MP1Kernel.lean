import MP1Interface

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open scoped ContDiff

namespace Grad.Mollifier.Pointwise

universe valueUniverse

theorem orderedDerivative_contDiff {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (rank : ℕ) (word : Word rank) (function : Spatial → Value)
    (smoothness : ContDiff ℝ ∞ function) : ContDiff ℝ ∞ (orderedDerivative rank word function) := by
  have smoothDerivatives : ContDiff ℝ ∞ (iteratedFDeriv ℝ rank function) :=
    smoothness.iteratedFDeriv_right (by
      exact_mod_cast (le_top : (⊤ : ℕ∞) + (rank : ℕ∞) ≤ ⊤))
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin rank => Spatial) Value
    (fun position => spatialDirection (word position))).contDiff.comp smoothDerivatives

theorem orderedDerivative_compactSupport {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (rank : ℕ) (word : Word rank) (function : Spatial → Value)
    (compactSupport : HasCompactSupport function) : HasCompactSupport (orderedDerivative rank word function) :=
  (compactSupport.iteratedFDeriv (𝕜 := ℝ) rank).comp_left
    (g := fun tensor : ContinuousMultilinearMap ℝ (fun _ : Fin rank => Spatial) Value =>
      tensor (fun position => spatialDirection (word position))) rfl

theorem orderedDerivative_support {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (rank : ℕ) (word : Word rank) (function : Spatial → Value) :
    tsupport (orderedDerivative rank word function) ⊆ tsupport function :=
  (tsupport_comp_subset
    (g := fun tensor : ContinuousMultilinearMap ℝ (fun _ : Fin rank => Spatial) Value =>
      tensor (fun position => spatialDirection (word position))) rfl
    (iteratedFDeriv ℝ rank function)).trans (tsupport_iteratedFDeriv_subset rank)

theorem orderedDerivative_zero {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (word : Word 0) (function : Spatial → Value) :
    orderedDerivative 0 word function = function := by
  funext point
  exact iteratedFDeriv_zero_apply _

theorem orderedDerivative_succ {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (rank : ℕ) (word : Word (rank + 1)) (function : Spatial → Value)
    (smoothness : ContDiff ℝ ∞ function) (point : Spatial) :
    orderedDerivative (rank + 1) word function point =
      fderiv ℝ (orderedDerivative rank (Fin.tail word) function) point (spatialDirection (word 0)) := by
  have differentiable := smoothness.differentiable_iteratedFDeriv
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl rank)
  exact (differentiable point).iteratedFDeriv_succ_apply_left'

theorem kernelDerivativeGoal : KernelDerivativeGoal := by
  intro kernel smoothness compactSupport rank word
  have smooth := orderedDerivative_contDiff rank word kernel smoothness
  have compact := orderedDerivative_compactSupport rank word kernel compactSupport
  exact ⟨smooth, compact, orderedDerivative_support rank word kernel,
    smooth.continuous.integrable_of_hasCompactSupport compact⟩

theorem localGoal : LocalGoal := by
  intro Value _normed _inner _complete field
  have membership : MemLp (field : Spatial → Value) 2 volume := by
    simpa only [Measure.restrict_univ] using Lp.memLp field
  exact membership.locallyIntegrable (by norm_num)

theorem independenceGoal : IndependenceGoal := by
  intro Value _normed _inner _complete kernel field representative represented
  funext point
  apply integral_congr_ae
  filter_upwards [represented] with source same
  rw [same]

end Grad.Mollifier.Pointwise

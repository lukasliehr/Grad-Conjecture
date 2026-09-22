import ProductInterface
import AW1Submultiplicative
import AW3Exponential

noncomputable section

open scoped BigOperators ContDiff

namespace Grad.NonlinearProduct

open Grad.ClosedJets Grad.CartesianState Grad.AnalyticWeights

theorem subadditive_nonempty_sum {Index : Type*} [DecidableEq Index]
    (function : ℤ → ℝ) (subadditive : ∀ first second, function (first + second) ≤ function first + function second)
    (indices : Finset Index) (nonempty : indices.Nonempty) (cells : Index → ℤ) :
    function (∑ index ∈ indices, cells index) ≤ ∑ index ∈ indices, function (cells index) := by
  induction indices using Finset.induction with
  | empty => simp at nonempty
  | @insert index rest indexNotIn inductionHypothesis =>
    by_cases restNonempty : rest.Nonempty
    · rw [Finset.sum_insert indexNotIn, Finset.sum_insert indexNotIn]
      exact (subadditive _ _).trans (add_le_add le_rfl (inductionHypothesis restNonempty))
    · have restEmpty := Finset.not_nonempty_iff_eq_empty.mp restNonempty
      subst rest
      simp

def productFrequency {arity : ℕ} (cells : Fin arity → ℤ) : ℝ :=
  ∑ index, cellFrequency (cells index)

theorem productFrequency_nonnegative {arity : ℕ} (cells : Fin arity → ℤ) :
    0 ≤ productFrequency cells := Finset.sum_nonneg (fun _ _ => (cellFrequency_pos _).le)

theorem cellFrequency_sum_le {arity : ℕ} (positiveArity : 0 < arity) (cells : Fin arity → ℤ) :
    cellFrequency (∑ index, cells index) ≤ productFrequency cells := by
  exact subadditive_nonempty_sum cellFrequency cellWeight_add_le Finset.univ
    ⟨⟨0, positiveArity⟩, Finset.mem_univ _⟩ cells

def productPhaseDefect {arity : ℕ} (parameters : PhaseParameters) (cells : Fin arity → ℤ)
    (point : SpatialPlane) : ℝ :=
  cartesianPhase parameters (∑ index, cells index) point -
    ∑ index, cartesianPhase parameters (cells index) point

def productDefectMultiplier {arity : ℕ} (parameters : PhaseParameters) (cells : Fin arity → ℤ)
    (point : SpatialPlane) : ℝ := Real.exp (productPhaseDefect parameters cells point)

theorem productPhaseDefect_smooth {arity : ℕ} (parameters : PhaseParameters) (cells : Fin arity → ℤ) :
    ContDiff ℝ ∞ (productPhaseDefect parameters cells) := by
  have eachSmooth : ∀ index, ContDiff ℝ ∞ (cartesianPhase parameters (cells index)) :=
    fun _ => cartesianPhase_contDiff _ _
  have outputSmooth := cartesianPhase_contDiff parameters (∑ index, cells index)
  unfold productPhaseDefect
  fun_prop

theorem productDefectMultiplier_smooth {arity : ℕ} (parameters : PhaseParameters) (cells : Fin arity → ℤ) :
    ContDiff ℝ ∞ (productDefectMultiplier parameters cells) :=
  (productPhaseDefect_smooth parameters cells).exp

theorem productPhaseDefect_nonpositive {arity : ℕ} (positiveArity : 0 < arity)
    (parameters : PhaseParameters) (cells : Fin arity → ℤ) (point : ClosedDisk) :
    productPhaseDefect parameters cells point.val ≤ 0 := by
  have rateNonnegative : 0 ≤ rate parameters.sigma0 parameters.gamma ‖point.val‖ := by
    have radiusBound : ‖point.val‖ ≤ 1 := point.property
    have widthBound := parameters_gamma_lt_sigma0 parameters
    unfold rate
    nlinarith [parameters.gamma_pos]
  have bound := subadditive_nonempty_sum (phase parameters.sigma0 parameters.gamma ‖point.val‖)
    (fun first second => phase_subadditive parameters.sigma0 parameters.gamma ‖point.val‖ first second
      parameters.gamma_pos.le (norm_nonneg _) rateNonnegative)
    Finset.univ ⟨⟨0, positiveArity⟩, Finset.mem_univ _⟩ cells
  apply sub_nonpos.mpr
  simpa only [cartesianPhase, Calculus.physicalPhase, one_mul] using bound

theorem productDefectMultiplier_le_one {arity : ℕ} (positiveArity : 0 < arity)
    (parameters : PhaseParameters) (cells : Fin arity → ℤ) (point : ClosedDisk) :
    productDefectMultiplier parameters cells point.val ≤ 1 :=
  Real.exp_le_one_iff.mpr (productPhaseDefect_nonpositive positiveArity parameters cells point)

end Grad.NonlinearProduct

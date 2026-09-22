import AKDN19JointWeightedEulerInduction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
namespace Grad.OriginalCartesianTameEstimate

section Linear
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem vectorEulerWithin_pair (domain : Set ℝ) (unique : UniqueDiffOn ℝ domain)
    (first : ℝ → E) (second : ℝ → F) (rank : ℕ)
    (firstSmooth : ContDiffOn ℝ rank first domain) (secondSmooth : ContDiffOn ℝ rank second domain)
    (radius : ℝ) (inside : radius ∈ domain) :
    vectorEulerWithinIteratedDerivative domain rank (fun point => (first point,second point)) radius =
      (vectorEulerWithinIteratedDerivative domain rank first radius,
        vectorEulerWithinIteratedDerivative domain rank second radius) := by
  apply Prod.ext
  · exact (vectorEulerWithin_observation domain unique (fun point => (first point,second point))
      (ContinuousLinearMap.fst ℝ E F) rank (firstSmooth.prodMk secondSmooth) inside).symm
  · exact (vectorEulerWithin_observation domain unique (fun point => (first point,second point))
      (ContinuousLinearMap.snd ℝ E F) rank (firstSmooth.prodMk secondSmooth) inside).symm

theorem vectorEulerWithin_add (domain : Set ℝ) (unique : UniqueDiffOn ℝ domain)
    (first second : ℝ → E) (rank : ℕ)
    (firstSmooth : ContDiffOn ℝ rank first domain) (secondSmooth : ContDiffOn ℝ rank second domain)
    (radius : ℝ) (inside : radius ∈ domain) :
    vectorEulerWithinIteratedDerivative domain rank (fun point => first point+second point) radius =
      vectorEulerWithinIteratedDerivative domain rank first radius+
        vectorEulerWithinIteratedDerivative domain rank second radius := by
  let addition := ContinuousLinearMap.fst ℝ E E+ContinuousLinearMap.snd ℝ E E
  have observed := vectorEulerWithin_observation domain unique (fun point => (first point,second point))
    addition rank (firstSmooth.prodMk secondSmooth) inside
  change vectorEulerWithinIteratedDerivative domain rank (fun point => first point+second point) radius = _ at observed
  dsimp only at observed
  rw [vectorEulerWithin_pair domain unique first second rank firstSmooth secondSmooth radius inside] at observed
  exact observed

theorem vectorEulerWithin_right (domain : Set ℝ) (field : ℝ → E) (rank : ℕ) :
    vectorEulerWithinIteratedDerivative domain rank (vectorEulerWithinIteratedDerivative domain 1 field) =
      vectorEulerWithinIteratedDerivative domain (rank+1) field := by
  induction rank with
  | zero => rfl
  | succ rank previous =>
      change (fun point => point • derivWithin
        (vectorEulerWithinIteratedDerivative domain rank (vectorEulerWithinIteratedDerivative domain 1 field)) domain point) = _
      rw [previous]
      rfl

theorem vectorEulerWithin_observation_norm (domain : Set ℝ) (unique : UniqueDiffOn ℝ domain)
    (field : ℝ → E) (observe : E →L[ℝ] F) (rank : ℕ) (smooth : ContDiffOn ℝ rank field domain)
    (radius : ℝ) (inside : radius ∈ domain) :
    ‖vectorEulerWithinIteratedDerivative domain rank (fun point => observe (field point)) radius‖ ≤
      ‖observe‖*‖vectorEulerWithinIteratedDerivative domain rank field radius‖ := by
  rw [vectorEulerWithin_observation domain unique field observe rank smooth inside]
  exact observe.le_opNorm _

end Linear
end Grad.OriginalCartesianTameEstimate

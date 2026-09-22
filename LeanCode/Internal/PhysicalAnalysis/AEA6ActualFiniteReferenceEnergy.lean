import AEA5LiteralWeightedEnergyDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularLowReference
open Grad.AnnularLowEnergy Grad.AnnularVariational Grad.PhaseAlgebra
open Grad.CartesianState

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem lowForcing_young (eta : ℝ) (positive : 0 < eta) (field forcing : E) :
    2 * inner ℝ field forcing ≤ (eta / 4) * ‖field‖ ^ 2 + (4 / eta) * ‖forcing‖ ^ 2 := by
  have comparison := Grad.BoundaryTrace.frequency_young (eta / 4) ‖field‖ ‖forcing‖ (by positivity)
  have inverse : (eta / 4)⁻¹ = 4 / eta := by field_simp
  rw [inverse] at comparison
  have innerBound := real_inner_le_norm field forcing
  exact (by nlinarith : 2 * inner ℝ field forcing ≤ 2 * ‖field‖ * ‖forcing‖).trans comparison

/-- Uniform reference weighted energy inequality, with stronger eta/2 margin
before the current coefficient error consumes its own quarter. -/
theorem lowPairEnergySlope_bound (parameters : PhaseParameters) (length radius : ℝ)
    (lengthPositive : 0 < length) (mode : LowAnnularMode) (positive : 0 < radius)
    (first second forcingFirst forcingSecond : E) :
    lowPairEnergySlope parameters length radius mode first second forcingFirst forcingSecond +
      (lowEta length parameters.gamma / 2) * radius ^ (-(7 / 2 : ℝ)) * (‖first‖ ^ 2 + ‖second‖ ^ 2) ≤
      (4 / lowEta length parameters.gamma) * radius ^ (-(7 / 2 : ℝ)) * (‖forcingFirst‖ ^ 2 + ‖forcingSecond‖ ^ 2) := by
  have etaPositive := lowEta_pos length parameters.gamma lengthPositive parameters.gamma_pos
  have weightNonnegative := (Real.rpow_pos_of_pos positive (-(7 / 2 : ℝ))).le
  have reference := mul_le_mul_of_nonneg_left
    (lowReference_weighted_coercivity parameters length radius lengthPositive mode positive first second) weightNonnegative
  have firstForce := mul_le_mul_of_nonneg_left (lowForcing_young _ etaPositive first forcingFirst) weightNonnegative
  have secondForce := mul_le_mul_of_nonneg_left (lowForcing_young _ etaPositive second forcingSecond) weightNonnegative
  rw [lowPairEnergySlope_forcing parameters length radius mode positive]
  linear_combination reference + firstForce + secondForce

/-- The energy is the literal finite sum of rho mu^-1 over original low modes.
No positive angular mode or nonzero axial-cell restriction is inserted. -/
def lowFiniteEnergy (length radius : ℝ) (support : Finset LowAnnularMode)
    (first second : LowAnnularMode → E) : ℝ :=
  ∑ mode ∈ support, lowPairEnergy length radius mode (first mode) (second mode)

theorem lowFiniteEnergy_hasDerivAt (parameters : PhaseParameters) (length radius : ℝ)
    (support : Finset LowAnnularMode) (positive : 0 < radius)
    (first second : LowAnnularMode → ℝ → E) (forcingFirst forcingSecond : LowAnnularMode → E)
    (firstDerivative : ∀ mode ∈ support, HasDerivAt (first mode)
      (lowReferenceFirst parameters length radius mode (first mode radius) (second mode radius) +
        lowMu length radius mode.val.2 • forcingFirst mode) radius)
    (secondDerivative : ∀ mode ∈ support, HasDerivAt (second mode)
      (lowReferenceSecond parameters length radius mode (first mode radius) (second mode radius) +
        lowMu length radius mode.val.2 • forcingSecond mode) radius) :
    HasDerivAt (fun point => lowFiniteEnergy length point support (fun mode => first mode point) (fun mode => second mode point))
      (∑ mode ∈ support, lowPairEnergySlope parameters length radius mode
        (first mode radius) (second mode radius) (forcingFirst mode) (forcingSecond mode)) radius := by
  have result := HasDerivAt.sum (fun mode member => lowPairEnergy_hasDerivAt parameters length radius mode positive
    (first mode) (second mode) (forcingFirst mode) (forcingSecond mode) (firstDerivative mode member) (secondDerivative mode member))
  have equality : (∑ mode ∈ support, fun point => lowPairEnergy length point mode (first mode point) (second mode point)) =
      (fun point => lowFiniteEnergy length point support (fun mode => first mode point) (fun mode => second mode point)) := by
    funext point
    simp only [Finset.sum_apply, lowFiniteEnergy]
  rw [equality] at result
  exact result

/-- Actual finite-system differential estimate in the exact BE18 norm.
All constants depend only on L and the original phase, never on ell or cutoff. -/
theorem lowFiniteEnergy_derivative_bound (parameters : PhaseParameters) (length radius : ℝ)
    (lengthPositive : 0 < length) (support : Finset LowAnnularMode) (positive : 0 < radius)
    (first second : LowAnnularMode → ℝ → E) (forcingFirst forcingSecond : LowAnnularMode → E)
    (firstDerivative : ∀ mode ∈ support, HasDerivAt (first mode)
      (lowReferenceFirst parameters length radius mode (first mode radius) (second mode radius) +
        lowMu length radius mode.val.2 • forcingFirst mode) radius)
    (secondDerivative : ∀ mode ∈ support, HasDerivAt (second mode)
      (lowReferenceSecond parameters length radius mode (first mode radius) (second mode radius) +
        lowMu length radius mode.val.2 • forcingSecond mode) radius) :
    deriv (fun point => lowFiniteEnergy length point support (fun mode => first mode point) (fun mode => second mode point)) radius +
      (lowEta length parameters.gamma / 2) * radius ^ (-(7 / 2 : ℝ)) *
        (∑ mode ∈ support, (‖first mode radius‖ ^ 2 + ‖second mode radius‖ ^ 2)) ≤
      (4 / lowEta length parameters.gamma) * radius ^ (-(7 / 2 : ℝ)) *
        (∑ mode ∈ support, (‖forcingFirst mode‖ ^ 2 + ‖forcingSecond mode‖ ^ 2)) := by
  rw [(lowFiniteEnergy_hasDerivAt parameters length radius support positive first second forcingFirst forcingSecond
    firstDerivative secondDerivative).deriv]
  have estimates := Finset.sum_le_sum (fun mode (_member : mode ∈ support) =>
    lowPairEnergySlope_bound parameters length radius lengthPositive mode positive
      (first mode radius) (second mode radius) (forcingFirst mode) (forcingSecond mode))
  rw [Finset.sum_add_distrib] at estimates
  rw [← Finset.mul_sum, ← Finset.mul_sum] at estimates
  exact estimates

end Hilbert
end Grad.AnnularLowReference

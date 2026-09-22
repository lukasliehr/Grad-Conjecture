import GC18APClosure
import FC5Definite

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.AnalyticWeights.Calculus

def apFiniteEmbed {dimension grade : ℕ} (L sigma gamma ell : ℝ) :
    (ℤ →₀ ClosedJet dimension) →ₗ[ℂ] APAmbient dimension grade :=
  Finsupp.lsum ℂ (fun cell => (apCellInjectionLinear dimension grade cell).comp
    (apRowLinear L sigma gamma ell cell))

theorem apFiniteEmbed_single {dimension grade : ℕ} (L sigma gamma ell : ℝ)
    (cell : ℤ) (field : ClosedJet dimension) :
    apFiniteEmbed (grade := grade) L sigma gamma ell (Finsupp.single cell field) = apSingle L sigma gamma ell cell field := by
  rw [apFiniteEmbed, Finsupp.lsum_single]
  rfl

theorem apFiniteEmbed_apply {dimension grade : ℕ} (L sigma gamma ell : ℝ)
    (field : ℤ →₀ ClosedJet dimension) (cell : ℤ) :
    apFiniteEmbed (grade := grade) L sigma gamma ell field cell = apRowLinear L sigma gamma ell cell (field cell) := by
  classical
  rw [apFiniteEmbed, Finsupp.lsum_apply, Finsupp.sum, lp.coeFn_sum, Finset.sum_apply]
  change (∑ other ∈ field.support,
    (lp.single 2 other (apRowLinear L sigma gamma ell other (field other)) : APAmbient dimension grade) cell) = _
  simp only [lp.single_apply, Pi.single_apply]
  rw [Finset.sum_eq_single cell]
  · simp only [ite_true]
  · intro other _ different
    exact if_neg (Ne.symm different)
  · intro missing
    rw [Finsupp.notMem_support_iff.mp missing, map_zero]
    simp

theorem apRowLinear_injective {dimension grade : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ) :
    Function.Injective (apRowLinear (dimension := dimension) (grade := grade) L sigma gamma ell cell) := by
  intro first second equality
  have zeroCoordinate := congrArg (fun row : APRow dimension grade => row (zeroGradeIndex grade)) equality
  rw [apRowLinear_apply, apRowLinear_apply] at zeroCoordinate
  have powerNonzero : (scaledCellWeight L ell cell : ℂ) ^ grade ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le zero_lt_one (scaledCellWeight_one_le L ell cell)).ne')
  change (scaledCellWeight L ell cell : ℂ) ^ grade • closedContinuousToDiskL2 (closedMultiDerivative (apWeightedJet sigma gamma ell cell first) (0, 0)) =
    (scaledCellWeight L ell cell : ℂ) ^ grade • closedContinuousToDiskL2 (closedMultiDerivative (apWeightedJet sigma gamma ell cell second) (0, 0)) at zeroCoordinate
  rw [closedMultiDerivative_zero, closedMultiDerivative_zero] at zeroCoordinate
  have l2Equality := (smul_right_injective _ powerNonzero) zeroCoordinate
  have valueEquality : (apWeightedJet sigma gamma ell cell first).value = (apWeightedJet sigma gamma ell cell second).value := by
    apply sub_eq_zero.mp
    apply closedContinuousToDiskL2_eq_zero
    change apClosedL2Linear dimension ((apWeightedJet sigma gamma ell cell first).value -
      (apWeightedJet sigma gamma ell cell second).value) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr l2Equality
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have pointEquality := congrArg (fun value : C(ClosedDisk, ComplexEuclidean dimension) => value point) valueEquality
  rw [apWeightedJet_value, apWeightedJet_value] at pointEquality
  have positive : 0 < originalWeight sigma gamma ell cell point.val := by rw [originalWeight, physicalWeight_exp]; positivity
  exact (smul_right_injective _ positive.ne') pointEquality

theorem apFiniteEmbed_injective {dimension grade : ℕ} (L sigma gamma ell : ℝ) :
    Function.Injective (apFiniteEmbed (dimension := dimension) (grade := grade) L sigma gamma ell) := by
  intro first second equality
  apply Finsupp.ext
  intro cell
  apply apRowLinear_injective (grade := grade) L sigma gamma ell cell
  rw [← apFiniteEmbed_apply, ← apFiniteEmbed_apply, equality]

theorem apFiniteEmbed_range {dimension grade : ℕ} (L sigma gamma ell : ℝ) :
    LinearMap.range (apFiniteEmbed (dimension := dimension) (grade := grade) L sigma gamma ell) =
      apSmoothCore L sigma gamma ell dimension grade := by
  apply le_antisymm
  · rintro _ ⟨field, rfl⟩
    rw [apFiniteEmbed, Finsupp.lsum_apply, Finsupp.sum]
    apply Submodule.sum_mem
    intro cell _
    exact Submodule.subset_span (Set.mem_range.mpr ⟨(cell, field cell), rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨cell, field⟩, rfl⟩
    exact ⟨Finsupp.single cell field, apFiniteEmbed_single L sigma gamma ell cell field⟩

end Grad.GaugeCoefficients.Physical.RadialLedger

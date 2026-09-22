import AKC16ConjugatedMatrixJetSeries
import AKC4FiniteGradeOperatorCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
open Set
open scoped BigOperators ENNReal Topology ContDiff
namespace Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.BoundaryLift Grad.AnnularKernelL2
open Grad.AnnularReconstruction Grad.AnnularKernelContinuity Grad.PhaseAlgebra Grad.AnnularRadialSmoothness

/-- Actual radial kernel jets with their original analytic moments give each
finite radial order at exactly the original width. Only order+4 polynomial
input degrees are reserved; the original kernel is unchanged. -/
theorem radialConjugatedAction_matrixJets {source target : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (kernels : ℕ → (radius : RadialPoint) → RadialKernel parameters radius source target)
    (coefficients : ℕ → ℝ → (ℤ × ℤ) → (ℤ × ℤ) →
      (ComplexEuclidean source →L[ℂ] ComplexEuclidean target))
    (same : ∀ rank radius shift input, (kernels rank radius).entry shift input = coefficients rank radius.val shift input)
    (derivative : ∀ rank shift input radius, HasDerivAt (fun point => coefficients rank point shift input)
      (coefficients (rank + 1) radius shift input) radius)
    (regular : ∀ rank, RegularKernelFamily (kernels rank)) (grade order : ℕ) :
    ContDiffOn ℝ order (radialConjugatedAction parameters lower positive bounded.le (kernels 0) grade (order + 4)) (Icc lower 1) := by
  have momentBounds : ∀ rank, ∃ constant : ℝ, 0 ≤ constant ∧ ∀ radius,
      fullKernelMoment (radialKernelParameters parameters radius) (grade + (order + 4)) (kernels rank radius) ≤ constant :=
    fun rank => (regular rank).2 (grade + (order + 4))
  choose constants nonnegative estimates using momentBounds
  have smooth : ∀ shift input, ContDiff ℝ ∞ (fun radius => coefficients 0 radius shift input) :=
    fun shift input => derivativeTower_smooth (fun rank radius => coefficients rank radius shift input)
      (fun rank radius => derivative rank shift input radius) 0
  let family := conjugatedMatrixJetTerm parameters grade (order + 4) (coefficients 0)
  let majorant := fun rank (index : (ℤ × ℤ) × (ℤ × ℤ)) => conjugatedJetConstant parameters constants rank *
    ((annularFrequency index.1.1 index.1.2 ^ 4)⁻¹ * (annularFrequency index.2.1 index.2.2 ^ 4)⁻¹)
  have summable : ∀ rank, Summable (majorant rank) := fun rank => latticeDoubleDecay_summable.mul_left _
  have bound : ∀ rank ≤ order, ∀ index radius, radius ∈ Icc lower 1 → ‖family rank index radius‖ ≤ majorant rank index := by
    intro rank valid index radius inside
    let actual : RadialPoint := ⟨radius, positive.le.trans inside.1, inside.2⟩
    apply (fourierMatrixPoint_bound _ _ _).trans
    exact conjugatedCoefficientJet_bound parameters grade order kernels coefficients same derivative constants nonnegative estimates
      rank valid index.1 index.2 actual
  have series : ContDiffOn ℝ order (fun radius => ∑' index, family 0 index radius) (Icc lower 1) :=
    intervalSeries_contDiffOn_order lower 1 bounded order family
      (fun rank _ index => (conjugatedMatrixJetTerm_continuous parameters grade (order + 4) (coefficients 0) smooth rank index).continuousOn)
      (fun rank _ index radius _ => conjugatedMatrixJetTerm_hasDerivAt parameters grade (order + 4) (coefficients 0) smooth rank index radius)
      majorant (fun rank _ => summable rank) bound
  apply series.congr
  intro radius inside
  let actual := collarRadius lower positive bounded.le radius
  have actualValue : actual.val = radius := collarRadius_literal lower positive bounded.le radius inside
  have sameTerm (index : (ℤ × ℤ) × (ℤ × ℤ)) :
      family 0 index radius = conjugatedMatrixPoint parameters grade (order + 4) actual (kernels 0 actual) index := by
    change fourierMatrixPoint _ _ (conjugatedCoefficientJet parameters grade (order + 4) (coefficients 0) 0 index.1 index.2 radius) = _
    rw [conjugatedCoefficientJet_zero]
    simp only [conjugatedMatrixPoint, same, actualValue]
  have termsSummable : Summable (conjugatedMatrixPoint parameters grade (order + 4) actual (kernels 0 actual)) :=
    (Summable.of_norm_bounded (summable 0) (fun index => bound 0 (Nat.zero_le order) index radius inside)).congr sameTerm
  change conjugatedKernelAction parameters grade (order + 4) actual (kernels 0 actual) = _
  rw [conjugatedKernelAction_matrixSeries parameters grade (order + 4) actual (kernels 0 actual) termsSummable]
  exact tsum_congr (fun index => (sameTerm index).symm)

end Grad.AnnularWeightedSmoothness

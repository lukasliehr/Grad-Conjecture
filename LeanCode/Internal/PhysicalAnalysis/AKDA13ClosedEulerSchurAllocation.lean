import AKDA12ClosedEulerLeibnizAllocation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
open Set
open scoped ContDiff BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.AnnularKernelL2 Grad.AnnularVariational
open Grad.AnnularWeightedSmoothness

theorem eulerAllocationSum_mono (first second : ℕ → ℕ → ℝ) (terms : List (ℕ × ℕ))
    (bound : ∀ term ∈ terms, first term.1 term.2 ≤ second term.1 term.2) :
    eulerAllocationSum first terms ≤ eulerAllocationSum second terms := by
  induction terms with
  | nil => exact le_rfl
  | cons term terms previous =>
      exact add_le_add (bound term List.mem_cons_self)
        (previous (fun item member => bound item (List.mem_cons_of_mem term member)))

theorem eulerAllocationSum_mul_left (scalar : ℝ) (values : ℕ → ℕ → ℝ) (terms : List (ℕ × ℕ)) :
    scalar*eulerAllocationSum values terms = eulerAllocationSum (fun first second => scalar*values first second) terms := by
  induction terms with
  | nil => exact mul_zero _
  | cons term terms previous =>
      change scalar*(values term.1 term.2+eulerAllocationSum values terms) =
        scalar*values term.1 term.2+eulerAllocationSum (fun first second => scalar*values first second) terms
      rw [mul_add,previous]

theorem eulerAllocationSum_summable {Index : Type*} (values : ℕ → ℕ → Index → ℝ)
    (summable : ∀ first second, Summable (values first second)) (terms : List (ℕ × ℕ)) :
    Summable (fun index => eulerAllocationSum (fun first second => values first second index) terms) := by
  induction terms with
  | nil => exact summable_zero
  | cons term terms previous => exact (summable term.1 term.2).add previous

theorem eulerAllocationSum_tsum {Index : Type*} (values : ℕ → ℕ → Index → ℝ)
    (summable : ∀ first second, Summable (values first second)) (terms : List (ℕ × ℕ)) :
    (∑' index, eulerAllocationSum (fun first second => values first second index) terms) =
      eulerAllocationSum (fun first second => ∑' index, values first second index) terms := by
  induction terms with
  | nil => exact tsum_zero
  | cons term terms previous =>
      change (∑' (index : Index), (values term.1 term.2 index+eulerAllocationSum (fun first second => values first second index) terms)) =
        (∑' (index : Index), values term.1 term.2 index)+eulerAllocationSum (fun first second => ∑' index, values first second index) terms
      rw [Summable.tsum_add (summable term.1 term.2) (eulerAllocationSum_summable values summable terms),previous]

/-- Literal phase-conjugated Euler derivative on a closed original collar. -/
def actualClosedConjugatedEulerEntry {source target : ℕ} (parameters : PhaseParameters) (domain : Set ℝ)
    (coefficient : ℝ → (ℤ × ℤ) → (ℤ × ℤ) → (ComplexEuclidean source →L[ℂ] ComplexEuclidean target))
    (rank : ℕ) (radius : ℝ) (shift input : ℤ × ℤ) : ComplexEuclidean source →L[ℂ] ComplexEuclidean target :=
  vectorEulerWithinIteratedDerivative domain rank (fun point =>
    radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2 point • coefficient point shift input) radius

/-- Actual closed-collar Schur allocation. The scalar Euler derivative
charges only the displacement moment, and the remaining rank belongs
to the SAME kernel derivative tower. -/
theorem actualClosedEulerDisplacementMoment_allocated {source target : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (kernels : ℕ → (radius : RadialPoint) → RadialKernel parameters radius source target)
    (derivative : ∀ order point, point ∈ Icc lower 1 → ∀ shift input,
      HasDerivWithinAt (fun location => (kernels order (collarRadius lower positive bounded.le location)).entry shift input)
        (point⁻¹ • (kernels (order+1) (collarRadius lower positive bounded.le point)).entry shift input) (Icc lower 1) point)
    (radius : RadialPoint) (inside : radius.val ∈ Icc lower 1) (rank moment : ℕ)
    (inputs : (ℤ × ℤ) → (ℤ × ℤ)) :
    let coefficient := fun point => (kernels 0 (collarRadius lower positive bounded.le point)).entry
    Summable (fun shift : ℤ × ℤ => Grad.AnnularVariational.annularFrequency shift.1 shift.2^moment *
      ‖actualClosedConjugatedEulerEntry parameters (Icc lower 1) coefficient rank radius.val shift (inputs shift)‖) ∧
    (∑' shift : ℤ × ℤ, Grad.AnnularVariational.annularFrequency shift.1 shift.2^moment *
      ‖actualClosedConjugatedEulerEntry parameters (Icc lower 1) coefficient rank radius.val shift (inputs shift)‖) ≤
      eulerAllocationSum (fun first second => positiveEulerRatioConstant parameters first *
        fullKernelMoment (radialKernelParameters parameters radius) (moment+first) (kernels second radius)) (eulerLeibnizTerms rank) := by
  dsimp only
  have nonzero : ∀ point ∈ Icc lower 1, point ≠ 0 := fun point member => (positive.trans_le member.1).ne'
  have sameRadius : collarRadius lower positive bounded.le radius.val = radius :=
    Subtype.ext (collarRadius_literal lower positive bounded.le radius.val inside)
  let envelope := fun first second (shift : ℤ × ℤ) => positiveEulerRatioConstant parameters first *
    (boundaryCoefficientPhaseCost (radialKernelParameters parameters radius) shift *
      Grad.AnnularVariational.annularFrequency shift.1 shift.2^(moment+first) * (kernels second radius).entryNorm shift)
  have envelopeSummable (first second : ℕ) : Summable (envelope first second) :=
    ((kernels second radius).moments (moment+first)).mul_left (positiveEulerRatioConstant parameters first)
  have bound (shift : ℤ × ℤ) : Grad.AnnularVariational.annularFrequency shift.1 shift.2^moment *
      ‖actualClosedConjugatedEulerEntry parameters (Icc lower 1)
        (fun point => (kernels 0 (collarRadius lower positive bounded.le point)).entry) rank radius.val shift (inputs shift)‖ ≤
      eulerAllocationSum (fun first second => envelope first second shift) (eulerLeibnizTerms rank) := by
    let scalar := fun order => eulerIteratedDerivative order
      (radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm (inputs shift)).2 (inputs shift).2)
    let vector := fun order point => (kernels order (collarRadius lower positive bounded.le point)).entry shift (inputs shift)
    have fidelity := scalarEulerPolynomial_fidelity (Icc lower 1) (uniqueDiffOn_Icc bounded) nonzero scalar vector
      (fun order point member => actualScalarEulerJets_hasDerivWithinAt (Icc lower 1) _
        (radialPhaseRatio_smooth parameters _ _) order point (nonzero point member))
      (fun order point member => derivative order point member shift (inputs shift)) rank radius.val inside
    change Grad.AnnularVariational.annularFrequency shift.1 shift.2^moment *
      ‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank (fun point => scalar 0 point • vector 0 point) radius.val‖ ≤ _
    rw [fidelity]
    apply (mul_le_mul_of_nonneg_left (scalarEulerPolynomial_norm scalar vector _ radius.val)
      (pow_nonneg (annularFrequency_pos shift).le moment)).trans
    rw [eulerAllocationSum_mul_left]
    apply eulerAllocationSum_mono
    intro term _
    have phase := radialPhaseRatio_euler_displacement parameters term.1 shift (inputs shift) radius
    have ratio := bulkPhase_ratio_le parameters radius shift ((twoFrequencyTranslation shift).symm (inputs shift))
    simp only [Equiv.apply_symm_apply] at ratio
    change radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm (inputs shift)).2 (inputs shift).2 radius.val ≤ _ at ratio
    have entry := (kernels term.2 radius).entry_le shift (inputs shift)
    have ratioEntry := mul_le_mul ratio entry (norm_nonneg _) (boundaryCoefficientPhaseCost_nonnegative _ _)
    have phaseEntry := mul_le_mul_of_nonneg_right phase (norm_nonneg (vector term.2 radius.val))
    dsimp only [vector] at phaseEntry
    rw [sameRadius] at phaseEntry
    have first0 : 0 ≤ positiveEulerRatioConstant parameters term.1 := zero_le_one.trans (positiveEulerRatioConstant_one_le _ _)
    have weight0 : 0 ≤ Grad.AnnularVariational.annularFrequency shift.1 shift.2^term.1 :=
      pow_nonneg (annularFrequency_pos shift).le term.1
    have joined := mul_le_mul_of_nonneg_left ratioEntry
      (mul_nonneg first0 weight0)
    have moment0 : 0 ≤ Grad.AnnularVariational.annularFrequency shift.1 shift.2^moment :=
      pow_nonneg (annularFrequency_pos shift).le moment
    have final := mul_le_mul_of_nonneg_left (phaseEntry.trans (by
      convert joined using 1; ring)) moment0
    dsimp only [scalar,vector,envelope]
    rw [sameRadius,pow_add]
    convert final using 1 <;> first | rfl | ring
  have totalSummable := eulerAllocationSum_summable envelope envelopeSummable (eulerLeibnizTerms rank)
  have actualSummable := Summable.of_nonneg_of_le
    (fun shift => mul_nonneg (pow_nonneg (annularFrequency_pos shift).le moment) (norm_nonneg _)) bound totalSummable
  refine ⟨actualSummable,?_⟩
  apply (actualSummable.tsum_le_tsum bound totalSummable).trans_eq
  rw [eulerAllocationSum_tsum envelope envelopeSummable]
  congr 1
  funext first second
  exact tsum_mul_left

end Grad.OriginalCartesianTameEstimate

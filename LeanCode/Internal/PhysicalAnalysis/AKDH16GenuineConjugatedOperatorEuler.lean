import AKDH15ActualConjugatedEntryObservation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.AnnularWeightedSmoothness Grad.AnnularRadialSmoothness

theorem vectorEulerWithin_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (domain : Set ℝ) (rank : ℕ) (first second : ℝ → E) (same : EqOn first second domain) :
    EqOn (vectorEulerWithinIteratedDerivative domain rank first)
      (vectorEulerWithinIteratedDerivative domain rank second) domain := by
  induction rank with
  | zero => exact same
  | succ rank previous =>
      intro radius inside
      change radius • derivWithin (vectorEulerWithinIteratedDerivative domain rank first) domain radius =
        radius • derivWithin (vectorEulerWithinIteratedDerivative domain rank second) domain radius
      rw [derivWithin_congr previous (previous inside)]

theorem scalarEulerPolynomial_map {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (mapping : E →L[ℝ] F)
    (scalar : ℕ → ℝ → ℝ) (vector : ℕ → ℝ → E) (terms : List (ℕ × ℕ)) (radius : ℝ) :
    scalarEulerPolynomial scalar (fun order point => mapping (vector order point)) terms radius =
      mapping (scalarEulerPolynomial scalar vector terms radius) := by
  induction terms with
  | nil => exact (map_zero mapping).symm
  | cons term terms previous =>
      change scalar term.1 radius • mapping (vector term.2 radius)+
        scalarEulerPolynomial scalar (fun order point => mapping (vector order point)) terms radius =
        mapping (scalar term.1 radius • vector term.2 radius+scalarEulerPolynomial scalar vector terms radius)
      rw [previous,map_add,map_smul]

theorem scalarEulerPolynomial_mapped_fidelity {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (domain : Set ℝ) (unique : UniqueDiffOn ℝ domain) (nonzero : ∀ radius ∈ domain, radius ≠ 0)
    (scalar : ℕ → ℝ → ℝ) (vector : ℕ → ℝ → E) (mapping : E →L[ℝ] F)
    (scalarDerivative : ∀ order radius, radius ∈ domain →
      HasDerivWithinAt (scalar order) (radius⁻¹ • scalar (order+1) radius) domain radius)
    (vectorDerivative : ∀ order radius, radius ∈ domain →
      HasDerivWithinAt (vector order) (radius⁻¹ • vector (order+1) radius) domain radius)
    (rank : ℕ) (radius : ℝ) (inside : radius ∈ domain) :
    vectorEulerWithinIteratedDerivative domain rank (fun point => scalar 0 point • mapping (vector 0 point)) radius =
      mapping (scalarEulerPolynomial scalar vector (eulerLeibnizTerms rank) radius) := by
  rw [scalarEulerPolynomial_fidelity domain unique nonzero scalar
    (fun order point => mapping (vector order point)) scalarDerivative ?_ rank radius inside,
    scalarEulerPolynomial_map]
  intro order point member
  have result := mapping.hasFDerivAt.comp_hasDerivWithinAt point (vectorDerivative order point member)
  simpa only [map_smul,Function.comp_def] using result

/-- Finite reserve is used only to identify the actual bounded derivative.
The resulting kernel is the sharp, same-phase Euler kernel of DH10. -/
theorem genuineConjugatedOperatorEuler {source target : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (kernels : ℕ → (radius : RadialPoint) → RadialKernel parameters radius source target)
    (tower : KernelEulerDerivativeTower parameters lower positive bounded.le kernels)
    (grade reserve rank : ℕ)
    (smooth : ContDiffOn ℝ rank
      (radialConjugatedAction parameters lower positive bounded.le (kernels 0) grade reserve) (Icc lower 1))
    (radius : RadialPoint) (inside : radius.val ∈ Icc lower 1) :
    vectorEulerWithinIteratedDerivative (Icc lower 1) rank
      (radialConjugatedAction parameters lower positive bounded.le (kernels 0) grade reserve) radius.val =
      conjugatedKernelAction parameters grade reserve radius
        (conjugatedEulerKernel parameters radius (fun order => kernels order radius) rank) := by
  apply fourierEntryObservation_ext
  intro output input
  let shift : ℤ × ℤ := (output.1-input.1,output.2-input.2)
  have outputSame : (twoFrequencyTranslation shift).symm input = output := by
    apply Prod.ext
    · change input.1+(output.1-input.1) = output.1
      omega
    · change input.2+(output.2-input.2) = output.2
      omega
  rw [← outputSame]
  let observe := (fourierEntryObservation (source := source) (target := target)
    ((twoFrequencyTranslation shift).symm input) input).restrictScalars ℝ
  have observation := vectorEulerWithin_observation (Icc lower 1) (uniqueDiffOn_Icc bounded)
    (radialConjugatedAction parameters lower positive bounded.le (kernels 0) grade reserve) observe rank smooth inside
  change _ = observe _ at observation
  change observe (vectorEulerWithinIteratedDerivative (Icc lower 1) rank
    (radialConjugatedAction parameters lower positive bounded.le (kernels 0) grade reserve) radius.val) =
    observe (conjugatedKernelAction parameters grade reserve radius
      (conjugatedEulerKernel parameters radius (fun order => kernels order radius) rank))
  rw [← observation]
  let scalar := fun order => eulerIteratedDerivative order
    (radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2)
  let vector := fun order point => (kernels order (collarRadius lower positive bounded.le point)).entry shift input
  let constant : ℂ := (polynomialWeightRatio grade shift ((twoFrequencyTranslation shift).symm input) : ℂ) *
    frequencyReserveSymbol reserve input
  let multiplier := ((constant • ContinuousLinearMap.id ℂ
    (ComplexEuclidean source →L[ℂ] ComplexEuclidean target))).restrictScalars ℝ
  have nonzero : ∀ point ∈ Icc lower 1, point ≠ 0 := fun point member => (positive.trans_le member.1).ne'
  have observedSame : EqOn
      (fun point => observe (radialConjugatedAction parameters lower positive bounded.le (kernels 0) grade reserve point))
      (fun point => scalar 0 point • multiplier (vector 0 point)) (Icc lower 1) := by
    intro point member
    dsimp only [observe,radialConjugatedAction,ContinuousLinearMap.coe_restrictScalars']
    rw [fourierEntryObservation_conjugated,bulkWeightRatio_phasePolynomial,
      collarRadius_literal lower positive bounded.le point member]
    ext value coordinate
    change (((radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2 point *
      polynomialWeightRatio grade shift ((twoFrequencyTranslation shift).symm input) : ℝ) : ℂ) *
      frequencyReserveSymbol reserve input) * _ =
      (radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2 point : ℂ) * (constant * _)
    rw [Complex.ofReal_mul]
    dsimp only [constant,vector,ContinuousLinearMap.id_apply]
    ring_nf
    rfl
  rw [vectorEulerWithin_congr (Icc lower 1) rank _ _ observedSame inside]
  have scalarDerivative (order : ℕ) (point : ℝ) (member : point ∈ Icc lower 1) :
      HasDerivWithinAt (scalar order) (point⁻¹ • scalar (order+1) point) (Icc lower 1) point :=
    actualScalarEulerJets_hasDerivWithinAt (Icc lower 1)
      (radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2)
      (radialPhaseRatio_smooth parameters ((twoFrequencyTranslation shift).symm input).2 input.2)
      order point (nonzero point member)
  have vectorDerivative := fun order point member => tower.entry parameters lower positive bounded.le kernels order point member shift input
  rw [scalarEulerPolynomial_mapped_fidelity (Icc lower 1) (uniqueDiffOn_Icc bounded) nonzero scalar vector
    multiplier scalarDerivative vectorDerivative rank radius.val inside]
  have original := scalarEulerPolynomial_fidelity (Icc lower 1) (uniqueDiffOn_Icc bounded) nonzero scalar vector
    scalarDerivative vectorDerivative rank radius.val inside
  rw [← original]
  change multiplier (actualClosedConjugatedEulerEntry parameters (Icc lower 1)
    (fun point => (kernels 0 (collarRadius lower positive bounded.le point)).entry) rank radius.val shift input) =
    fourierEntryObservation ((twoFrequencyTranslation shift).symm input) input
      (conjugatedKernelAction parameters grade reserve radius
        (conjugatedEulerKernel parameters radius (fun order => kernels order radius) rank))
  rw [conjugatedEulerKernel_actual parameters lower positive bounded kernels tower radius inside rank shift input,
    fourierEntryObservation_conjugated,bulkWeightRatio_phasePolynomial]
  ext value coordinate
  change constant * ((radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2 radius.val : ℂ) * _) =
    (((radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2 radius.val *
      polynomialWeightRatio grade shift ((twoFrequencyTranslation shift).symm input) : ℝ) : ℂ) * frequencyReserveSymbol reserve input) * _
  rw [Complex.ofReal_mul]
  dsimp only [constant]
  ring_nf

end Grad.OriginalCartesianTameEstimate

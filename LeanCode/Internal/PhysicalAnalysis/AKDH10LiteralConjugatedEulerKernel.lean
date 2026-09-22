import AKDH9ActualPhaseEulerKernel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.AnnularWeightedSmoothness Grad.AnnularRadialSmoothness
open Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.Allocation
attribute [local irreducible] fullKernelAdd fullKernelSmul

def conjugatedEulerKernelSum {source target : ℕ} (parameters : PhaseParameters) (radius : RadialPoint)
    (kernels : ℕ → RadialKernel parameters radius source target) (terms : List (ℕ × ℕ)) :
    RadialKernel parameters radius source target :=
  List.rec (fullKernelSmul 0 (kernels 0)) (fun term _ previous =>
    fullKernelAdd (phaseEulerKernel parameters radius term.1 (kernels term.2)) previous) terms

def conjugatedEulerKernel {source target : ℕ} (parameters : PhaseParameters) (radius : RadialPoint)
    (kernels : ℕ → RadialKernel parameters radius source target) (rank : ℕ) :
    RadialKernel parameters radius source target :=
  conjugatedEulerKernelSum parameters radius kernels (eulerLeibnizTerms rank)

theorem conjugatedEulerKernelSum_moment {source target : ℕ} (parameters : PhaseParameters) (radius : RadialPoint)
    (kernels : ℕ → RadialKernel parameters radius source target) (terms : List (ℕ × ℕ)) (moment : ℕ) :
    fullKernelMoment (radialKernelParameters parameters radius) moment (conjugatedEulerKernelSum parameters radius kernels terms) ≤
      eulerAllocationSum (fun first second => positiveEulerRatioConstant parameters first *
        fullKernelMoment (radialKernelParameters parameters radius) (moment+first) (kernels second)) terms := by
  induction terms with
  | nil => exact (fullKernelSmul_moment_le 0 _ moment).trans_eq (by simp [eulerAllocationSum])
  | cons term terms previous =>
      exact (fullKernelAdd_moment_le _ moment _ _).trans
        (add_le_add (phaseEulerKernel_moment parameters radius term.1 moment (kernels term.2)) previous)

theorem conjugatedEulerKernelSum_entry {source target : ℕ} (parameters : PhaseParameters) (radius : RadialPoint)
    (kernels : ℕ → RadialKernel parameters radius source target) (terms : List (ℕ × ℕ)) (shift input : ℤ × ℤ) :
    radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2 radius.val •
      (conjugatedEulerKernelSum parameters radius kernels terms).entry shift input =
    scalarEulerPolynomial
      (fun rank => eulerIteratedDerivative rank (radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2))
      (fun rank _ => (kernels rank).entry shift input) terms radius.val := by
  induction terms with
  | nil =>
      change _ • (fullKernelSmul (0 : ℂ) (kernels 0)).entry shift input = 0
      rw [fullKernelSmul_entry]
      ext vector coordinate
      change (radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2 radius.val : ℂ) *
        (0 * ((kernels 0).entry shift input vector coordinate)) = 0
      ring
  | cons term terms previous =>
      change _ • (fullKernelAdd (phaseEulerKernel parameters radius term.1 (kernels term.2))
        (conjugatedEulerKernelSum parameters radius kernels terms)).entry shift input = _
      rw [fullKernelAdd_entry,smul_add,phaseEulerKernel_entry_actual,previous]
      rfl

/-- Full original-kernel realization of each genuine phase-conjugated
Euler derivative. It is suitable for the existing bulk Schur action. -/
theorem conjugatedEulerKernel_actual {source target : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (kernels : ℕ → (radius : RadialPoint) → RadialKernel parameters radius source target)
    (derivative : KernelEulerDerivativeTower parameters lower positive bounded.le kernels)
    (radius : RadialPoint) (inside : radius.val ∈ Icc lower 1) (rank : ℕ) (shift input : ℤ × ℤ) :
    actualClosedConjugatedEulerEntry parameters (Icc lower 1)
      (fun point => (kernels 0 (collarRadius lower positive bounded.le point)).entry) rank radius.val shift input =
    radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2 radius.val •
      (conjugatedEulerKernel parameters radius (fun order => kernels order radius) rank).entry shift input := by
  let scalar := fun order => eulerIteratedDerivative order
    (radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2)
  let vector := fun order point => (kernels order (collarRadius lower positive bounded.le point)).entry shift input
  have nonzero : ∀ point ∈ Icc lower 1, point ≠ 0 := fun point member => (positive.trans_le member.1).ne'
  have fidelity := scalarEulerPolynomial_fidelity (Icc lower 1) (uniqueDiffOn_Icc bounded) nonzero scalar vector
    (fun order point member => actualScalarEulerJets_hasDerivWithinAt (Icc lower 1) _
      (radialPhaseRatio_smooth parameters _ _) order point (nonzero point member))
    (fun order point member => derivative.entry parameters lower positive bounded.le kernels order point member shift input)
    rank radius.val inside
  change vectorEulerWithinIteratedDerivative (Icc lower 1) rank (fun point => scalar 0 point • vector 0 point) radius.val = _
  rw [fidelity]
  rw [conjugatedEulerKernel,conjugatedEulerKernelSum_entry]
  have sameRadius : collarRadius lower positive bounded.le radius.val = radius :=
    Subtype.ext (collarRadius_literal lower positive bounded.le radius.val inside)
  generalize eulerLeibnizTerms rank = terms
  induction terms with
  | nil => rfl
  | cons term terms previous =>
      change scalar term.1 radius.val • vector term.2 radius.val+scalarEulerPolynomial scalar vector terms radius.val = _
      rw [previous]
      dsimp only [vector]
      rw [sameRadius]
      rfl

/-- Uniform physical allocation for the actual conjugated Euler kernels.
The raw Euler and phase displacement ranks share one total budget. -/
theorem OriginalEulerMoments.conjugatedKernels {parameters : PhaseParameters} {L compact : ℝ} {source target : ℕ}
    {kernels : (state : AnnularReconstructionState parameters L compact) → ℕ →
      (radius : RadialPoint) → RadialKernel parameters radius source target}
    (moments : OriginalEulerMoments parameters L compact kernels) :
    OriginalEulerMoments parameters L compact (fun state rank radius =>
      conjugatedEulerKernel parameters radius (fun order => kernels state order radius) rank) := by
  choose constants nonnegative bounds using moments
  intro rank moment
  let constant := eulerAllocationSum (fun first second => positiveEulerRatioConstant parameters first *
    constants second (moment+first)) (eulerLeibnizTerms rank)
  have phase0 (order : ℕ) := zero_le_one.trans (positiveEulerRatioConstant_one_le parameters order)
  refine ⟨constant,eulerAllocationSum_nonnegative _ (fun first second => mul_nonneg (phase0 first) (nonnegative _ _)) _,?_⟩
  intro state low radius
  apply (conjugatedEulerKernelSum_moment parameters radius (fun order => kernels state order radius) (eulerLeibnizTerms rank) moment).trans
  let size := 1+physicalBudget parameters state.val.field state.val.rho state.val.epsilon (10+(rank+moment))
  have paid : eulerAllocationSum (fun first second => positiveEulerRatioConstant parameters first *
      fullKernelMoment (radialKernelParameters parameters radius) (moment+first) (kernels state second radius)) (eulerLeibnizTerms rank) ≤
      eulerAllocationSum (fun first second => size * (positiveEulerRatioConstant parameters first * constants second (moment+first))) (eulerLeibnizTerms rank) := by
    apply eulerAllocationSum_mono
    intro term member
    have degree := eulerLeibnizTerms_rank rank term member
    have bound := mul_le_mul_of_nonneg_left (bounds term.2 (moment+term.1) state low radius) (phase0 term.1)
    rw [show 10+(term.2+(moment+term.1)) = 10+(rank+moment) by omega] at bound
    exact bound.trans_eq (by dsimp only [size]; ring)
  apply paid.trans_eq
  rw [← eulerAllocationSum_mul_left]
  exact mul_comm _ _

end Grad.OriginalCartesianTameEstimate

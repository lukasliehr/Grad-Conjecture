import AKDD19SameNormalizedInverseRowsEuler

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularRadialSmoothness Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularKernelL2

/-- Actual full-cell original-phase Euler/Schur statement. Constants are
chosen before the state, positive collar, radius and arbitrary input-cell
selector. No radial derivative or norm bound is an input. -/
def OriginalPhaseEulerBound (parameters : PhaseParameters) (L compact : ℝ) {source target : ℕ}
    (base : (state : AnnularReconstructionState parameters L compact) →
      (radius : RadialPoint) → RadialKernel parameters radius source target) : Prop :=
  ∀ rank moment, ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (state : AnnularReconstructionState parameters L compact),
    physicalBudget parameters state.val.field state.val.rho state.val.epsilon 10 ≤ 1 →
    ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
      (radius : RadialPoint), radius.val ∈ Icc lower 1 → ∀ inputs : (ℤ × ℤ) → (ℤ × ℤ),
    let coefficient := fun point => (base state (collarRadius lower positive bounded.le point)).entry
    Summable (fun shift : ℤ × ℤ => Grad.AnnularVariational.annularFrequency shift.1 shift.2^moment *
      ‖actualClosedConjugatedEulerEntry parameters (Icc lower 1) coefficient rank radius.val shift (inputs shift)‖) ∧
    (∑' shift : ℤ × ℤ, Grad.AnnularVariational.annularFrequency shift.1 shift.2^moment *
      ‖actualClosedConjugatedEulerEntry parameters (Icc lower 1) coefficient rank radius.val shift (inputs shift)‖) ≤
      constant*(1+physicalBudget parameters state.val.field state.val.rho state.val.epsilon (10+(rank+moment)))

theorem ActualEulerFamily.originalPhase {parameters : PhaseParameters} {L compact : ℝ} {source target : ℕ}
    {base : (state : AnnularReconstructionState parameters L compact) →
      (radius : RadialPoint) → RadialKernel parameters radius source target}
    (family : ActualEulerFamily parameters L compact base) : OriginalPhaseEulerBound parameters L compact base := by
  intro rank moment
  obtain ⟨constant,nonnegative,bound⟩ := family.moments.conjugated rank moment
  refine ⟨constant,nonnegative,?_⟩
  intro state low lower positive bounded radius inside inputs
  have actual := bound state low lower positive bounded (family.derivative state lower positive bounded) radius inside inputs
  have same : (fun point => (family.kernels state 0 (collarRadius lower positive bounded.le point)).entry) =
      (fun point => (base state (collarRadius lower positive bounded.le point)).entry) := by
    funext point
    rw [family.zero]
  dsimp only at actual
  rw [same] at actual
  exact actual

/-- SAME actual encoded first inverse and mass inverse. Their original
signs, preconditioner and exact Neumann inverse kernels are retained. -/
theorem actualFirstAndMassInverse_originalPhase (parameters : PhaseParameters) (L compact : ℝ) :
    OriginalPhaseEulerBound parameters L compact
      (fun state radius => radialEncodedFirstInverseKernel parameters L compact state.val radius state.firstSmall) ∧
    OriginalPhaseEulerBound parameters L compact
      (fun state radius => radialMassInverseKernel parameters L compact state.val radius state.property) :=
  ⟨(originalEncodedFirstInverseEulerFamily parameters L compact).originalPhase,
    (originalMassInverseEulerFamily parameters L compact).originalPhase⟩

/-- The literal normalized seven-slot mass, covariant and rotated-
covariant rows have uniform full-cell original-width Euler Schur bounds.
Every phase/coefficient derivative split pays rank+moment once; each
bound contains exactly one high B_(10+rank+moment). The external original
seven-slot reciprocal-radius normalization remains explicit elsewhere. -/
theorem actualNormalizedInverseRows_originalPhase (parameters : PhaseParameters) (L compact : ℝ) :
    OriginalPhaseEulerBound parameters L compact
      (fun state radius => radialRecoveredMassKernel parameters L compact state.val radius state.property) ∧
    OriginalPhaseEulerBound parameters L compact
      (fun state radius => radialNormalizedCovariantKernel parameters L compact state.val radius state.property) ∧
    OriginalPhaseEulerBound parameters L compact
      (fun state radius => radialNormalizedRotatedCovariantKernel parameters L compact state.val radius state.property) :=
  ⟨(originalRecoveredMassEulerFamily parameters L compact).originalPhase,
    (originalNormalizedCovariantEulerFamily parameters L compact).originalPhase,
    (originalNormalizedRotatedCovariantEulerFamily parameters L compact).originalPhase⟩

end Grad.OriginalCartesianTameEstimate

import AKC19ConjugatedKernelAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 350000
open Set
open scoped BigOperators ENNReal Topology ContDiff
namespace Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.BoundaryLift Grad.AnnularKernelL2
open Grad.AnnularReconstruction Grad.AnnularKernelContinuity Grad.AnnularRadialSmoothness

theorem smoothConjugatedFamily_matrixJets {source target : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (kernels : ℕ → (radius : RadialPoint) → RadialKernel parameters radius source target)
    (coefficients : ℕ → ℝ → (ℤ × ℤ) → (ComplexEuclidean source →L[ℂ] ComplexEuclidean target))
    (same : ∀ rank radius shift input, (kernels rank radius).entry shift input = coefficients rank radius.val shift)
    (derivative : ∀ rank shift radius, HasDerivAt (fun point => coefficients rank point shift)
      (coefficients (rank + 1) radius shift) radius)
    (regular : ∀ rank, RegularKernelFamily (kernels rank)) (start : ℕ) :
    SmoothConjugatedFamily parameters lower positive bounded.le (kernels start) := by
  intro grade order
  refine ⟨order + 4, ?_⟩
  have result := radialConjugatedAction_matrixJets parameters lower positive bounded
    (fun rank => kernels (start + rank))
    (fun rank radius shift _ => coefficients (start + rank) radius shift)
    (fun rank radius shift input => same (start + rank) radius shift input)
    (fun rank shift _ radius => by simpa only [Nat.add_assoc] using derivative (start + rank) shift radius)
    (fun rank => regular (start + rank)) grade order
  apply result.congr
  intro radius _
  change (bulkKernelAction parameters grade _ (kernels start _)).comp _ =
    (bulkKernelAction parameters grade _ (kernels (start + 0) _)).comp _
  rw [Nat.add_zero]
  rfl

theorem smoothConjugatedFamily_fixed {source target : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (family : (p : PhaseParameters) → FullTwoFrequencyKernel p source target)
    (same : ∀ first second, SameKernelEntries (family first) (family second)) :
    SmoothConjugatedFamily parameters lower positive bounded.le
      (fun radius => family (radialKernelParameters parameters radius)) := by
  let factor := fun rank : ℕ => if rank = 0 then (1 : ℂ) else 0
  let kernels := fun rank (radius : RadialPoint) => fullKernelSmul (factor rank) (family (radialKernelParameters parameters radius))
  let coefficients := fun rank (_radius : ℝ) shift input => factor rank • (family parameters).entry shift input
  have regular : ∀ rank, RegularKernelFamily (kernels rank) := by
    intro rank
    exact fixedRadialKernel_regular parameters (fun p => fullKernelSmul (factor rank) (family p))
      (fun first second shift input => congrArg (fun value => factor rank • value) (same first second shift input))
  have derivative : ∀ rank shift input radius, HasDerivAt (fun point => coefficients rank point shift input)
      (coefficients (rank + 1) radius shift input) radius := by
    intro rank shift input radius
    have zero : coefficients (rank + 1) radius shift input = 0 := by
      change (if rank + 1 = 0 then (1 : ℂ) else 0) • (family parameters).entry shift input = 0
      rw [if_neg (by omega)]
      apply ContinuousLinearMap.ext
      intro vector
      apply PiLp.ext
      intro component
      change (0 : ℂ) * (family parameters).entry shift input vector component = 0
      exact zero_mul _
    rw [zero]
    exact hasDerivAt_const radius (factor rank • (family parameters).entry shift input)
  intro grade order
  have derived := radialConjugatedAction_matrixJets parameters lower positive bounded kernels coefficients
    (fun rank radius shift input => congrArg (fun value => factor rank • value) (same _ parameters shift input))
    derivative regular grade order
  refine ⟨order + 4, derived.congr ?_⟩
  intro radius _
  change (bulkKernelAction parameters grade _ _).comp (hilbertReserve parameters source (order + 4)) =
    (bulkKernelAction parameters grade _ (fullKernelSmul (factor 0) _)).comp (hilbertReserve parameters source (order + 4))
  simp only [factor, ite_true, bulkKernelAction_smul, one_smul]

theorem smoothConjugatedFamily_identity (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (dimension : ℕ) :
    SmoothConjugatedFamily parameters lower positive bounded
      (fun radius => fullIdentityKernel (radialKernelParameters parameters radius) dimension) := by
  intro grade order
  refine ⟨0, (contDiffOn_const (c := ContinuousLinearMap.id ℂ (CellL2 dimension))).congr ?_⟩
  intro radius _
  dsimp only
  rw [bulkKernelAction_identity, hilbertReserve_zero, ContinuousLinearMap.comp_id]

end Grad.AnnularWeightedSmoothness

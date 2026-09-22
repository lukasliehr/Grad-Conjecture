import AEA10ActualPhysicalRowConjugation
import AEA6ActualFiniteReferenceEnergy

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace Grad.AnnularLowReference
open Grad.AnnularLowEnergy Grad.AnnularVariational Grad.CartesianState

/-- Actual circular physical solutions obey the original weighted finite-mode
energy estimate after the specified phase/am/mu change of variables. The mode
set may contain either sign of each low angular mode and any axial cell. -/
theorem originalLowCircularPhysicalEnergy_consumer
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (parameters : PhaseParameters) (length radius : ℝ)
    (lengthPositive : 0 < length) (support : Finset LowAnnularMode) (positive : 0 < radius)
    (xi flux : LowAnnularMode → ℝ → E) (forcingXi forcingFlux : LowAnnularMode → E)
    (firstPhysical : ∀ mode ∈ support, HasDerivAt (xi mode)
      (lowCircularMatrix length radius mode 0 0 • xi mode radius +
        lowCircularMatrix length radius mode 0 1 • flux mode radius + forcingXi mode) radius)
    (secondPhysical : ∀ mode ∈ support, HasDerivAt (flux mode)
      (lowCircularMatrix length radius mode 1 0 • xi mode radius +
        lowCircularMatrix length radius mode 1 1 • flux mode radius + forcingFlux mode) radius) :
    deriv (fun point => lowFiniteEnergy length point support
      (fun mode => lowPhysicalWeightedField parameters length mode 0 (xi mode) point)
      (fun mode => lowPhysicalWeightedField parameters length mode 1 (flux mode) point)) radius +
      (lowEta length parameters.gamma / 2) * radius ^ (-(7 / 2 : ℝ)) *
        (∑ mode ∈ support,
          (‖lowPhysicalWeightedField parameters length mode 0 (xi mode) radius‖ ^ 2 +
            ‖lowPhysicalWeightedField parameters length mode 1 (flux mode) radius‖ ^ 2)) ≤
      (4 / lowEta length parameters.gamma) * radius ^ (-(7 / 2 : ℝ)) *
        (∑ mode ∈ support,
          (‖lowPhysicalNormalizedForcing parameters length radius mode 0 (forcingXi mode)‖ ^ 2 +
            ‖lowPhysicalNormalizedForcing parameters length radius mode 1 (forcingFlux mode)‖ ^ 2)) := by
  exact lowFiniteEnergy_derivative_bound parameters length radius lengthPositive support positive
    (fun mode => lowPhysicalWeightedField parameters length mode 0 (xi mode))
    (fun mode => lowPhysicalWeightedField parameters length mode 1 (flux mode))
    (fun mode => lowPhysicalNormalizedForcing parameters length radius mode 0 (forcingXi mode))
    (fun mode => lowPhysicalNormalizedForcing parameters length radius mode 1 (forcingFlux mode))
    (fun mode member => lowCircularFirst_hasDerivAt_conjugate parameters length radius mode positive
      (xi mode) (flux mode) (forcingXi mode) (firstPhysical mode member))
    (fun mode member => lowCircularSecond_hasDerivAt_conjugate parameters length radius mode positive
      (xi mode) (flux mode) (forcingFlux mode) (secondPhysical mode member))

/-- The matrix bound acts on the original complete ADY low Fourier space. -/
theorem originalLowReferenceOperator_consumer (parameters : PhaseParameters) (length radius : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < radius) (bounded : radius ≤ 1)
    (field : LowEnergyBoundary) :
    ‖lowNormalizedReference parameters length radius lengthPositive positive bounded field‖ ≤
      (2 * (7 + parameters.gamma * (1 + length))) * ‖field‖ :=
  lowNormalizedReference_bound parameters length radius lengthPositive positive bounded field

end Grad.AnnularLowReference

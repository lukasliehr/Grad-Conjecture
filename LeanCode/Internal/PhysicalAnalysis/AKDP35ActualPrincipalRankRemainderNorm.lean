import AKDP34ActualLedgerRowsRankControl
import AKDP33OriginalCircleRadialNorm

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 1600000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.NonlinearProduct
open Grad.OriginalCoreRealization Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

/-- The SAME complete original principal rank remainder, including every
current composition allocation, obeys an adjustable one-high estimate.
The numerical constant is selected before the original coefficient state. -/
theorem startupActualPrincipal_rank_oneHigh (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell) (lengthNonzero : L≠0) (scaleNonzero : ell≠0)
    (four five : ℕ → ℝ) (fourNonnegative : ∀ grade,0≤four grade) (fiveNonnegative : ∀ grade,0≤five grade)
    (rank : ℕ) (outer inner : Fin 2) (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ constant : ℝ,0≤constant ∧
      ∀ (state : StartupActualRankState parameters admissible four five) (core image : ACore parameters 3),
        originalSourceFieldLinear parameters image=
          startupGenuinePrincipalTensorKernel admissible state.ledger.val state.ledger.property.1 state.inverseCoherent outer inner
            (originalSourceFieldLinear parameters core) →
        ‖startupOriginalRankField parameters rank image-
          (StartupRankOperator.principalTensor admissible rank state.ledger.val state.ledger.property.1 state.inverseCoherent outer inner).coarse
            (startupOriginalRankField parameters rank core)‖ ≤ epsilon*originalGradeNorm rank core+
          constant*((1+physicalBudget parameters state.baseField state.rho state.epsilon (12+rank))*originalGradeNorm 0 core) := by
  let result := StartupActualRankState.principal_controlled parameters admissible lengthNonzero scaleNonzero
    four five fourNonnegative fiveNonnegative rank outer inner
  let profile : StartupCoreRankProfile := Classical.choose result
  have controlled := Classical.choose_spec result
  refine ⟨profile.remainder epsilon,profile.remainderNonnegative epsilon positive,?_⟩
  intro state core image same
  let actual := (controlled state).some
  have identical : image=actual.action core := originalSourceFieldLinear_injective parameters (same.trans (actual.same core).symm)
  subst image
  exact actual.remainderBound epsilon positive core

/-- The actual tensor image is an original core; this construction adds no
regularity or representative premise to the principal estimate. -/
theorem startupActualPrincipal_core_exists (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell) (lengthNonzero : L≠0) (scaleNonzero : ell≠0)
    (four five : ℕ → ℝ) (fourNonnegative : ∀ grade,0≤four grade) (fiveNonnegative : ∀ grade,0≤five grade)
    (state : StartupActualRankState parameters admissible four five) (core : ACore parameters 3) (outer inner : Fin 2) :
    ∃ image : ACore parameters 3,
      originalSourceFieldLinear parameters image=
        startupGenuinePrincipalTensorKernel admissible state.ledger.val state.ledger.property.1 state.inverseCoherent outer inner
          (originalSourceFieldLinear parameters core) := by
  let result := StartupActualRankState.principal_controlled parameters admissible lengthNonzero scaleNonzero
    four five fourNonnegative fiveNonnegative 0 outer inner
  have controlled := Classical.choose_spec result
  exact ⟨(controlled state).some.action core,(controlled state).some.same core⟩

theorem startupActualPrincipal_core_oneHigh (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell) (lengthNonzero : L≠0) (scaleNonzero : ell≠0)
    (four five : ℕ → ℝ) (fourNonnegative : ∀ grade,0≤four grade) (fiveNonnegative : ∀ grade,0≤five grade)
    (rank : ℕ) (outer inner : Fin 2) :
    ∃ constant : ℝ,0≤constant ∧
      ∀ (state : StartupActualRankState parameters admissible four five) (core image : ACore parameters 3),
        originalSourceFieldLinear parameters image=
          startupGenuinePrincipalTensorKernel admissible state.ledger.val state.ledger.property.1 state.inverseCoherent outer inner
            (originalSourceFieldLinear parameters core) →
        originalGradeNorm rank image ≤ constant*(originalGradeNorm rank core+
          (1+physicalBudget parameters state.baseField state.rho state.epsilon (12+rank))*originalGradeNorm 0 core) := by
  let result := StartupActualRankState.principal_controlled parameters admissible lengthNonzero scaleNonzero
    four five fourNonnegative fiveNonnegative rank outer inner
  let profile : StartupCoreRankProfile := Classical.choose result
  have controlled := Classical.choose_spec result
  refine ⟨profile.high,profile.highNonnegative,?_⟩
  intro state core image same
  let actual := (controlled state).some
  have identical : image=actual.action core := originalSourceFieldLinear_injective parameters (same.trans (actual.same core).symm)
  subst image
  exact actual.highBound core

end Grad.CartesianStartup

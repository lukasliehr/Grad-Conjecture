import AUB2FiniteSmoothLinearity

noncomputable section
set_option maxHeartbeats 1000000
namespace Grad.ActualUniformGlobal
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.ActualFiniteGlobal Grad.OrdinaryDiskFaithfulness Grad.OrdinaryDiskCalculus
open Grad.ActualInverseInduction Grad.OrdinaryInteriorBootstrap Grad.OrdinaryDiskMultiplier
open Grad.GaugeCoefficients.Physical.RadialLedger
attribute [local instance] unitNormedSpace

theorem smoothSource_bulk_bound (grade : ℕ) (core : ClosedJet 1) :
    ‖closedL2Core core‖ ≤ ‖unitDiskCoreInto grade core‖ := by
  have coordinate := unitSobolev_derivative_bound grade core (zeroGradeIndex grade)
  change ‖closedContinuousToDiskL2 (closedMultiDerivative core (0, 0))‖ ≤ _ at coordinate
  rw [closedMultiDerivative_zero] at coordinate
  exact coordinate.trans_eq (unitDiskCore_norm grade core).symm

def uniformInteriorStateConstant (grade : ℕ) (ceiling : ℝ) : ℝ :=
  max 0 (inverseInteriorStateConstant grade ceiling)

theorem uniformInteriorStateConstant_nonnegative (grade : ℕ) (ceiling : ℝ) :
    0 ≤ uniformInteriorStateConstant grade ceiling := le_max_left _ _

theorem inverseInteriorStateConstant_le (grade : ℕ) (parameter ceiling : ℝ)
    (bounded : |parameter| ≤ ceiling) :
    inverseInteriorStateConstant grade parameter ≤ uniformInteriorStateConstant grade ceiling := by
  have square : parameter ^ 2 ≤ ceiling ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg parameter) bounded 2
  have coefficient := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right square (unitBConstant_nonnegative grade))
      (apLoweringConstant_nonnegative grade)) (interiorSourceConstant_nonnegative grade)
  exact (add_le_add coefficient le_rfl).trans (le_max_right _ _)

private theorem scalarGradeInduction {Input : Type*} (grade : ℕ)
    (energy : Input → ℕ → ℝ) (size : Input → ℝ) (base : ℝ) (state forcing : ℕ → ℝ)
    (baseNonnegative : 0 ≤ base) (stateNonnegative : ∀ order, 0 ≤ state order)
    (forcingNonnegative : ∀ order, 0 ≤ forcing order)
    (baseBound : ∀ input, energy input 1 ≤ base * size input)
    (stepBound : ∀ order, order ≤ grade → ∀ input,
      energy input (order + 2) ≤ state order * energy input (order + 1) + forcing order * size input) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ input, energy input (grade + 2) ≤ constant * size input := by
  have every : ∀ order : ℕ, order ≤ grade + 1 → ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ input, energy input (order + 1) ≤ constant * size input := by
    intro order
    induction order with
    | zero => exact fun _ => ⟨base, baseNonnegative, baseBound⟩
    | succ order previous =>
      intro upper
      obtain ⟨constant, nonnegative, bound⟩ := previous (by omega)
      refine ⟨state order * constant + forcing order,
        add_nonneg (mul_nonneg (stateNonnegative order) nonnegative) (forcingNonnegative order), ?_⟩
      intro input
      exact (stepBound order (by omega) input).trans
        ((add_le_add (mul_le_mul_of_nonneg_left (bound input) (stateNonnegative order)) le_rfl).trans_eq (by ring))
  exact every (grade + 1) le_rfl

private structure FiniteEstimateInput (ceiling : ℝ) where
  parameters : PhaseParameters
  parameter : ℝ
  parameterBound : |parameter| ≤ ceiling
  source : highDiskL2
  core : ClosedJet 1
  same : source.val = closedL2Core core
  modes : Finset ℤ

/-- The global induction is applied to the actual finite inverse family.
Its two inputs are quantitative bounds for the actual selected forcing and
actual outer field; these are discharged by the angular and collar blocks. -/
theorem finiteGlobal_uniform_of_outer (grade : ℕ) (ceiling : ℝ)
    (selection outerConstant : ℕ → ℝ)
    (selectionNonnegative : ∀ order, 0 ≤ selection order)
    (outerNonnegative : ∀ order, 0 ≤ outerConstant order)
    (selectionBound : ∀ order (modes : Finset ℤ) (core : ClosedJet 1),
      ‖selectedForcing order modes core‖ ≤ selection order * ‖unitDiskCoreInto order core‖)
    (outerBound : ∀ order (parameter : ℝ), |parameter| ≤ ceiling →
      ∀ (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core) (modes : Finset ℤ),
      ‖finiteOuterOrdinary (order + 2) modes parameter source core same‖ ≤
        outerConstant order * ‖unitDiskCoreInto order core‖) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (parameters : PhaseParameters) (parameter : ℝ),
      |parameter| ≤ ceiling → ∀ (source : highDiskL2) (core : ClosedJet 1)
      (same : source.val = closedL2Core core) (modes : Finset ℤ),
      ‖finiteGlobalRepresentative parameters modes parameter source core same (grade + 2)‖ ≤
        constant * ‖unitDiskCoreInto grade core‖ := by
  let energy (input : FiniteEstimateInput ceiling) (order : ℕ) :=
    ‖finiteGlobalRepresentative input.parameters input.modes input.parameter input.source input.core input.same order‖
  let size (input : FiniteEstimateInput ceiling) := ‖unitDiskCoreInto grade input.core‖
  let forcing (order : ℕ) :=
    (ordinaryInteriorSourceConstant order * selection order + outerConstant order) * apLoweringConstant order
  have forcingNonnegative (order : ℕ) : 0 ≤ forcing order :=
    mul_nonneg (add_nonneg (mul_nonneg (interiorSourceConstant_nonnegative order) (selectionNonnegative order))
      (outerNonnegative order)) (apLoweringConstant_nonnegative order)
  have baseBound (input : FiniteEstimateInput ceiling) : energy input 1 ≤ 2 * size input := by
    have sourceBound : ‖input.source‖ ≤ size input := by
      change ‖input.source.val‖ ≤ _
      rw [input.same]
      exact smoothSource_bulk_bound grade input.core
    exact (finiteGlobal_H1_bound input.parameters input.modes input.parameter input.source input.core input.same).trans
      (mul_le_mul_of_nonneg_left sourceBound (by norm_num))
  have stepBound (order : ℕ) (paid : order ≤ grade) (input : FiniteEstimateInput ceiling) :
      energy input (order + 2) ≤ uniformInteriorStateConstant order ceiling * energy input (order + 1) +
        forcing order * size input := by
    have lower : ‖unitDiskCoreInto order input.core‖ ≤ apLoweringConstant order * size input :=
      (congrArg norm (unitLower_core paid input.core)).symm.le.trans (unitLower_bound paid _)
    have state : inverseInteriorStateConstant order input.parameter * energy input (order + 1) ≤
        uniformInteriorStateConstant order ceiling * energy input (order + 1) :=
      mul_le_mul_of_nonneg_right
        (inverseInteriorStateConstant_le order input.parameter ceiling input.parameterBound) (norm_nonneg _)
    have sourceBound : ‖selectedForcing order input.modes input.core‖ ≤
        selection order * (apLoweringConstant order * size input) :=
      (selectionBound order input.modes input.core).trans
        (mul_le_mul_of_nonneg_left lower (selectionNonnegative order))
    have collar : ‖finiteOuterOrdinary (order + 2) input.modes input.parameter input.source input.core input.same‖ ≤
        outerConstant order * (apLoweringConstant order * size input) :=
      (outerBound order input.parameter input.parameterBound input.source input.core input.same input.modes).trans
        (mul_le_mul_of_nonneg_left lower (outerNonnegative order))
    have estimate : energy input (order + 2) ≤
        inverseInteriorStateConstant order input.parameter * energy input (order + 1) +
        ordinaryInteriorSourceConstant order * ‖selectedForcing order input.modes input.core‖ +
        ‖finiteOuterOrdinary (order + 2) input.modes input.parameter input.source input.core input.same‖ :=
      finiteGlobal_step_bound input.parameters order input.modes input.parameter input.source input.core input.same
    exact estimate.trans ((add_le_add (add_le_add state
      (mul_le_mul_of_nonneg_left sourceBound (interiorSourceConstant_nonnegative order))) collar).trans_eq (by
        dsimp only [forcing]
        ring))
  obtain ⟨constant, nonnegative, bound⟩ := scalarGradeInduction grade energy size 2
    (fun order => uniformInteriorStateConstant order ceiling) forcing (by norm_num)
    (fun order => uniformInteriorStateConstant_nonnegative order ceiling) forcingNonnegative baseBound stepBound
  refine ⟨constant, nonnegative, ?_⟩
  intro parameters parameter parameterBound source core same modes
  exact bound ⟨parameters, parameter, parameterBound, source, core, same, modes⟩

end Grad.ActualUniformGlobal

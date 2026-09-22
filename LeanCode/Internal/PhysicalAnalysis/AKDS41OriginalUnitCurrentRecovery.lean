import AKDS33OriginalUnitPrincipalEndpoint
import AKDS40FiniteJetHighRankAbsorption

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
namespace Grad.OriginalCoreRealization
open Grad.CartesianState Grad.NonlinearProduct Grad.NonlinearQuotientBounds Grad.QuotientProjection
open Grad.GaugeCoefficients.Physical.Allocation Grad.OriginalCartesianTameEstimate
open Grad.BoundaryTrace Grad.GaugeCoefficients.Physical.RadialLedger Grad.CartesianStartup
open Grad.SourceCollarCoefficients

/-- The physical-length current recovers the identical original covariant
core from its compact input; the uniform profile is chosen before the state. -/
theorem originalUnitCurrent_sameCore_bound (parameters : PhaseParameters) (length radius : ℝ)
    (radiusNonnegative : 0≤radius) :
    ∃ constants : ℕ→ℝ,(∀ grade,0≤constants grade) ∧
      ∀ (state : OriginalUnitRankState parameters length radius) (core image : ACore parameters 3),
      originalSourceFieldLinear parameters image=
        originalCurrentKernel (unitDiskAdmissible parameters) state.data.gaugeDeviation
          (state.coherent radiusNonnegative).2.2.2.1 (state.inverseCoherent radiusNonnegative)
          (originalSourceFieldLinear parameters core) →
      ∀ grade,originalGradeNorm grade image≤constants grade*
        (originalGradeNorm grade core+(1+physicalBudget parameters state.field state.rho state.epsilon (12+grade))*
          originalGradeNorm 0 core) := by
  let endpoint := fun grade => (OriginalUnitRankState.current_endpoint parameters length radius radiusNonnegative grade).1
  let profile := fun grade => (endpoint grade).choose
  refine ⟨(fun grade => (profile grade).high),(fun grade => (profile grade).highNonnegative),?_⟩
  intro state core image same grade
  let actual := ((endpoint grade).choose_spec state).some
  have identical : image=actual.action core :=
    originalSourceFieldLinear_injective parameters (same.trans (actual.same core).symm)
  rw [identical]
  exact actual.highBound core

/-- Recover the covariant core only after absorbing the compact core.
The high coefficient multiplies its independent cell-zero source bound. -/
theorem originalUnitCurrent_oneHigh_of_compact (parameters : PhaseParameters) (length radius : ℝ)
    (radiusNonnegative : 0≤radius) (loss : ℕ) (lossLarge : 20≤loss)
    (compactConstants : ℕ→ℝ) (compactNonnegative : ∀ grade,0≤compactConstants grade)
    (cellConstant : ℝ) (cellNonnegative : 0≤cellConstant) :
    ∃ constants : ℕ→ℝ,(∀ grade,0≤constants grade) ∧
      ∀ (state : OriginalUnitRankState parameters length radius)
      (source : SmoothQuotient parameters) (core image : ACore parameters 3),
      physicalBudget parameters state.field state.rho state.epsilon 20≤1 →
      originalCellNorm parameters 0 core≤cellConstant*
        (‖quotientEta parameters 20 source‖+
          physicalBudget parameters state.field state.rho state.epsilon 20*‖quotientEta parameters 20 source‖) →
      (∀ grade,originalGradeNorm grade core≤compactConstants grade*
        (‖quotientEta parameters (grade+loss) source‖+
          physicalBudget parameters state.field state.rho state.epsilon (grade+loss)*‖quotientEta parameters loss source‖)) →
      originalSourceFieldLinear parameters image=
        originalCurrentKernel (unitDiskAdmissible parameters) state.data.gaugeDeviation
          (state.coherent radiusNonnegative).2.2.2.1 (state.inverseCoherent radiusNonnegative)
          (originalSourceFieldLinear parameters core) →
      ∀ grade,originalGradeNorm grade image≤constants grade*
        (‖quotientEta parameters (grade+loss) source‖+
          physicalBudget parameters state.field state.rho state.epsilon (grade+loss)*‖quotientEta parameters loss source‖) := by
  let current := originalUnitCurrent_sameCore_bound parameters length radius radiusNonnegative
  let constants := fun grade => current.choose grade*(compactConstants grade+2*cellConstant)
  have nonnegative (grade : ℕ) : 0≤constants grade :=
    mul_nonneg (current.choose_spec.1 grade)
      (add_nonneg (compactNonnegative grade) (mul_nonneg (by norm_num) cellNonnegative))
  refine ⟨constants,nonnegative,?_⟩
  intro state source core image bounded cell compact same grade
  let payment := ‖quotientEta parameters (grade+loss) source‖+
    physicalBudget parameters state.field state.rho state.epsilon (grade+loss)*‖quotientEta parameters loss source‖
  have base := originalGradeNorm_zero_of_cellTame parameters core cellConstant
    ‖quotientEta parameters 20 source‖ (physicalBudget parameters state.field state.rho state.epsilon 20)
    cellNonnegative (norm_nonneg _) bounded cell
  have sourcePaid : (1+physicalBudget parameters state.field state.rho state.epsilon (12+grade))*
      ‖quotientEta parameters 20 source‖≤payment := by
    have pieces := add_le_add
      (referenceSource_norm_mono parameters (by omega : 20≤grade+loss) source)
      (mul_le_mul (physicalBudget_monotone parameters state.field state.rho state.epsilon (by omega : 12+grade≤grade+loss))
        (referenceSource_norm_mono parameters lossLarge source) (norm_nonneg _)
        (physicalBudget_nonnegative _ _ _ _ _))
    dsimp only [payment]
    nlinarith only [pieces]
  have baseWeighted := mul_le_mul_of_nonneg_left base
    (add_nonneg zero_le_one (physicalBudget_nonnegative parameters state.field state.rho state.epsilon (12+grade)))
  have lowPaid := mul_le_mul_of_nonneg_left sourcePaid (mul_nonneg (by norm_num : (0:ℝ)≤2) cellNonnegative)
  have basePaid : (1+physicalBudget parameters state.field state.rho state.epsilon (12+grade))*
      originalGradeNorm 0 core≤(2*cellConstant)*payment := by nlinarith only [baseWeighted,lowPaid]
  have result := (current.choose_spec.2 state core image same grade).trans
    (mul_le_mul_of_nonneg_left (add_le_add (compact grade) basePaid) (current.choose_spec.1 grade))
  exact result.trans_eq (by dsimp only [constants]; ring)

end Grad.OriginalCoreRealization

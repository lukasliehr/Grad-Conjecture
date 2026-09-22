import AKDN7SharpBalancedPhaseEuler

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.PhaseAlgebra Grad.AnnularWeightedSmoothness
open Grad.SourceCollarCoefficients Grad.SourceBoundaryTrace Grad.AnnularSmoothCore Grad.BoundaryLift
open Grad.SourceCollarDivision Grad.AnnularReconstruction

/-- Finite reserve used only for differentiation of the actual diagonal. -/
def balancedReservedPhaseAction (parameters : PhaseParameters) (dimension reserve : ℕ) (radius : ℝ) :
    CellL2 dimension →L[ℂ] CellL2 dimension :=
  radius • phaseSlopeDiagonal parameters dimension reserve radius-hilbertReserve parameters dimension reserve

theorem balancedReservedPhaseAction_smooth (parameters : PhaseParameters) (dimension reserve order : ℕ)
    (enough : order+5 ≤ reserve) (lower : ℝ) (bounded : lower < 1) :
    ContDiffOn ℝ order (balancedReservedPhaseAction parameters dimension reserve) (Icc lower 1) :=
  (contDiffOn_id.smul (phaseSlopeDiagonal_contDiffOn parameters dimension reserve order enough lower 1 bounded)).sub contDiffOn_const

theorem balancedReservedPhaseAction_coefficient (parameters : PhaseParameters) (dimension reserve : ℕ)
    (enough : 5 ≤ reserve) (radius : ℝ) (field : CellL2 dimension) (mode : ℤ × ℤ) :
    balancedReservedPhaseAction parameters dimension reserve radius field mode =
      actualBalancedPhaseScalar parameters mode.2 radius • (frequencyReserveSymbol reserve mode • field mode) := by
  change radius • phaseSlopeDiagonal parameters dimension reserve radius field mode-
    hilbertReserve parameters dimension reserve field mode = _
  rw [phaseSlopeDiagonal_coefficient parameters dimension reserve enough,hilbertReserve_apply]
  rw [actualBalancedPhaseScalar,reservedPhaseSlopeSymbol]
  apply PiLp.ext
  intro coordinate
  simp only [PiLp.sub_apply,PiLp.smul_apply,←Complex.coe_smul,smul_eq_mul,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_one]
  ring

/-- Bounded observations identify the genuine finite-reserve Euler
operator with the literal Euler scalar, before any norm estimate. -/
theorem balancedReservedPhaseAction_genuineEuler (parameters : PhaseParameters) (dimension reserve rank : ℕ)
    (enough : rank+5 ≤ reserve) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (field : CellL2 dimension) (mode : ℤ × ℤ) :
    vectorEulerWithinIteratedDerivative (Icc lower 1) rank
      (balancedReservedPhaseAction parameters dimension reserve) radius field mode =
      eulerIteratedDerivative rank (actualBalancedPhaseScalar parameters mode.2) radius •
        (frequencyReserveSymbol reserve mode • field mode) := by
  let observe := (((lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode).comp
    (ContinuousLinearMap.apply ℂ (CellL2 dimension) field)).restrictScalars ℝ)
  have observation := vectorEulerWithin_observation (Icc lower 1) (uniqueDiffOn_Icc bounded)
    (balancedReservedPhaseAction parameters dimension reserve) observe rank
    (balancedReservedPhaseAction_smooth parameters dimension reserve rank enough lower bounded) inside
  change _ = observe _ at observation
  change observe (vectorEulerWithinIteratedDerivative (Icc lower 1) rank
    (balancedReservedPhaseAction parameters dimension reserve) radius) = _
  rw [←observation]
  have same : EqOn (fun point => observe (balancedReservedPhaseAction parameters dimension reserve point))
      (fun point => actualBalancedPhaseScalar parameters mode.2 point • (frequencyReserveSymbol reserve mode • field mode)) (Icc lower 1) := by
    intro point _
    exact balancedReservedPhaseAction_coefficient parameters dimension reserve (by omega) point field mode
  rw [vectorEulerWithin_congr (Icc lower 1) rank _ _ same inside]
  exact vectorEulerWithin_fixedScalar (Icc lower 1) (uniqueDiffOn_Icc bounded)
    (fun point member => (positive.trans_le member.1).ne') _ (actualBalancedPhaseScalar_smooth parameters mode.2)
    _ rank radius inside

def balancedPhaseEulerSymbol (parameters : PhaseParameters) (rank : ℕ) (radius : ℝ) (mode : ℤ × ℤ) : ℂ :=
  (eulerIteratedDerivative rank (actualBalancedPhaseScalar parameters mode.2) radius : ℂ)*frequencyReserveSymbol 1 mode

theorem balancedPhaseEulerSymbol_bound (parameters : PhaseParameters) (rank : ℕ) (radius : RadialPoint)
    (mode : ℤ × ℤ) :
    ‖balancedPhaseEulerSymbol parameters rank radius mode‖ ≤ balancedPhaseEulerConstant parameters rank := by
  have nonnegative := (Grad.SourceBoundaryTrace.annularFrequency_pos mode).le
  change ‖(eulerIteratedDerivative rank (actualBalancedPhaseScalar parameters mode.2) radius : ℂ)*
    ((annularFrequency mode.1 mode.2 : ℂ)^1)⁻¹‖ ≤ _
  rw [norm_mul,norm_inv,pow_one]
  simp only [Complex.norm_real,Real.norm_of_nonneg nonnegative]
  have scalarBound : ‖eulerIteratedDerivative rank (actualBalancedPhaseScalar parameters mode.2) radius‖ ≤
      balancedPhaseEulerConstant parameters rank*annularFrequency mode.1 mode.2 :=
    actualBalancedPhaseScalar_euler_bound parameters rank mode radius radius.property
  exact (mul_le_mul_of_nonneg_right scalarBound
    (inv_nonneg.mpr nonnegative)).trans_eq (by rw [mul_assoc,mul_inv_cancel₀ (Grad.SourceBoundaryTrace.annularFrequency_pos mode).ne',mul_one])

/-- The sharp bounded Euler action: precisely one input frequency, for
all radial ranks, with the same original phase and no coefficient state. -/
def balancedPhaseEulerAction (parameters : PhaseParameters) (dimension rank : ℕ) (radius : RadialPoint) :
    CellL2 dimension →L[ℂ] CellL2 dimension :=
  boundedHilbertMultiplier parameters dimension (balancedPhaseEulerSymbol parameters rank radius)
    (balancedPhaseEulerConstant parameters rank) (balancedPhaseEulerConstant_nonnegative parameters rank)
    (balancedPhaseEulerSymbol_bound parameters rank radius)

theorem balancedPhaseEulerAction_norm (parameters : PhaseParameters) (dimension rank : ℕ) (radius : RadialPoint) :
    ‖balancedPhaseEulerAction parameters dimension rank radius‖ ≤ balancedPhaseEulerConstant parameters rank :=
  coefficientOperator_norm_le _ _ _ _ (balancedPhaseEulerConstant_nonnegative parameters rank) _

theorem balancedPhaseEulerAction_zero (parameters : PhaseParameters) (dimension : ℕ) (radius : RadialPoint) :
    balancedPhaseEulerAction parameters dimension 0 radius = balancedPhaseAction parameters dimension radius := by
  apply ContinuousLinearMap.ext
  intro field
  apply lp.ext
  funext mode
  change balancedPhaseEulerSymbol parameters 0 radius mode • field mode = balancedPhaseSymbol parameters radius mode • field mode
  congr 1
  change ((radius.val * Grad.AnnularVariational.annularPhaseSlope parameters mode.2 radius-1 : ℝ) : ℂ)*
    frequencyReserveSymbol 1 mode = _
  simp only [balancedPhaseSymbol,reservedPhaseSlopeSymbol,frequencyReserveSymbol,frequencyRatioSymbol,pow_one,
    Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_one,one_div]
  ring

/-- Compatible reserve is cancelled before the bound. No reserve or high
coefficient norm is charged to the native input. -/
theorem balancedReservedPhaseAction_sameEuler (parameters : PhaseParameters) (dimension reserve rank : ℕ)
    (enough : rank+5 ≤ reserve+1) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (radius : RadialPoint) (inside : radius.val ∈ Icc lower 1) (reserved high : CellL2 dimension)
    (same : ∀ mode, reserved mode=(annularFrequency mode.1 mode.2 : ℂ)^reserve • high mode) :
    vectorEulerWithinIteratedDerivative (Icc lower 1) rank
      (balancedReservedPhaseAction parameters dimension (reserve+1)) radius.val reserved =
      balancedPhaseEulerAction parameters dimension rank radius high := by
  apply lp.ext
  funext mode
  rw [balancedReservedPhaseAction_genuineEuler parameters dimension (reserve+1) rank enough lower positive bounded radius inside]
  change _ = balancedPhaseEulerSymbol parameters rank radius mode • high mode
  rw [same,balancedPhaseEulerSymbol,←Complex.coe_smul,smul_smul,smul_smul]
  congr 1
  have nonzero : (annularFrequency mode.1 mode.2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Grad.SourceBoundaryTrace.annularFrequency_pos mode).ne'
  simp only [frequencyReserveSymbol,pow_add,pow_one]
  field_simp

end Grad.OriginalCartesianTameEstimate

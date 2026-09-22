import BKA9SourceInputs

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.NonlinearQuotientBounds Grad.BoundaryTrace
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection

/-- The seven scalar negative-half slots in the exact AH20 order
`(x, R xi, xi_zeta, xi, F0, R F0, F2)`. -/
abbrev SevenSlotTrace (parameters : PhaseParameters) (angular cell : ℕ) :=
  PiLp 2 (fun _ : Fin 7 => NegativeTrace parameters angular cell 1)

def sevenSlotTrace (parameters : PhaseParameters) (angular cell : ℕ)
    (x : NegativeTrace parameters angular cell 1)
    (xi : PositiveTrace parameters angular cell 1)
    (source : SourceBoundaryTuple) : SevenSlotTrace parameters angular cell :=
  (PiLp.continuousLinearEquiv 2 ℂ
    (fun _ : Fin 7 => NegativeTrace parameters angular cell 1)).symm
      ![x,
        positiveRotationToNegative parameters angular cell xi,
        positiveCellToNegative parameters angular cell xi,
        positiveToNegative parameters angular cell xi,
        sourceBoundaryToNegative parameters angular cell (source 0),
        sourceBoundaryToNegative parameters angular cell (source 1),
        sourceBoundaryToNegative parameters angular cell (source 2)]

theorem sevenSlotTrace_components (parameters : PhaseParameters) (angular cell : ℕ)
    (x : NegativeTrace parameters angular cell 1)
    (xi : PositiveTrace parameters angular cell 1)
    (source : SourceBoundaryTuple) :
    (fun slot => sevenSlotTrace parameters angular cell x xi source slot) =
      ![x,
        positiveRotationToNegative parameters angular cell xi,
        positiveCellToNegative parameters angular cell xi,
        positiveToNegative parameters angular cell xi,
        sourceBoundaryToNegative parameters angular cell (source 0),
        sourceBoundaryToNegative parameters angular cell (source 1),
        sourceBoundaryToNegative parameters angular cell (source 2)] := by
  funext slot
  fin_cases slot <;> rfl

theorem sevenSlotTrace_norm_sq (parameters : PhaseParameters) (angular cell : ℕ)
    (x : NegativeTrace parameters angular cell 1)
    (xi : PositiveTrace parameters angular cell 1)
    (source : SourceBoundaryTuple) :
    ‖sevenSlotTrace parameters angular cell x xi source‖ ^ 2 =
      ‖x‖ ^ 2 +
      ‖positiveRotationToNegative parameters angular cell xi‖ ^ 2 +
      ‖positiveCellToNegative parameters angular cell xi‖ ^ 2 +
      ‖positiveToNegative parameters angular cell xi‖ ^ 2 +
      ‖sourceBoundaryToNegative parameters angular cell (source 0)‖ ^ 2 +
      ‖sourceBoundaryToNegative parameters angular cell (source 1)‖ ^ 2 +
      ‖sourceBoundaryToNegative parameters angular cell (source 2)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  let components : Fin 7 → NegativeTrace parameters angular cell 1 :=
    ![x,
      positiveRotationToNegative parameters angular cell xi,
      positiveCellToNegative parameters angular cell xi,
      positiveToNegative parameters angular cell xi,
      sourceBoundaryToNegative parameters angular cell (source 0),
      sourceBoundaryToNegative parameters angular cell (source 1),
      sourceBoundaryToNegative parameters angular cell (source 2)]
  have componentLaw := sevenSlotTrace_components parameters angular cell x xi source
  calc
    ∑ slot, ‖sevenSlotTrace parameters angular cell x xi source slot‖ ^ 2 =
        ∑ slot, ‖components slot‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro slot _
          rw [congrFun componentLaw slot]
    _ = _ := by
      dsimp only [components]
      simp [Fin.sum_univ_succ]
      ring

theorem sevenSlotTrace_bound_sq (parameters : PhaseParameters) (angular cell : ℕ)
    (x : NegativeTrace parameters angular cell 1)
    (xi : PositiveTrace parameters angular cell 1)
    (source : SourceBoundaryTuple) :
    ‖sevenSlotTrace parameters angular cell x xi source‖ ^ 2 ≤
      ‖x‖ ^ 2 + 3 * ‖xi‖ ^ 2 + ‖source‖ ^ 2 := by
  have rotation := pow_le_pow_left₀ (norm_nonneg _)
    (positiveRotationToNegative_bound parameters angular cell xi) 2
  have cellDerivative := pow_le_pow_left₀ (norm_nonneg _)
    (positiveCellToNegative_bound parameters angular cell xi) 2
  have inclusion := pow_le_pow_left₀ (norm_nonneg _)
    (positiveToNegative_bound parameters angular cell xi) 2
  have sourceZero := pow_le_pow_left₀ (norm_nonneg _)
    (sourceBoundaryToNegative_bound parameters angular cell (source 0)) 2
  have sourceOne := pow_le_pow_left₀ (norm_nonneg _)
    (sourceBoundaryToNegative_bound parameters angular cell (source 1)) 2
  have sourceTwo := pow_le_pow_left₀ (norm_nonneg _)
    (sourceBoundaryToNegative_bound parameters angular cell (source 2)) 2
  have sourceNorm := PiLp.norm_sq_eq_of_L2
    (fun _ : Fin 3 => SourceBoundary 1) source
  rw [Fin.sum_univ_three] at sourceNorm
  rw [sevenSlotTrace_norm_sq]
  nlinarith

/-- AH20 with the three actual known source slots supplied by the accepted
original outer-source trace. -/
def actualSevenSlotTrace (parameters : PhaseParameters) (L : ℝ) (angular cell : ℕ)
    (x : NegativeTrace parameters angular cell 1)
    (xi : PositiveTrace parameters angular cell 1)
    (source : ZAmbient parameters (angular + cell + 2)) :
    SevenSlotTrace parameters angular cell :=
  sevenSlotTrace parameters angular cell x xi
    (sourceOuterTrace parameters L (angular + cell) source)

theorem actualSevenSlotTrace_components (parameters : PhaseParameters) (L : ℝ)
    (angular cell : ℕ) (x : NegativeTrace parameters angular cell 1)
    (xi : PositiveTrace parameters angular cell 1)
    (source : ZAmbient parameters (angular + cell + 2)) :
    (fun slot => actualSevenSlotTrace parameters L angular cell x xi source slot) =
      ![x,
        positiveRotationToNegative parameters angular cell xi,
        positiveCellToNegative parameters angular cell xi,
        positiveToNegative parameters angular cell xi,
        sourceBoundaryToNegative parameters angular cell
          (sourceOuterTrace parameters L (angular + cell) source 0),
        sourceBoundaryToNegative parameters angular cell
          (sourceOuterTrace parameters L (angular + cell) source 1),
        sourceBoundaryToNegative parameters angular cell
          (sourceOuterTrace parameters L (angular + cell) source 2)] := by
  exact sevenSlotTrace_components parameters angular cell x xi
    (sourceOuterTrace parameters L (angular + cell) source)

theorem actualSevenSlotTrace_bound_sq (parameters : PhaseParameters) (L : ℝ)
    (positive : 0 < L) (angular cell : ℕ)
    (x : NegativeTrace parameters angular cell 1)
    (xi : PositiveTrace parameters angular cell 1)
    (source : ZAmbient parameters (angular + cell + 2)) :
    ‖actualSevenSlotTrace parameters L angular cell x xi source‖ ^ 2 ≤
      ‖x‖ ^ 2 + 3 * ‖xi‖ ^ 2 +
        sourceOuterTraceConstant L (angular + cell) ^ 2 * ‖source‖ ^ 2 := by
  apply (sevenSlotTrace_bound_sq parameters angular cell x xi
    (sourceOuterTrace parameters L (angular + cell) source)).trans
  have sourceBound := pow_le_pow_left₀ (norm_nonneg _)
    (sourceOuterTrace_bound parameters L positive (angular + cell) source) 2
  rw [mul_pow] at sourceBound
  nlinarith

theorem actualSevenSlotTrace_source_core (parameters : PhaseParameters) (L : ℝ)
    (angular cell : ℕ) (x : NegativeTrace parameters angular cell 1)
    (xi : PositiveTrace parameters angular cell 1)
    (source : SmoothQuotient parameters) (mode : ℤ × ℤ) :
    (fun slot : Fin 3 => negativeTraceCoefficient parameters angular cell
      (actualSevenSlotTrace parameters L angular cell x xi
        (quotientEta parameters (angular + cell + 2) source) (Fin.natAdd 4 slot)) mode) =
      ![originalBoundaryCoefficient parameters
          (tangentialBoundaryCore parameters (cartesianSourceVector source)) mode,
        originalBoundaryCoefficient parameters
          (rotationCore parameters
            (tangentialBoundaryCore parameters (cartesianSourceVector source))) mode,
        (L : ℂ)⁻¹ • originalBoundaryCoefficient parameters (source 3) mode] := by
  funext slot
  have outer := sourceOuterTrace_core parameters L (angular + cell) source mode
  fin_cases slot
  · change negativeTraceCoefficient parameters angular cell
        (sourceBoundaryToNegative parameters angular cell
          (sourceOuterTrace parameters L (angular + cell)
            (quotientEta parameters (angular + cell + 2) source) 0)) mode = _
    rw [sourceBoundaryToNegative_coefficient]
    exact congrFun outer 0
  · change negativeTraceCoefficient parameters angular cell
        (sourceBoundaryToNegative parameters angular cell
          (sourceOuterTrace parameters L (angular + cell)
            (quotientEta parameters (angular + cell + 2) source) 1)) mode = _
    rw [sourceBoundaryToNegative_coefficient]
    exact congrFun outer 1
  · change negativeTraceCoefficient parameters angular cell
        (sourceBoundaryToNegative parameters angular cell
          (sourceOuterTrace parameters L (angular + cell)
            (quotientEta parameters (angular + cell + 2) source) 2)) mode = _
    rw [sourceBoundaryToNegative_coefficient]
    exact congrFun outer 2

end Grad.BoundaryKernelAction

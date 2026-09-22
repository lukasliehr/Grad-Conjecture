import AKCI4ActualBalancedHomogeneousFlux
import AKH3ExactPhaseDiagonalCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
open scoped Topology
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothness Grad.BoundaryLift

def balancedPhaseSymbol (parameters : PhaseParameters) (radius : ℝ) (mode : ℤ × ℤ) : ℂ :=
  (radius : ℂ)*reservedPhaseSlopeSymbol parameters 1 radius mode - frequencyRatioSymbol none mode

theorem balancedPhaseSymbol_bound (parameters : PhaseParameters) (radius : RadialPoint)
    (mode : ℤ × ℤ) :
    ‖balancedPhaseSymbol parameters radius mode‖ ≤ phaseSlopeJetConstant parameters 0+1 := by
  have radiusBound : ‖(radius.val : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_of_nonneg radius.property.1]
    exact radius.property.2
  have slope := reservedPhaseSlopeSymbol_bound parameters 1 (le_refl 1) radius mode
  have first := mul_le_mul radiusBound slope (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
  exact (norm_sub_le _ _).trans ((add_le_add ((norm_mul _ _).le.trans first)
    (frequencyRatioSymbol_bound none mode)).trans_eq (by simp only [one_mul]))

/-- Exactly D(Phi)-1 at the cost of one input frequency, with the original
curved phase. No five-grade reserve from qualitative smoothness is used. -/
def balancedPhaseAction (parameters : PhaseParameters) (dimension : ℕ) (radius : RadialPoint) :
    CellL2 dimension →L[ℂ] CellL2 dimension :=
  boundedHilbertMultiplier parameters dimension (balancedPhaseSymbol parameters radius)
    (phaseSlopeJetConstant parameters 0+1)
    (by linarith [phaseSlopeJetConstant_nonnegative parameters 0])
    (balancedPhaseSymbol_bound parameters radius)

theorem balancedPhaseAction_norm (parameters : PhaseParameters) (dimension : ℕ) (radius : RadialPoint) :
    ‖balancedPhaseAction parameters dimension radius‖ ≤ phaseSlopeJetConstant parameters 0+1 :=
  coefficientOperator_norm_le _ _ _ _ (by linarith [phaseSlopeJetConstant_nonnegative parameters 0]) _

theorem balancedPhaseAction_same (parameters : PhaseParameters) (dimension : ℕ) (radius : RadialPoint)
    (high low : CellL2 dimension)
    (same : ∀ mode, high mode = (annularFrequency mode.1 mode.2 : ℂ) • low mode)
    (mode : ℤ × ℤ) :
    balancedPhaseAction parameters dimension radius high mode =
      ((radius.val : ℂ)*(Grad.AnnularVariational.annularPhaseSlope parameters mode.2 radius : ℂ)-1) • low mode := by
  have nonzero : (annularFrequency mode.1 mode.2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Grad.SourceBoundaryTrace.annularFrequency_pos mode).ne'
  change balancedPhaseSymbol parameters radius mode • high mode = _
  rw [same,smul_smul]
  congr 1
  simp only [balancedPhaseSymbol,reservedPhaseSlopeSymbol,frequencyReserveSymbol,
    frequencyRatioSymbol,pow_one]
  field_simp

end Grad.OriginalCartesianTameEstimate

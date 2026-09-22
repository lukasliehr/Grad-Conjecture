import AKCI5OriginalBalancedPhaseOrder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
open scoped Topology
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothness Grad.AnnularWeightedSystem
open Grad.AnnularReconstruction Grad.AnnularCurrentLow Grad.AnnularKernelL2
open Grad.GaugeCoefficients.Physical.Allocation

/-- The exact balanced homogeneous radial RHS from SR15, including both
copies of D(Phi)-1 and the original j,c,rV row kernels. -/
def balancedHomogeneousSystem (parameters : PhaseParameters) (length compact : ℝ)
    (state : RetainedInverseState parameters length compact) (grade : ℕ) (radius : RadialPoint)
    (high : PhysicalHilbertPair) : PhysicalHilbertPair :=
  let row := fun index : Fin 3 => bulkKernelAction parameters (grade+1) radius
    (lowPhysicalRowKernel parameters length compact state index radius) (balancedSevenInput parameters radius high)
  (balancedPhaseAction parameters 1 radius high.1,balancedPhaseAction parameters 1 radius high.2) +
    balancedFluxOutput parameters length radius (row 0,(row 1,row 2))

/-- A concrete original-kernel estimate, before differentiating any radial
word. Every homogeneous term consumes one next tangential grade. -/
theorem balancedHomogeneousSystem_oneOrder (parameters : PhaseParameters) (length compact : ℝ)
    (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (state : RetainedInverseState parameters length compact),
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 ≤ 1 →
    ∀ (radius : RadialPoint) (high low : PhysicalHilbertPair),
    (∀ mode, hilbertPairCoefficient mode high =
      (annularFrequency mode.1 mode.2 : ℂ)^(grade+1) • hilbertPairCoefficient mode low) →
    ‖balancedHomogeneousSystem parameters length compact state grade radius high‖ ≤
      constant * (‖high‖ +
        physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+11) * ‖low‖) := by
  obtain ⟨fluxConstant,fluxNonnegative,fluxBound⟩ := actualBalancedHomogeneousFlux_oneOrder parameters length compact grade
  let phaseConstant := phaseSlopeJetConstant parameters 0+1
  have phaseNonnegative : 0 ≤ phaseConstant := by
    dsimp only [phaseConstant]
    linarith [phaseSlopeJetConstant_nonnegative parameters 0]
  refine ⟨phaseConstant+fluxConstant,add_nonneg phaseNonnegative fluxNonnegative,?_⟩
  intro state small radius high low same
  have phaseBound (field : CellL2 1) : ‖balancedPhaseAction parameters 1 radius field‖ ≤ phaseConstant*‖field‖ :=
    ((balancedPhaseAction parameters 1 radius).le_opNorm field).trans
      (mul_le_mul_of_nonneg_right (balancedPhaseAction_norm parameters 1 radius) (norm_nonneg field))
  have pairBound : ‖(balancedPhaseAction parameters 1 radius high.1,balancedPhaseAction parameters 1 radius high.2)‖ ≤ phaseConstant*‖high‖ := by
    rw [Prod.norm_def]
    exact max_le ((phaseBound high.1).trans (mul_le_mul_of_nonneg_left (norm_fst_le high) phaseNonnegative))
      ((phaseBound high.2).trans (mul_le_mul_of_nonneg_left (norm_snd_le high) phaseNonnegative))
  have baseNonnegative := mul_nonneg
    (physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+11)) (norm_nonneg low)
  have phasePaid := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (a := ‖high‖) baseNonnegative) phaseNonnegative
  unfold balancedHomogeneousSystem
  exact (norm_add_le _ _).trans ((add_le_add (pairBound.trans phasePaid)
    (fluxBound state small radius high low same)).trans_eq (by ring))

/-- The same next-grade input gives the literal SR15 weighted coefficients.
This is an operator identity and does not assume a replacement radial PDE. -/
theorem balancedHomogeneousSystem_coefficient (parameters : PhaseParameters) (length compact : ℝ)
    (state : RetainedInverseState parameters length compact) (grade : ℕ) (radius : RadialPoint)
    (high current : PhysicalHilbertPair)
    (same : ∀ mode, hilbertPairCoefficient mode high =
      (annularFrequency mode.1 mode.2 : ℂ) • hilbertPairCoefficient mode current)
    (mode : ℤ × ℤ) :
    let row := fun index : Fin 3 => bulkKernelAction parameters (grade+1) radius
      (lowPhysicalRowKernel parameters length compact state index radius) (balancedSevenInput parameters radius high)
    hilbertPairCoefficient mode (balancedHomogeneousSystem parameters length compact state grade radius high) =
      (((radius.val : ℂ)*(Grad.AnnularVariational.annularPhaseSlope parameters mode.2 radius : ℂ)-1) • current.1 mode +
        hilbertMeanFree parameters (row 0) mode,
       ((radius.val : ℂ)*(Grad.AnnularVariational.annularPhaseSlope parameters mode.2 radius : ℂ)-1) • current.2 mode -
        ((radius.val : ℂ)*(length : ℂ)⁻¹) • (frequencyRatioSymbol (some true) mode • row 1 mode) -
        frequencyRatioSymbol (some false) mode • row 2 mode) := by
  dsimp only
  have first (query : ℤ × ℤ) : high.1 query = (annularFrequency query.1 query.2 : ℂ) • current.1 query :=
    congrArg Prod.fst (same query)
  have second (query : ℤ × ℤ) : high.2 query = (annularFrequency query.1 query.2 : ℂ) • current.2 query :=
    congrArg Prod.snd (same query)
  dsimp only [balancedHomogeneousSystem]
  rw [balancedFluxOutput_actual]
  change (balancedPhaseAction parameters 1 radius high.1 mode + _,
    balancedPhaseAction parameters 1 radius high.2 mode + _) = _
  rw [balancedPhaseAction_same parameters 1 radius high.1 current.1 first mode,
    balancedPhaseAction_same parameters 1 radius high.2 current.2 second mode]
  apply Prod.ext
  · rfl
  · simp only [sub_eq_add_neg,neg_smul,add_assoc]
    rfl

end Grad.OriginalCartesianTameEstimate

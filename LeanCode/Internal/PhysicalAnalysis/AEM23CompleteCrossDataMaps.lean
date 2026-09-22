import AEM22LiteralHighToLowSourceRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCrossMaps
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularCurrentLow
open Grad.BoundaryKernelAction Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularKernelL2
open Grad.ActualBoundaryPrimitives Grad.GaugeCoefficients.Physical.Allocation

abbrev CrossHighBulk (lower : ℝ) := PiLp 2 (fun _ : Fin 3 => AnnularBulk lower)

/-- Literal nonzero BF16 data subset: (f,qc,rqv,-beta), in the inherited
Hilbert norms. The full source-graph embedding sets all other inputs to zero. -/
abbrev CrossHighData (parameters : PhaseParameters) (lower : ℝ) :=
  WithLp 2 (CrossHighBulk lower × HighBoundaryPrimitive parameters 0 0)

def lowToHighBulkTriple (parameters : PhaseParameters) (lower length compact : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact) :
    lowEnergyGraph lower length positive →L[ℂ] CrossHighBulk lower :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => AnnularBulk lower)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (lowToHighBulkCross parameters lower length compact lengthPositive positive bounded state))

def lowToHighCross (parameters : PhaseParameters) (lower length compact : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (state : RetainedInverseState parameters length compact) :
    lowEnergyGraph lower length positive →L[ℂ] CrossHighData parameters lower :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ (CrossHighBulk lower) (HighBoundaryPrimitive parameters 0 0)).symm.toContinuousLinearMap.comp
    ((lowToHighBulkTriple parameters lower length compact lengthPositive positive (lowerHalf.trans (by norm_num)) state).prod
      (lowToHighBoundaryCross parameters lower length compact lengthPositive positive lowerHalf state))

theorem lowToHighCross_bulk (parameters : PhaseParameters) (lower length compact : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (state : RetainedInverseState parameters length compact) (field : lowEnergyGraph lower length positive) (row : Fin 3) :
    (lowToHighCross parameters lower length compact lengthPositive positive lowerHalf state field).ofLp.1 row =
      lowToHighBulkCross parameters lower length compact lengthPositive positive (lowerHalf.trans (by norm_num)) state row field := rfl

theorem lowToHighCross_boundary (parameters : PhaseParameters) (lower length compact : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (state : RetainedInverseState parameters length compact) (field : lowEnergyGraph lower length positive) :
    (lowToHighCross parameters lower length compact lengthPositive positive lowerHalf state field).ofLp.2 =
      lowToHighBoundaryCross parameters lower length compact lengthPositive positive lowerHalf state field := rfl

theorem crossHighBulk_norm_le_sum (lower : ℝ) (field : CrossHighBulk lower) :
    ‖field‖ ≤ ∑ row, ‖field row‖ := by
  have square := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => AnnularBulk lower) field
  rw [Fin.sum_univ_three] at square ⊢
  nlinarith [norm_nonneg field, norm_nonneg (field 0), norm_nonneg (field 1), norm_nonneg (field 2),
    mul_nonneg (norm_nonneg (field 0)) (norm_nonneg (field 1)),
    mul_nonneg (norm_nonneg (field 0)) (norm_nonneg (field 2)),
    mul_nonneg (norm_nonneg (field 1)) (norm_nonneg (field 2))]

def lowToHighErrorConstant (parameters : PhaseParameters) (length compact : ℝ) : ℝ :=
  (∑ row : Fin 3, lowPhysicalRowErrorConstant parameters length compact row * (7 + 2 * length)) +
    lowBoundaryErrorConstant parameters length compact * lowOuterSevenConstant length

theorem lowToHighErrorConstant_nonnegative (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length) :
    0 ≤ lowToHighErrorConstant parameters length compact := by
  unfold lowToHighErrorConstant
  exact add_nonneg (Finset.sum_nonneg (fun row _ =>
    mul_nonneg (lowPhysicalRowErrorConstant_nonnegative parameters length compact row) (by linarith)))
    (mul_nonneg (lowBoundaryErrorConstant_nonnegative parameters length compact) (lowOuterSevenConstant_nonnegative length lengthPositive))

theorem lowToHighCross_B8 (parameters : PhaseParameters) (lower length compact : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (state : RetainedInverseState parameters length compact) (field : lowEnergyGraph lower length positive) :
    ‖lowToHighCross parameters lower length compact lengthPositive positive lowerHalf state field‖ ≤
      lowToHighErrorConstant parameters length compact *
        physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 * ‖field‖ := by
  let data := lowToHighCross parameters lower length compact lengthPositive positive lowerHalf state field
  let budget := physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8
  have square := WithLp.prod_norm_sq_eq_of_L2 data
  change ‖data‖ ^ 2 = ‖data.ofLp.1‖ ^ 2 + ‖data.ofLp.2‖ ^ 2 at square
  have triangle : ‖data‖ ≤ ‖data.ofLp.1‖ + ‖data.ofLp.2‖ := by
    nlinarith [norm_nonneg data, norm_nonneg data.ofLp.1, norm_nonneg data.ofLp.2,
      mul_nonneg (norm_nonneg data.ofLp.1) (norm_nonneg data.ofLp.2)]
  have bulk : ‖data.ofLp.1‖ ≤
      (∑ row : Fin 3, lowPhysicalRowErrorConstant parameters length compact row * (7 + 2 * length)) * budget * ‖field‖ := by
    apply (crossHighBulk_norm_le_sum lower data.ofLp.1).trans
    have rows := Finset.sum_le_sum (fun row (_ : row ∈ Finset.univ) =>
      lowToHighBulkCross_B8 parameters lower length compact lengthPositive positive (lowerHalf.trans (by norm_num)) state row field)
    change (∑ row : Fin 3, ‖lowToHighBulkCross parameters lower length compact lengthPositive positive
      (lowerHalf.trans (by norm_num)) state row field‖) ≤ _
    dsimp only [budget]
    simpa only [Finset.sum_mul] using rows
  have boundary : ‖data.ofLp.2‖ ≤ (lowBoundaryErrorConstant parameters length compact * lowOuterSevenConstant length) * budget * ‖field‖ :=
    lowToHighBoundaryCross_B8 parameters lower length compact lengthPositive positive lowerHalf state field
  change ‖data‖ ≤ _
  unfold lowToHighErrorConstant
  dsimp only [budget] at bulk boundary
  nlinarith

end Grad.AnnularCrossMaps

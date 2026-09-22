import AJB1ActualLowPhysicalRowOrbit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularLowOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularKernelOrbit
open Grad.AnnularKernelL2 Grad.AnnularKernelContinuity Grad.BoundaryKernelAction Grad.AnnularReconstruction

/-- Exact original rho-stored seven-input and mu-normalized three-output
composition, with only the physical coefficient kernels translated. -/
def actualLowResponseOrbit (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact) (tau : OrbitParameter) :
    LowEnergyBulk lower →L[ℂ] LowEnergyBulk lower :=
  ((lowFirstOutput parameters lower length).comp (actualLowRowOrbit parameters length compact lower positive bounded state 0 tau) +
    (lowCellOutput lower length positive).comp (actualLowRowOrbit parameters length compact lower positive bounded state 1 tau) +
    (lowAngularOutput lower length positive).comp (actualLowRowOrbit parameters length compact lower positive bounded state 2 tau)).comp
    (lowNormalizedSevenInput parameters lower length lengthPositive positive)

def actualLowResponseOrbitJet (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact) (tau : OrbitParameter) (angular cell : ℕ) :
    LowEnergyBulk lower →L[ℂ] LowEnergyBulk lower :=
  ((lowFirstOutput parameters lower length).comp (actualLowRowOrbitJet parameters length compact lower positive bounded state 0 tau angular cell) +
    (lowCellOutput lower length positive).comp (actualLowRowOrbitJet parameters length compact lower positive bounded state 1 tau angular cell) +
    (lowAngularOutput lower length positive).comp (actualLowRowOrbitJet parameters length compact lower positive bounded state 2 tau angular cell)).comp
    (lowNormalizedSevenInput parameters lower length lengthPositive positive)

def actualLowGeneratorOrbit (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact) (tau : OrbitParameter) :
    LowEnergyBulk lower →L[ℂ] LowEnergyBulk lower :=
  lowCommonDiagonal parameters length lower lengthPositive positive +
    actualLowResponseOrbit parameters length compact lower lengthPositive positive bounded state tau

private theorem orbitAction_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (field : lp (fun _ : ℤ × ℤ => E) 2) : orbitLpAction E 0 field = field := by
  apply lp.ext
  funext mode
  rw [orbitLpAction_apply, orbitCharacter_zero, one_smul]

theorem actualLowRowOrbit_zero (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : RetainedInverseState parameters length compact) (row : Fin 3) :
    actualLowRowOrbit parameters length compact lower positive bounded state row 0 =
      lowPhysicalRowAction parameters length compact lower positive bounded state row := by
  rw [actualLowRowOrbit_conjugation]
  apply ContinuousLinearMap.ext
  intro field
  simp only [ContinuousLinearMap.comp_apply, neg_zero, orbitAction_zero]

theorem actualLowResponseOrbit_zero (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact) :
    actualLowResponseOrbit parameters length compact lower lengthPositive positive bounded state 0 =
      lowPhysicalResponse parameters length compact lower lengthPositive positive bounded state := by
  unfold actualLowResponseOrbit lowPhysicalResponse
  rw [actualLowRowOrbit_zero, actualLowRowOrbit_zero, actualLowRowOrbit_zero]

/-- The zero displacement is the SAME accepted AEI21 current generator. -/
theorem actualLowGeneratorOrbit_zero (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact) :
    actualLowGeneratorOrbit parameters length compact lower lengthPositive positive bounded state 0 =
      lowCurrentBulk parameters length compact lower lengthPositive positive bounded state := by
  rw [actualLowGeneratorOrbit, actualLowResponseOrbit_zero]
  rfl

/-- One actual error moment controls every positive derivative of the
fully normalized low response, uniformly over the original collars. -/
theorem actualLowResponseOrbitJet_oneHigh (parameters : PhaseParameters) (length compact : ℝ)
    (lengthPositive : 0 < length) (angular cell : ℕ) (orderPositive : 0 < angular + cell) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (state : RetainedInverseState parameters length compact)
      (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (tau : OrbitParameter),
      ‖actualLowResponseOrbitJet parameters length compact lower lengthPositive positive bounded state tau angular cell‖ ≤
        constant * state.val.errorBudget (angular + cell) := by
  obtain ⟨first, firstNonnegative, firstBound⟩ := actualLowRowOrbitJet_oneHigh parameters length compact 0 angular cell orderPositive
  obtain ⟨second, secondNonnegative, secondBound⟩ := actualLowRowOrbitJet_oneHigh parameters length compact 1 angular cell orderPositive
  obtain ⟨third, thirdNonnegative, thirdBound⟩ := actualLowRowOrbitJet_oneHigh parameters length compact 2 angular cell orderPositive
  let amplitude := lowBalanceConstant length parameters.gamma + 2
  have amplitudeNonnegative : 0 ≤ amplitude := by
    have one : 1 ≤ lowBalanceConstant length parameters.gamma := le_max_left _ _
    dsimp [amplitude]
    linarith
  refine ⟨(amplitude * first + second + 2 * third) * (7 + 2 * length), by positivity, ?_⟩
  intro state lower positive bounded tau
  let budget := state.val.errorBudget (angular + cell)
  have budgetNonnegative : 0 ≤ budget :=
    Grad.GaugeCoefficients.Physical.Allocation.physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon _
  have totalNonnegative : 0 ≤ (amplitude * first + second + 2 * third) * (7 + 2 * length) * budget := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ totalNonnegative
  intro field
  let input := lowNormalizedSevenInput parameters lower length lengthPositive positive field
  let result := fun row => actualLowRowOrbitJet parameters length compact lower positive bounded state row tau angular cell input
  have r0 : ‖result 0‖ ≤ first * budget * ‖input‖ :=
    (ContinuousLinearMap.le_opNorm _ input).trans (mul_le_mul_of_nonneg_right (firstBound state lower positive bounded tau) (norm_nonneg input))
  have r1 : ‖result 1‖ ≤ second * budget * ‖input‖ :=
    (ContinuousLinearMap.le_opNorm _ input).trans (mul_le_mul_of_nonneg_right (secondBound state lower positive bounded tau) (norm_nonneg input))
  have r2 : ‖result 2‖ ≤ third * budget * ‖input‖ :=
    (ContinuousLinearMap.le_opNorm _ input).trans (mul_le_mul_of_nonneg_right (thirdBound state lower positive bounded tau) (norm_nonneg input))
  have o0 := (lowFirstOutput_bound parameters lower length (result 0)).trans
    (mul_le_mul_of_nonneg_left r0 amplitudeNonnegative)
  have o1 := (lowCellOutput_bound lower length positive (result 1)).trans r1
  have o2 := (lowAngularOutput_bound lower length positive (result 2)).trans
    (mul_le_mul_of_nonneg_left r2 (by norm_num))
  change ‖lowFirstOutput parameters lower length (result 0) + lowCellOutput lower length positive (result 1) +
    lowAngularOutput lower length positive (result 2)‖ ≤ _
  have total : ‖lowFirstOutput parameters lower length (result 0) + lowCellOutput lower length positive (result 1) +
      lowAngularOutput lower length positive (result 2)‖ ≤ (amplitude * first + second + 2 * third) * budget * ‖input‖ :=
    (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans (by dsimp [amplitude] at *; nlinarith))
  apply total.trans
  have inputBound := lowNormalizedSevenInput_bound parameters lower length lengthPositive positive field
  calc
    _ ≤ (amplitude * first + second + 2 * third) * budget * ((7 + 2 * length) * ‖field‖) :=
      mul_le_mul_of_nonneg_left inputBound (by positivity)
    _ = _ := by ring

end Grad.AnnularLowOrbit

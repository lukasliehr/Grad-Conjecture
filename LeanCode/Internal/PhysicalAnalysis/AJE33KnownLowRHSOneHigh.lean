import AJE32ExactKnownLowRHSConjugation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 300000
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource Grad.AnnularCurrentEnergy
open Grad.AnnularStrongData Grad.AnnularReconstruction Grad.AnnularHighInverseOrbit Grad.AnnularKernelL2
open Grad.AnnularKnownLow Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularLowOrbit Grad.AnnularCoupledOrbit
open Grad.GaugeCoefficients.Physical.Allocation

private theorem normIntoHilbertZero {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (field : E) : ‖WithLp.toLp 2 (field,(0 : F))‖ ≤ ‖field‖ := by
  simpa only [norm_zero,add_zero] using hilbert_norm_le_add (WithLp.toLp 2 (field,(0 : F)))

theorem knownLowBulkIntoData_bound (lower : ℝ) (field : LowEnergyBulk lower) :
    ‖knownLowBulkIntoData lower field‖ ≤ ‖field‖ := normIntoHilbertZero field

theorem knownLowSourceInput_bound (lower : ℝ) (data : KnownLowData lower) :
    ‖knownLowSourceInput lower data‖ ≤ 3 * ‖data‖ :=
  (knownLowSevenPacket_bound lower data.ofLp.1.ofLp.1).trans
    (mul_le_mul_of_nonneg_left (knownLowData_component_bounds lower data).1 (by norm_num))

def knownLowOutputConstant (parameters : PhaseParameters) (length : ℝ) (row : Fin 3) : ℝ :=
  ![lowBalanceConstant length parameters.gamma + 2,1,2] row

theorem knownLowOutputConstant_nonnegative (parameters : PhaseParameters) (length : ℝ) (row : Fin 3) :
    0 ≤ knownLowOutputConstant parameters length row := by
  have bound : 1 ≤ lowBalanceConstant length parameters.gamma := le_max_left _ _
  fin_cases row <;> change 0 ≤ _
  · change 0 ≤ lowBalanceConstant length parameters.gamma + 2
    linarith
  · norm_num [knownLowOutputConstant]
  · norm_num [knownLowOutputConstant]

theorem knownLowOutput_bound (parameters : PhaseParameters) (length lower : ℝ) (positive : 0 < lower)
    (row : Fin 3) (field : DivisionRow 1 lower) :
    ‖knownLowOutput parameters length lower positive row field‖ ≤ knownLowOutputConstant parameters length row * ‖field‖ := by
  fin_cases row
  · exact lowFirstOutput_bound parameters lower length field
  · change ‖lowCellOutput lower length positive field‖ ≤ 1 * ‖field‖
    simpa only [one_mul] using lowCellOutput_bound lower length positive field
  · exact lowAngularOutput_bound lower length positive field

theorem knownLowRowOperatorMap_bound (parameters : PhaseParameters) (length lower : ℝ) (positive : 0 < lower)
    (row : Fin 3) (mapping : DivisionRow 7 lower →L[ℂ] DivisionRow 1 lower) :
    ‖knownLowRowOperatorMap parameters length lower positive row mapping‖ ≤
      (3 * knownLowOutputConstant parameters length row) * ‖mapping‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg
    (mul_nonneg (by norm_num) (knownLowOutputConstant_nonnegative parameters length row)) (norm_nonneg mapping))
  intro data
  change ‖knownLowBulkIntoData lower (knownLowOutput parameters length lower positive row (mapping (knownLowSourceInput lower data)))‖ ≤ _
  apply (knownLowBulkIntoData_bound lower _).trans
  apply (knownLowOutput_bound parameters length lower positive row _).trans
  have innerBound := (mapping.le_opNorm (knownLowSourceInput lower data)).trans
    (mul_le_mul_of_nonneg_left (knownLowSourceInput_bound lower data) (norm_nonneg mapping))
  exact (mul_le_mul_of_nonneg_left innerBound (knownLowOutputConstant_nonnegative parameters length row)).trans_eq (by ring)

private theorem threeOperatorBound {E : Type*} [NormedAddCommGroup E] (first second third : E)
    (a b c budget : ℝ) (hf : ‖first‖ ≤ a * budget) (hg : ‖second‖ ≤ b * budget) (hh : ‖third‖ ≤ c * budget) :
    ‖first + second + third‖ ≤ (a + b + c) * budget :=
  (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans
    ((add_le_add (add_le_add hf hg) hh).trans_eq (by ring)))

/-- Every positive derivative of the actual AIR RHS contains one original
primitive error budget, uniformly over the original positive collars. -/
theorem knownLowDataOrbitJet_oneHigh (parameters : PhaseParameters) (length compact : ℝ)
    (angular cell : ℕ) (orderPositive : 0 < angular + cell) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (state : RetainedInverseState parameters length compact)
      (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (tau : OrbitParameter),
      ‖knownLowDataOrbitJet parameters length compact lower positive bounded state angular cell tau‖ ≤
        constant * state.val.errorBudget (angular + cell) := by
  obtain ⟨first,firstNonnegative,firstBound⟩ := actualLowRowOrbitJet_oneHigh parameters length compact 0 angular cell orderPositive
  obtain ⟨second,secondNonnegative,secondBound⟩ := actualLowRowOrbitJet_oneHigh parameters length compact 1 angular cell orderPositive
  obtain ⟨third,thirdNonnegative,thirdBound⟩ := actualLowRowOrbitJet_oneHigh parameters length compact 2 angular cell orderPositive
  let coefficient := fun row => 3 * knownLowOutputConstant parameters length row
  have coefficientNonnegative (row : Fin 3) : 0 ≤ coefficient row :=
    mul_nonneg (by norm_num) (knownLowOutputConstant_nonnegative parameters length row)
  refine ⟨coefficient 0 * first + coefficient 1 * second + coefficient 2 * third,
    add_nonneg (add_nonneg (mul_nonneg (coefficientNonnegative 0) firstNonnegative)
      (mul_nonneg (coefficientNonnegative 1) secondNonnegative))
      (mul_nonneg (coefficientNonnegative 2) thirdNonnegative), ?_⟩
  intro state lower positive bounded tau
  have firstEstimate := (knownLowRowOperatorMap_bound parameters length lower positive 0 _).trans
    (mul_le_mul_of_nonneg_left (firstBound state lower positive bounded tau) (coefficientNonnegative 0))
  have secondEstimate := (knownLowRowOperatorMap_bound parameters length lower positive 1 _).trans
    (mul_le_mul_of_nonneg_left (secondBound state lower positive bounded tau) (coefficientNonnegative 1))
  have thirdEstimate := (knownLowRowOperatorMap_bound parameters length lower positive 2 _).trans
    (mul_le_mul_of_nonneg_left (thirdBound state lower positive bounded tau) (coefficientNonnegative 2))
  unfold knownLowDataOrbitJet
  rw [constantOrbitJet,if_neg (ne_of_gt orderPositive),add_zero]
  exact threeOperatorBound _ _ _ _ _ _ _
    (firstEstimate.trans_eq (mul_assoc _ _ _).symm)
    (secondEstimate.trans_eq (mul_assoc _ _ _).symm)
    (thirdEstimate.trans_eq (mul_assoc _ _ _).symm)

end Grad.AnnularStrongOrbit

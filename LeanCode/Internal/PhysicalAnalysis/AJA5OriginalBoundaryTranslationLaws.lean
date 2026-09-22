import AJA2ExactPhysicalPacketTranslations
import AAT4TraceLiftCommutation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.AnnularHighInverseOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularGrades Grad.AnnularFluxTrace Grad.AnnularTiltedReference Grad.AnnularCurrentEnergy Grad.AnnularCurrentBoundary
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse
open Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit

theorem energyTrace_translation_mode (lower length : ℝ) (positive : 0 < lower) (collar : lower < 1)
    (lengthPositive : 0 < length) (endpoint : Fin 2) (tau : OrbitParameter)
    (field : annularEnergySpace lower length positive) (mode : HighAnnularMode) :
    annularEnergyTrace lower length positive collar lengthPositive endpoint
      (energyTranslation lower length positive tau field) mode =
      orbitCharacter tau mode.val • annularEnergyTrace lower length positive collar lengthPositive endpoint field mode := by
  unfold energyTranslation
  simp only [add_apply, smul_apply, map_add, map_smul,
    annularEnergyTrace_diagonal, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, realLpDiagonal_apply]
  exact complexParts_smul _ _

/-- The genuine original outer trace, including b decoding and original
positive-half encoding, commutes with the same translation. -/
theorem actualOuterTrace_translation (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length) (angular cell : ℕ)
    (tau : OrbitParameter) (field : annularEnergySpace lower length positive) :
    actualCurrentHighOuterTrace parameters lower length positive lowerHalf lengthPositive angular cell
      (energyTranslation lower length positive tau field) =
      orbitLpAction (ComplexEuclidean 1) tau
        (actualCurrentHighOuterTrace parameters lower length positive lowerHalf lengthPositive angular cell field) := by
  rw [actualCurrentHighOuterTrace_same, actualCurrentHighOuterTrace_same, bEnergyDecode_translation]
  apply lp.ext
  funext mode
  rw [orbitLpAction_apply]
  by_cases high : 3 ≤ |mode.1|
  · rw [highBoundaryIntoPositive_high parameters angular cell _ ⟨mode, high⟩,
      highBoundaryIntoPositive_high parameters angular cell _ ⟨mode, high⟩]
    exact energyTrace_translation_mode lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 1 tau _ ⟨mode, high⟩
  · rw [highBoundaryIntoPositive_low parameters angular cell _ mode high,
      highBoundaryIntoPositive_low parameters angular cell _ mode high, smul_zero]

theorem negativeCoefficient_translation {dimension : ℕ} (parameters : PhaseParameters) (angular cell : ℕ)
    (tau : OrbitParameter) (field : NegativeTrace parameters angular cell dimension) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell (orbitLpAction (ComplexEuclidean dimension) tau field) mode =
      orbitCharacter tau mode • negativeTraceCoefficient parameters angular cell field mode := by
  unfold negativeTraceCoefficient
  rw [orbitLpAction_apply]
  exact smul_comm _ _ _

theorem positiveCoefficient_translation {dimension : ℕ} (parameters : PhaseParameters) (angular cell : ℕ)
    (tau : OrbitParameter) (field : PositiveTrace parameters angular cell dimension) (mode : ℤ × ℤ) :
    positiveTraceCoefficient parameters angular cell (orbitLpAction (ComplexEuclidean dimension) tau field) mode =
      orbitCharacter tau mode • positiveTraceCoefficient parameters angular cell field mode := by
  unfold positiveTraceCoefficient
  rw [orbitLpAction_apply]
  exact smul_comm _ _ _

/-- The literal retained derivative tuple (Rxi,xi_zeta,xi), with its
original trace weights, commutes exactly with the same orbital unitary. -/
theorem originalRetainedTuple_translation (parameters : PhaseParameters) (length : ℝ) (angular cell : ℕ)
    (tau : OrbitParameter) (xi : PositiveTrace parameters angular cell 1) :
    originalRetainedBoundaryVector parameters length angular cell (orbitLpAction (ComplexEuclidean 1) tau xi) =
      orbitLpAction (ComplexEuclidean 3) tau (originalRetainedBoundaryVector parameters length angular cell xi) := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  rw [negativeCoefficient_translation]
  unfold originalRetainedBoundaryVector
  rw [boundaryRetainedVector_actual_coefficient, boundaryRetainedVector_actual_coefficient,
    positiveRotationToNegative_coefficient, positiveRotationToNegative_coefficient,
    positiveCellToNegative_coefficient, positiveCellToNegative_coefficient,
    positiveToNegative_coefficient, positiveToNegative_coefficient, positiveCoefficient_translation]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [smul_smul, mul_left_comm, mul_assoc]

end Grad.AnnularHighInverseOrbit

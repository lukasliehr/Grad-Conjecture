import AJD15OriginalHighCrossInputCovariance

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularCrossMaps Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularHighInverseOrbit
open Grad.AnnularLowOrbit Grad.AnnularCurrentLow Grad.AnnularLowEnergy Grad.AnnularKernelL2
open Grad.BoundaryKernelAction Grad.PhaseAlgebra Grad.BoundaryTrace Grad.ActualBoundaryPrimitives

variable (parameters : PhaseParameters) (L lower : ℝ) (lengthPositive : 0 < L)
  (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)

/-- The negative-half x trace is the same canonical weak graph endpoint. -/
theorem lowOuterXNegative_translation (tau : OrbitParameter) (field : lowEnergyGraph lower L positive) :
    lowOuterXNegative parameters lower L lengthPositive positive lowerHalf
      (lowTranslation lower L positive tau field) =
    orbitLpAction (ComplexEuclidean 1) tau
      (lowOuterXNegative parameters lower L lengthPositive positive lowerHalf field) := by
  apply lp.ext
  funext mode
  rw [orbitLpAction_apply]
  by_cases retained : |mode.1| = 1 ∨ |mode.1| = 2
  · rw [lowOuterXNegative_retained parameters lower L lengthPositive positive lowerHalf _ ⟨mode, retained⟩,
      lowOuterXNegative_retained parameters lower L lengthPositive positive lowerHalf field ⟨mode, retained⟩,
      lowEnergyEndpoint_translation]
    rw [smul_comm _ (orbitCharacter tau mode), smul_comm _ (orbitCharacter tau mode)]
  · rw [lowOuterXNegative_outside parameters lower L lengthPositive positive lowerHalf _ mode retained,
      lowOuterXNegative_outside parameters lower L lengthPositive positive lowerHalf field mode retained, smul_zero]

/-- The positive-half xi trace retains its actual a_m mu normalization. -/
theorem lowOuterXiPositive_translation (tau : OrbitParameter) (field : lowEnergyGraph lower L positive) :
    lowOuterXiPositive parameters lower L lengthPositive positive lowerHalf
      (lowTranslation lower L positive tau field) =
    orbitLpAction (ComplexEuclidean 1) tau
      (lowOuterXiPositive parameters lower L lengthPositive positive lowerHalf field) := by
  apply lp.ext
  funext mode
  rw [orbitLpAction_apply]
  by_cases retained : |mode.1| = 1 ∨ |mode.1| = 2
  · rw [lowOuterXiPositive_retained parameters lower L lengthPositive positive lowerHalf _ ⟨mode, retained⟩,
      lowOuterXiPositive_retained parameters lower L lengthPositive positive lowerHalf field ⟨mode, retained⟩,
      lowEnergyEndpoint_translation]
    rw [smul_comm _ (orbitCharacter tau mode), smul_comm _ (orbitCharacter tau mode)]
  · rw [lowOuterXiPositive_outside parameters lower L lengthPositive positive lowerHalf _ mode retained,
      lowOuterXiPositive_outside parameters lower L lengthPositive positive lowerHalf field mode retained, smul_zero]

variable (angular cell : ℕ)

def sevenSlotTranslationEquivalence (tau : OrbitParameter) :
    SevenSlotTrace parameters angular cell ≃ₗᵢ[ℂ] SevenSlotTrace parameters angular cell :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin 7 => orbitLpEquivalence (ComplexEuclidean 1) tau)

theorem sevenSlotTranslation_apply (tau : OrbitParameter) (input : SevenSlotTrace parameters angular cell) (slot : Fin 7) :
    sevenSlotTranslationEquivalence parameters angular cell tau input slot =
      orbitLpAction (ComplexEuclidean 1) tau (input slot) := rfl

theorem sevenSlotFlatten_translation (tau : OrbitParameter) (input : SevenSlotTrace parameters angular cell) :
    sevenSlotFlatten parameters angular cell (sevenSlotTranslationEquivalence parameters angular cell tau input) =
      orbitLpAction (ComplexEuclidean 7) tau (sevenSlotFlatten parameters angular cell input) := by
  apply lp.ext
  funext mode
  apply PiLp.ext
  intro slot
  rfl

theorem positiveRotation_translation (tau : OrbitParameter) (input : PositiveTrace parameters angular cell 1) :
    positiveRotationToNegative parameters angular cell (orbitLpAction (ComplexEuclidean 1) tau input) =
      orbitLpAction (ComplexEuclidean 1) tau (positiveRotationToNegative parameters angular cell input) := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  rw [negativeCoefficient_translation, positiveRotationToNegative_coefficient,
    positiveRotationToNegative_coefficient, positiveCoefficient_translation]
  exact smul_comm _ _ _

theorem positiveCell_translation (tau : OrbitParameter) (input : PositiveTrace parameters angular cell 1) :
    positiveCellToNegative parameters angular cell (orbitLpAction (ComplexEuclidean 1) tau input) =
      orbitLpAction (ComplexEuclidean 1) tau (positiveCellToNegative parameters angular cell input) := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  rw [negativeCoefficient_translation, positiveCellToNegative_coefficient,
    positiveCellToNegative_coefficient, positiveCoefficient_translation]
  exact smul_comm _ _ _

theorem positiveValue_translation (tau : OrbitParameter) (input : PositiveTrace parameters angular cell 1) :
    positiveToNegative parameters angular cell (orbitLpAction (ComplexEuclidean 1) tau input) =
      orbitLpAction (ComplexEuclidean 1) tau (positiveToNegative parameters angular cell input) := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  rw [negativeCoefficient_translation, positiveToNegative_coefficient,
    positiveToNegative_coefficient, positiveCoefficient_translation]

/-- Exact seven physical boundary slots with the genuine zero source packet. -/
theorem actualSevenZero_translation (tau : OrbitParameter)
    (x : NegativeTrace parameters angular cell 1) (xi : PositiveTrace parameters angular cell 1) :
    actualSevenSlotTrace parameters L angular cell (orbitLpAction (ComplexEuclidean 1) tau x)
      (orbitLpAction (ComplexEuclidean 1) tau xi) 0 =
    sevenSlotTranslationEquivalence parameters angular cell tau (actualSevenSlotTrace parameters L angular cell x xi 0) := by
  apply PiLp.ext
  intro slot
  have first := actualSevenSlotTrace_components parameters L angular cell
    (orbitLpAction (ComplexEuclidean 1) tau x) (orbitLpAction (ComplexEuclidean 1) tau xi) 0
  have second := actualSevenSlotTrace_components parameters L angular cell x xi 0
  rw [sevenSlotTranslation_apply, congrFun first slot, congrFun second slot]
  fin_cases slot <;> simp [positiveRotation_translation, positiveCell_translation, positiveValue_translation]

/-- Flattening preserves the actual low outer trace and all fixed derivative slots. -/
theorem lowOuterSevenFlatten_translation (tau : OrbitParameter) (field : lowEnergyGraph lower L positive) :
    sevenSlotFlatten parameters 0 0
      (lowOuterSevenTrace parameters lower L lengthPositive positive lowerHalf (lowTranslation lower L positive tau field)) =
    orbitLpAction (ComplexEuclidean 7) tau
      (sevenSlotFlatten parameters 0 0 (lowOuterSevenTrace parameters lower L lengthPositive positive lowerHalf field)) := by
  rw [lowOuterSevenTrace_apply, lowOuterXNegative_translation, lowOuterXiPositive_translation,
    actualSevenZero_translation, sevenSlotFlatten_translation]
  rfl

end Grad.AnnularCrossOrbit

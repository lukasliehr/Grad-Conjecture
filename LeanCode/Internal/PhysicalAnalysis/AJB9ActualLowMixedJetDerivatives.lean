import AJB3ActualNormalizedLowOrbitDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularLowOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularKernelOrbit
open Grad.AnnularKernelL2 Grad.AnnularKernelContinuity Grad.BoundaryKernelAction Grad.AnnularReconstruction

section Differential
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

theorem orbitDifferential_map (mapping : E →L[ℂ] F) (angular cell : E) :
    (mapping.restrictScalars ℝ).comp (orbitDifferential angular cell) =
      orbitDifferential (mapping angular) (mapping cell) := by
  apply ContinuousLinearMap.ext
  intro step
  change mapping (orbitDifferential angular cell step) = orbitDifferential (mapping angular) (mapping cell) step
  simp only [orbitDifferential_apply, map_add, map_smul]

theorem orbitDifferential_add (a b c d : E) :
    orbitDifferential a b + orbitDifferential c d = orbitDifferential (a + c) (b + d) := by
  apply ContinuousLinearMap.ext
  intro step
  simp only [add_apply, orbitDifferential_apply, smul_add]
  abel

end Differential

variable (parameters : PhaseParameters) (length compact lower : ℝ)
  (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
  (state : RetainedInverseState parameters length compact)

theorem actualLowRowOrbitJet_hasFDerivAt (row : Fin 3) (tau : OrbitParameter) (angular cell : ℕ) :
    HasFDerivAt (fun sigma => actualLowRowOrbitJet parameters length compact lower positive bounded state row sigma angular cell)
      (orbitDifferential
        (actualLowRowOrbitJet parameters length compact lower positive bounded state row tau (angular + 1) cell)
        (actualLowRowOrbitJet parameters length compact lower positive bounded state row tau angular (cell + 1))) tau :=
  radialOrbitJetAction_hasFDerivAt _ _ _ _ _ _ _ _ _ _

theorem actualLowResponseOrbitJet_assembly (tau : OrbitParameter) (angular cell : ℕ) :
    actualLowResponseOrbitJet parameters length compact lower lengthPositive positive bounded state tau angular cell =
      actualLowRowAssembly lower (lowFirstOutput parameters lower length)
        (lowNormalizedSevenInput parameters lower length lengthPositive positive)
        (actualLowRowOrbitJet parameters length compact lower positive bounded state 0 tau angular cell) +
      actualLowRowAssembly lower (lowCellOutput lower length positive)
        (lowNormalizedSevenInput parameters lower length lengthPositive positive)
        (actualLowRowOrbitJet parameters length compact lower positive bounded state 1 tau angular cell) +
      actualLowRowAssembly lower (lowAngularOutput lower length positive)
        (lowNormalizedSevenInput parameters lower length lengthPositive positive)
        (actualLowRowOrbitJet parameters length compact lower positive bounded state 2 tau angular cell) := by
  apply ContinuousLinearMap.ext
  intro field
  rfl

theorem actualLowResponseOrbitJet_hasFDerivAt (tau : OrbitParameter) (angular cell : ℕ) :
    HasFDerivAt (fun sigma => actualLowResponseOrbitJet parameters length compact lower lengthPositive positive bounded state sigma angular cell)
      (orbitDifferential
        (actualLowResponseOrbitJet parameters length compact lower lengthPositive positive bounded state tau (angular + 1) cell)
        (actualLowResponseOrbitJet parameters length compact lower lengthPositive positive bounded state tau angular (cell + 1))) tau := by
  have rowDerivative (output : DivisionRow 1 lower →L[ℂ] LowEnergyBulk lower) (row : Fin 3) :=
    ((actualLowRowAssembly lower output (lowNormalizedSevenInput parameters lower length lengthPositive positive)).restrictScalars ℝ).hasFDerivAt.comp tau
      (actualLowRowOrbitJet_hasFDerivAt parameters length compact lower positive bounded state row tau angular cell)
  simp only [orbitDifferential_map] at rowDerivative
  have combined := ((rowDerivative (lowFirstOutput parameters lower length) 0).add
    (rowDerivative (lowCellOutput lower length positive) 1)).add
    (rowDerivative (lowAngularOutput lower length positive) 2)
  simp only [orbitDifferential_add, ← actualLowResponseOrbitJet_assembly] at combined
  have assembled : (fun sigma => actualLowResponseOrbitJet parameters length compact lower lengthPositive positive bounded state sigma angular cell) =
      (fun sigma =>
        actualLowRowAssembly lower (lowFirstOutput parameters lower length)
          (lowNormalizedSevenInput parameters lower length lengthPositive positive)
          (actualLowRowOrbitJet parameters length compact lower positive bounded state 0 sigma angular cell) +
        actualLowRowAssembly lower (lowCellOutput lower length positive)
          (lowNormalizedSevenInput parameters lower length lengthPositive positive)
          (actualLowRowOrbitJet parameters length compact lower positive bounded state 1 sigma angular cell) +
        actualLowRowAssembly lower (lowAngularOutput lower length positive)
          (lowNormalizedSevenInput parameters lower length lengthPositive positive)
          (actualLowRowOrbitJet parameters length compact lower positive bounded state 2 sigma angular cell)) := by
    funext sigma
    exact actualLowResponseOrbitJet_assembly parameters length compact lower lengthPositive positive bounded state sigma angular cell
  rw [assembled]
  exact combined

/-- The completed actual first derivative has exactly the two normalized
physical first jets as its columns. -/
theorem actualLowGeneratorDifferential_columns (tau : OrbitParameter) :
    actualLowGeneratorDifferential parameters length compact lower lengthPositive positive bounded state tau =
      orbitDifferential
        (actualLowResponseOrbitJet parameters length compact lower lengthPositive positive bounded state tau 1 0)
        (actualLowResponseOrbitJet parameters length compact lower lengthPositive positive bounded state tau 0 1) := by
  unfold actualLowGeneratorDifferential actualLowRowDifferential
  rw [orbitDifferential_map, orbitDifferential_map, orbitDifferential_map, orbitDifferential_add, orbitDifferential_add]
  rw [← actualLowResponseOrbitJet_assembly, ← actualLowResponseOrbitJet_assembly]

end Grad.AnnularLowOrbit

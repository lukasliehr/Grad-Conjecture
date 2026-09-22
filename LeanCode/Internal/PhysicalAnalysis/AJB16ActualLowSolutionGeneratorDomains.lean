import AJB13SameLowInverseSmoothness
import AJB15CompleteLpGeneratorMembership

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal ContDiff
namespace Grad.AnnularLowOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularKernelOrbit
open Grad.AnnularKernelL2 Grad.AnnularKernelContinuity Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularCoupledOrbit Grad.AnnularCurrentEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularInverseCalculus Grad.AnnularOrbitGenerators

/-- Application of complex-linear operators is a real bounded bilinear map. -/
theorem complexOperatorApplication_contDiff {P E F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
    (operator : P → E →L[ℂ] F) (field : P → E)
    (operatorSmooth : ContDiff ℝ ∞ operator) (fieldSmooth : ContDiff ℝ ∞ field) :
    ContDiff ℝ ∞ (fun point => operator point (field point)) :=
  ((ContinuousLinearMap.apply ℂ F).flip.bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff.comp₂ operatorSmooth fieldSmooth

theorem orbitCharacter_cell (time : ℝ) (mode : ℤ × ℤ) :
    orbitCharacter (0, time) mode = cellExponential mode.2 time := by
  simp [orbitCharacter, orbitAngle, cellExponential, mul_assoc]

variable (parameters : PhaseParameters) (length compact lower : ℝ)
  (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
  (state : RetainedInverseState parameters length compact)

theorem actualLowInverseOrbit_translation (tau : OrbitParameter) (data : LowEnergyData lower) :
    actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state tau
      (lowDataTranslationEquivalence lower tau data) =
        lowTranslation lower length positive tau
          (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state data) := by
  change lowTranslation lower length positive tau
    (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state
      ((lowDataTranslationEquivalence lower tau).symm (lowDataTranslationEquivalence lower tau data))) = _
  rw [(lowDataTranslationEquivalence lower tau).symm_apply_apply]

/-- The actual graph orbit is smooth when the independently prescribed
original data have a smooth character orbit; the inverse derivative is essential. -/
theorem actualLowSolutionCellOrbit_contDiff
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      lowCurrentNeighborhood parameters length compact)
    (data : LowEnergyData lower)
    (dataSmooth : ContDiff ℝ ∞ (fun time : ℝ => lowDataTranslationEquivalence lower (0, time) data)) :
    ContDiff ℝ ∞ (fun time : ℝ => lowTranslation lower length positive (0, time)
      (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state data)) := by
  have inverseSmooth : ContDiff ℝ ∞ (fun time : ℝ =>
      actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state (0, time)) :=
    (actualLowInverseOrbit_contDiff parameters length compact lower lengthPositive positive bounded state small).comp
      (contDiff_const.prodMk contDiff_id)
  have combined := complexOperatorApplication_contDiff (P := ℝ)
    (E := LowEnergyData lower) (F := lowEnergyGraph lower length positive)
    (fun time => actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state (0, time))
    (fun time => lowDataTranslationEquivalence lower (0, time) data) inverseSmooth dataSmooth
  have same : (fun time : ℝ =>
      actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state (0, time)
        (lowDataTranslationEquivalence lower (0, time) data)) =
      (fun time : ℝ => lowTranslation lower length positive (0, time)
        (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state data)) := by
    funext time
    exact actualLowInverseOrbit_translation parameters length compact lower lengthPositive positive bounded state (0, time) data
  rw [same] at combined
  exact combined

/-- The derivative vector is an element of the genuine original ADY graph. -/
def actualLowSolutionCellGenerator (data : LowEnergyData lower) (order : ℕ) :
    lowEnergyGraph lower length positive :=
  iteratedDeriv order (fun time : ℝ => lowTranslation lower length positive (0, time)
    (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state data)) 0

/-- Actual all-order Fourier-generator membership of the SAME solution,
on BOTH stored graph coordinates, proved using the complete norm derivatives. -/
theorem actualLowSolutionCellGenerator_coefficients
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      lowCurrentNeighborhood parameters length compact)
    (data : LowEnergyData lower)
    (dataSmooth : ContDiff ℝ ∞ (fun time : ℝ => lowDataTranslationEquivalence lower (0, time) data))
    (order : ℕ) (coordinate : Fin 2) (index : LowAnnularIndex) :
    (actualLowSolutionCellGenerator parameters length compact lower lengthPositive positive bounded state data order).val coordinate index =
      (Complex.I * (index.2.val.2 : ℂ)) ^ order •
        (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state data).val coordinate index := by
  let solution := lowCurrentInverse parameters length compact lower lengthPositive positive bounded state data
  let orbit := fun time : ℝ => lowTranslation lower length positive (0, time) solution
  have smooth : ContDiff ℝ ∞ orbit :=
    actualLowSolutionCellOrbit_contDiff parameters length compact lower lengthPositive positive bounded state small data dataSmooth
  exact smoothLpCharacterOrbit_coordinates (lowStoredCoordinate lower length positive coordinate) orbit smooth
    (fun index : LowAnnularIndex => index.2.val.2) (solution.val coordinate)
    (fun time index => by change orbitCharacter (0, time) index.2.val • solution.val coordinate index = _; rw [orbitCharacter_cell])
    order index

/-- Complete Hilbert summability of every actual cell-generator power. -/
theorem actualLowSolutionCellGenerator_memℓp
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      lowCurrentNeighborhood parameters length compact)
    (data : LowEnergyData lower)
    (dataSmooth : ContDiff ℝ ∞ (fun time : ℝ => lowDataTranslationEquivalence lower (0, time) data))
    (order : ℕ) (coordinate : Fin 2) :
    Memℓp (fun index : LowAnnularIndex => (Complex.I * (index.2.val.2 : ℂ)) ^ order •
      (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state data).val coordinate index) 2 := by
  have same : (fun index : LowAnnularIndex => (Complex.I * (index.2.val.2 : ℂ)) ^ order •
      (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state data).val coordinate index) =
      fun index => (actualLowSolutionCellGenerator parameters length compact lower lengthPositive positive bounded state data order).val coordinate index := by
    funext index
    exact (actualLowSolutionCellGenerator_coefficients parameters length compact lower lengthPositive positive bounded state small data dataSmooth order coordinate index).symm
  rw [same]
  exact ((actualLowSolutionCellGenerator parameters length compact lower lengthPositive positive bounded state data order).val coordinate).property

end Grad.AnnularLowOrbit

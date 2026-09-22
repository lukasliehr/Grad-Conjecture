import AJA13RealOrbitColumns
import AJA9ActualZeroFormOrbit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped ContDiff
namespace Grad.AnnularHighInverseOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse
open Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit Grad.BoundaryKernelAction

private theorem linearSmoothComp {P E F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (mapping : E →L[ℝ] F) (f : P → E)
    (smooth : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fun point => mapping (f point)) :=
  mapping.contDiff.comp smooth

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)

def currentHighFormOrbitJet (angular cell : ℕ) (tau : OrbitParameter) :=
  highBulkFormOrbitJet parameters L lower positive lengthPositive widthHalf widthLength compact
    (lowerHalf.trans (by norm_num)) state tau angular cell +
  highBoundaryFormOrbitJet parameters L lower positive lowerHalf lengthPositive compact state tau angular cell

theorem bulkJet_hasFDerivAt (angular cell : ℕ) (tau : OrbitParameter) :
    HasFDerivAt (fun sigma => highBulkFormOrbitJet parameters L lower positive lengthPositive widthHalf widthLength compact
      (lowerHalf.trans (by norm_num)) state sigma angular cell)
      (orbitColumns
        (highBulkFormOrbitJet parameters L lower positive lengthPositive widthHalf widthLength compact (lowerHalf.trans (by norm_num)) state tau (angular + 1) cell)
        (highBulkFormOrbitJet parameters L lower positive lengthPositive widthHalf widthLength compact (lowerHalf.trans (by norm_num)) state tau angular (cell + 1))) tau := by
  have coefficient := radialOrbitJetAction_hasFDerivAt parameters
    (radialEliminatedBulkKernel parameters L compact state) (radialEliminatedBulkKernel_regular parameters L compact state)
    0 lower positive (lowerHalf.trans (by norm_num)) tau angular cell
  have derivative := HasFDerivAt.comp (𝕜 := ℝ) (E := OrbitParameter)
    (F := DivisionRow 8 lower →L[ℂ] DivisionRow 3 lower)
    (G := annularEnergySpace lower L positive →L[ℝ] annularEnergySpace lower L positive →L[ℝ] ℝ)
    tau (ContinuousLinearMap.hasFDerivAt
      (E := DivisionRow 8 lower →L[ℂ] DivisionRow 3 lower)
      (F := annularEnergySpace lower L positive →L[ℝ] annularEnergySpace lower L positive →L[ℝ] ℝ)
      (bulkPairingAction parameters L lower positive lengthPositive widthHalf widthLength)) coefficient
  apply derivative.congr_fderiv
  exact orbitDifferential_comp
    (E := DivisionRow 8 lower →L[ℂ] DivisionRow 3 lower)
    (F := annularEnergySpace lower L positive →L[ℝ] annularEnergySpace lower L positive →L[ℝ] ℝ)
    (bulkPairingAction parameters L lower positive lengthPositive widthHalf widthLength)
    (actualEliminatedOrbitJet parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 tau (angular + 1) cell)
    (actualEliminatedOrbitJet parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 tau angular (cell + 1))

theorem boundaryJet_hasFDerivAt (angular cell : ℕ) (tau : OrbitParameter) :
    HasFDerivAt (fun sigma => highBoundaryFormOrbitJet parameters L lower positive lowerHalf lengthPositive compact state sigma angular cell)
      (orbitColumns
        (highBoundaryFormOrbitJet parameters L lower positive lowerHalf lengthPositive compact state tau (angular + 1) cell)
        (highBoundaryFormOrbitJet parameters L lower positive lowerHalf lengthPositive compact state tau angular (cell + 1))) tau := by
  apply (highBoundaryFormOrbitJet_hasFDerivAt parameters L lower positive lowerHalf lengthPositive compact state tau angular cell).congr_fderiv
  exact orbitDifferential_comp
    (E := NegativeTrace parameters 0 0 3 →L[ℂ] NegativeTrace parameters 0 0 1)
    (F := annularEnergySpace lower L positive →L[ℝ] annularEnergySpace lower L positive →L[ℝ] ℝ)
    (boundaryPairingAction parameters L lower positive lowerHalf lengthPositive)
    _ _

theorem currentHighFormOrbitJet_hasFDerivAt (angular cell : ℕ) (tau : OrbitParameter) :
    HasFDerivAt (currentHighFormOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell)
      (orbitColumns
        (currentHighFormOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state (angular + 1) cell tau)
        (currentHighFormOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular (cell + 1) tau)) tau := by
  exact sumOrbit_hasFDerivAt _ _ _ _ _ _ tau
    (bulkJet_hasFDerivAt parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell tau)
    (boundaryJet_hasFDerivAt parameters L compact lower positive lowerHalf lengthPositive state angular cell tau)

theorem currentHighFormOrbitJet_zero (tau : OrbitParameter) :
    currentHighFormOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 tau =
      currentHighFormOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau := by
  unfold currentHighFormOrbitJet currentHighFormOrbit highBulkFormOrbitJet highBulkFormOrbit actualEliminatedOrbitJet actualEliminatedOrbit
  rw [radialOrbitJetAction_zero]

theorem currentHighFormOrbit_contDiff :
    ContDiff ℝ ∞ (currentHighFormOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state) := by
  have smooth := orbitTower_contDiff
    (currentHighFormOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state)
    (currentHighFormOrbitJet_hasFDerivAt parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state) 0 0
  have equality := funext (currentHighFormOrbitJet_zero parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state)
  rw [equality] at smooth
  exact smooth

theorem currentHighZeroFormOrbit_contDiff :
    ContDiff ℝ ∞ (currentHighZeroFormOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state) := by
  exact linearSmoothComp
    (P := OrbitParameter)
    (E := annularEnergySpace lower L positive →L[ℝ] annularEnergySpace lower L positive →L[ℝ] ℝ)
    (F := annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ]
      annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ)
    (formRestriction (annularZeroRealInclusion lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive))
    (currentHighFormOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state)
    (currentHighFormOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state)

end Grad.AnnularHighInverseOrbit

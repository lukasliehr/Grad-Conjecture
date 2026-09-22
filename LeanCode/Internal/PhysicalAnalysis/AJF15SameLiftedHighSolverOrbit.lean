import AJF14ActualLiftTestFunctionalOrbit
import AJA16ActualHighInverseSmooth

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2000
open scoped ContDiff
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularHighInverseOrbit Grad.AnnularCurrentInverse Grad.AnnularCurrentEnergy
open Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit Grad.AnnularReconstruction Grad.CartesianState
open Grad.AnnularStrongOrbit Grad.AnnularUniformBoundary Grad.AnnularCurrentSolution

section Composition
variable {P E F G : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem realOperatorComposition_contDiff (outer : P → F →L[ℝ] G) (inner : P → E →L[ℝ] F)
    (outerSmooth : ContDiff ℝ ∞ outer) (innerSmooth : ContDiff ℝ ∞ inner) :
    ContDiff ℝ ∞ (fun point => (outer point).comp (inner point)) :=
  (ContinuousLinearMap.compL ℝ E F G).isBoundedBilinearMap.contDiff.comp₂ outerSmooth innerSmooth
end Composition

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
  (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
  (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)
  (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)

/-- The SAME AEL inverse, included into its original full energy graph. -/
def highSourceSolverOrbit (tau : OrbitParameter) :
    (annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ) →L[ℝ]
      annularEnergySpace lower L positive :=
  (annularZeroRealInclusion lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive).comp
    (currentHighInverseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau)

/-- Correction of the genuine physical incoming lift by that same inverse,
using the actual complete current form restricted only in the test slot. -/
def highIncomingSolverOrbit (tau : OrbitParameter) :
    AnnularBoundary →L[ℝ] annularEnergySpace lower L positive :=
  (physicalIncomingLift lower L positive lowerHalf lengthPositive).restrictScalars ℝ -
    (highSourceSolverOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau).comp
      ((liftedTestFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 tau).comp
        ((physicalIncomingLift lower L positive lowerHalf lengthPositive).restrictScalars ℝ))

theorem highSourceSolverOrbit_contDiff :
    ContDiff ℝ ∞ (highSourceSolverOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) :=
  realOperatorComposition_contDiff _ _ contDiff_const
    (currentHighInverseOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)

theorem highIncomingSolverOrbit_contDiff :
    ContDiff ℝ ∞ (highIncomingSolverOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) :=
  contDiff_const.sub (realOperatorComposition_contDiff _ _
    (highSourceSolverOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (realOperatorComposition_contDiff _ _
      (liftedTestFunctionalOrbitJet_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0)
      contDiff_const))

def fullHighEnergySolverOrbit (tau : OrbitParameter)
    (source : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ)
    (datum : AnnularBoundary) : annularEnergySpace lower L positive :=
  highSourceSolverOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau source +
    highIncomingSolverOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau datum

theorem fullHighEnergySolverOrbit_formula (tau : OrbitParameter)
    (source : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ)
    (datum : AnnularBoundary) :
    fullHighEnergySolverOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau source datum =
      physicalIncomingLift lower L positive lowerHalf lengthPositive datum +
        (currentHighInverseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau
          (source - liftedTestFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 tau
            (physicalIncomingLift lower L positive lowerHalf lengthPositive datum))).val := by
  change _ = physicalIncomingLift lower L positive lowerHalf lengthPositive datum +
    highSourceSolverOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau
      (source - liftedTestFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 tau
        (physicalIncomingLift lower L positive lowerHalf lengthPositive datum))
  rw [map_sub]
  let solve := highSourceSolverOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau
  let lift := physicalIncomingLift lower L positive lowerHalf lengthPositive datum
  let term := liftedTestFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 tau lift
  change solve source + (lift - solve term) = lift + (solve source - solve term)
  abel

end Grad.AnnularHighGenerators

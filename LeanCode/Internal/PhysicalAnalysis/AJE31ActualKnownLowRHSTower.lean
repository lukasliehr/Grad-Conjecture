import AJE30KnownLowSourceCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 300000
open scoped ContDiff
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularReconstruction
open Grad.AnnularHighInverseOrbit Grad.AnnularCrossOrbit Grad.AnnularKernelL2
open Grad.AnnularKnownLow Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularLowOrbit

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (state : RetainedInverseState parameters length compact)

def knownLowOutput (row : Fin 3) : DivisionRow 1 lower →L[ℂ] LowEnergyBulk lower :=
  ![lowFirstOutput parameters lower length,lowCellOutput lower length positive,lowAngularOutput lower length positive] row

/-- Apply a genuine pre-Q coefficient row to the shared seven source slots,
then perform the original low output normalization and bulk inclusion. -/
def knownLowRowOperatorMap (row : Fin 3) :
    (DivisionRow 7 lower →L[ℂ] DivisionRow 1 lower) →L[ℝ]
      (KnownLowData lower →L[ℝ] LowEnergyData lower) :=
  ((ContinuousLinearMap.compL ℝ (KnownLowData lower) (LowEnergyBulk lower) (LowEnergyData lower))
      (knownLowBulkIntoData lower)).comp
    (((ContinuousLinearMap.compL ℝ (KnownLowData lower) (DivisionRow 1 lower) (LowEnergyBulk lower))
      ((knownLowOutput parameters length lower positive row).restrictScalars ℝ)).comp
      (realInputPrecompose (knownLowSourceInput lower)))

def knownLowRowOperatorJet (row : Fin 3) (angular cell : ℕ) (tau : OrbitParameter) :
    KnownLowData lower →L[ℝ] LowEnergyData lower :=
  knownLowRowOperatorMap parameters length lower positive row
    (actualLowRowOrbitJet parameters length compact lower positive bounded state row tau angular cell)

theorem knownLowRowOperatorJet_hasFDerivAt (row : Fin 3) (angular cell : ℕ) (tau : OrbitParameter) :
    HasFDerivAt (knownLowRowOperatorJet parameters length compact lower positive bounded state row angular cell)
      (orbitColumns (knownLowRowOperatorJet parameters length compact lower positive bounded state row (angular + 1) cell tau)
        (knownLowRowOperatorJet parameters length compact lower positive bounded state row angular (cell + 1) tau)) tau :=
  mappedOrbit_hasFDerivAt (knownLowRowOperatorMap parameters length lower positive row) _ _ _ tau
    (radialOrbitJetAction_hasFDerivAt parameters (lowPhysicalRowKernel parameters length compact state row)
      (lowPhysicalRowKernel_regular parameters length compact state row) 0 lower positive bounded tau angular cell)

/-- Full actual AIR known low RHS tower, including the unchanged direct f,
Rg and independent incoming datum. No row is replaced by a generic source. -/
def knownLowDataOrbitJet (angular cell : ℕ) (tau : OrbitParameter) :
    KnownLowData lower →L[ℝ] LowEnergyData lower :=
  knownLowRowOperatorJet parameters length compact lower positive bounded state 0 angular cell tau +
    knownLowRowOperatorJet parameters length compact lower positive bounded state 1 angular cell tau +
    knownLowRowOperatorJet parameters length compact lower positive bounded state 2 angular cell tau +
    constantOrbitJet (knownLowDirectData parameters lower length positive) angular cell tau

theorem knownLowDataOrbitJet_hasFDerivAt (angular cell : ℕ) (tau : OrbitParameter) :
    HasFDerivAt (knownLowDataOrbitJet parameters length compact lower positive bounded state angular cell)
      (orbitColumns (knownLowDataOrbitJet parameters length compact lower positive bounded state (angular + 1) cell tau)
        (knownLowDataOrbitJet parameters length compact lower positive bounded state angular (cell + 1) tau)) tau := by
  exact sumOrbit_hasFDerivAt _ _ _ _ _ _ tau
    (sumOrbit_hasFDerivAt _ _ _ _ _ _ tau
      (sumOrbit_hasFDerivAt _ _ _ _ _ _ tau
        (knownLowRowOperatorJet_hasFDerivAt parameters length compact lower positive bounded state 0 angular cell tau)
        (knownLowRowOperatorJet_hasFDerivAt parameters length compact lower positive bounded state 1 angular cell tau))
      (knownLowRowOperatorJet_hasFDerivAt parameters length compact lower positive bounded state 2 angular cell tau))
    (constantOrbitJet_hasFDerivAt (knownLowDirectData parameters lower length positive) angular cell tau)

theorem knownLowDataOrbitJet_contDiff (angular cell : ℕ) :
    ContDiff ℝ ∞ (knownLowDataOrbitJet parameters length compact lower positive bounded state angular cell) :=
  orbitTower_contDiff _ (knownLowDataOrbitJet_hasFDerivAt parameters length compact lower positive bounded state) angular cell

end Grad.AnnularStrongOrbit

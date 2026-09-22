import AJE13ActualKnownDataCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open scoped ContDiff
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularReconstruction
open Grad.AnnularHighInverseOrbit Grad.AnnularCrossOrbit Grad.AnnularKernelL2

local instance knownAmbientNormed (parameters : PhaseParameters) (lower : ℝ) :
    NormedAddCommGroup (ActualHighKnownAmbient parameters lower 0 0) := inferInstance
local instance knownAmbientSeminormed (parameters : PhaseParameters) (lower : ℝ) :
    SeminormedAddCommGroup (ActualHighKnownAmbient parameters lower 0 0) :=
  (knownAmbientNormed parameters lower).toSeminormedAddCommGroup
local instance knownAmbientRealNormed (parameters : PhaseParameters) (lower : ℝ) :
    NormedSpace ℝ (ActualHighKnownAmbient parameters lower 0 0) := by
  letI : NormedSpace ℝ (HighKnownBulkHilbert lower) := inferInstance
  letI : NormedSpace ℝ (HighKnownGraphHilbert parameters lower) := inferInstance
  letI : NormedSpace ℝ (HighKnownBoundaryHilbert parameters 0 0) := inferInstance
  letI : NormedSpace ℝ (HighKnownGraphBoundaryHilbert parameters lower 0 0) := inferInstance
  exact inferInstance
local instance knownAmbientRealModule (parameters : PhaseParameters) (lower : ℝ) :
    Module ℝ (ActualHighKnownAmbient parameters lower 0 0) :=
  (knownAmbientRealNormed parameters lower).toModule

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (state : RetainedInverseState parameters L compact)

/-- Complete literal known bulk coefficient jet, with original F0,RF0,F2,
f,g,qc,rqv, and physical power zero. -/
def knownBulkOrbitJet (angular cell : ℕ) (tau : OrbitParameter) :
    ActualHighKnownAmbient parameters lower 0 0 →L[ℝ] DivisionRow 3 lower :=
  realInputPrecompose (knownAmbientEight parameters lower 0 0)
      (actualEliminatedOrbitJet parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 tau angular cell) +
    constantOrbitJet (knownAmbientDirect parameters lower 0 0 positive) angular cell tau

theorem knownBulkOrbitJet_hasFDerivAt (angular cell : ℕ) (tau : OrbitParameter) :
    HasFDerivAt (knownBulkOrbitJet parameters L compact lower positive lowerHalf state angular cell)
      (orbitColumns (knownBulkOrbitJet parameters L compact lower positive lowerHalf state (angular + 1) cell tau)
        (knownBulkOrbitJet parameters L compact lower positive lowerHalf state angular (cell + 1) tau)) tau := by
  exact sumOrbit_hasFDerivAt _ _ _ _ _ _ tau
    (realInputPrecompose_hasFDerivAt (knownAmbientEight parameters lower 0 0) _ _ _ tau
      (radialOrbitJetAction_hasFDerivAt parameters (radialEliminatedBulkKernel parameters L compact state)
        (radialEliminatedBulkKernel_regular parameters L compact state) 0 lower positive (lowerHalf.trans (by norm_num)) tau angular cell))
    (constantOrbitJet_hasFDerivAt (knownAmbientDirect parameters lower 0 0 positive) angular cell tau)

def knownBoundaryOrbitJet (angular cell : ℕ) (tau : OrbitParameter) :
    ActualHighKnownAmbient parameters lower 0 0 →L[ℝ] NegativeTrace parameters 0 0 1 :=
  realInputPrecompose (highKnownDatumProjection parameters lower 0 0)
      (actualBoundaryInverseOrbitJet parameters L compact state angular cell tau) +
    realInputPrecompose (knownAmbientSourceTuple parameters lower 0 0 positive (lowerHalf.trans_lt (by norm_num)))
      (graphSourceLiftOrbitJet parameters L compact state.outerInverseState 0 0 angular cell tau)

theorem knownBoundaryOrbitJet_hasFDerivAt (angular cell : ℕ) (tau : OrbitParameter) :
    HasFDerivAt (knownBoundaryOrbitJet parameters L compact lower positive lowerHalf state angular cell)
      (orbitColumns (knownBoundaryOrbitJet parameters L compact lower positive lowerHalf state (angular + 1) cell tau)
        (knownBoundaryOrbitJet parameters L compact lower positive lowerHalf state angular (cell + 1) tau)) tau := by
  exact sumOrbit_hasFDerivAt _ _ _ _ _ _ tau
    (realInputPrecompose_hasFDerivAt (highKnownDatumProjection parameters lower 0 0) _ _ _ tau
      (actualBoundaryInverseOrbitJet_hasFDerivAt parameters L compact state angular cell tau))
    (realInputPrecompose_hasFDerivAt
      (knownAmbientSourceTuple parameters lower 0 0 positive (lowerHalf.trans_lt (by norm_num))) _ _ _ tau
      (graphSourceLiftOrbitJet_hasFDerivAt parameters L compact state.outerInverseState 0 0 angular cell tau))

theorem knownBulkOrbitJet_contDiff (angular cell : ℕ) :
    ContDiff ℝ ∞ (knownBulkOrbitJet parameters L compact lower positive lowerHalf state angular cell) :=
  orbitTower_contDiff _ (knownBulkOrbitJet_hasFDerivAt parameters L compact lower positive lowerHalf state) angular cell

theorem knownBoundaryOrbitJet_contDiff (angular cell : ℕ) :
    ContDiff ℝ ∞ (knownBoundaryOrbitJet parameters L compact lower positive lowerHalf state angular cell) :=
  orbitTower_contDiff _ (knownBoundaryOrbitJet_hasFDerivAt parameters L compact lower positive lowerHalf state) angular cell

end Grad.AnnularStrongOrbit

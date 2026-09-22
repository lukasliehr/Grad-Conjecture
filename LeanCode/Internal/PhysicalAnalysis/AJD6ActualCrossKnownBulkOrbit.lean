import AJD5ActualCrossKnownPackets
import AJD3OriginalClosedGraphOperatorLift

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularCrossMaps Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit
open Grad.ActualBoundaryPrimitives Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource
open Grad.AnnularReconstruction Grad.AnnularKernelL2 Grad.AnnularHighInverseOrbit

private def rightComposeComplex {X E F : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (input : X →L[ℂ] E) :
    (E →L[ℂ] F) →L[ℝ] (X →L[ℂ] F) :=
  ((ContinuousLinearMap.compL ℂ X E F).flip input).restrictScalars ℝ

private theorem composeAndAdd_smooth {P X E F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (family : P → E →L[ℂ] F)
    (input : X →L[ℂ] E) (direct : X →L[ℂ] F) (smooth : ContDiff ℝ ∞ family) :
    ContDiff ℝ ∞ (fun point => (family point).comp input + direct) :=
  ((rightComposeComplex (F := F) input).contDiff.comp smooth).add contDiff_const

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters L compact)

theorem actualEliminatedOrbit_contDiff :
    ContDiff ℝ ∞ (actualEliminatedOrbit parameters L compact lower positive bounded state 0) := by
  let jet := fun angular cell tau => actualEliminatedOrbitJet parameters L compact lower positive bounded state 0 tau angular cell
  have derivative (angular cell : ℕ) (tau : OrbitParameter) :
      HasFDerivAt (jet angular cell) (orbitColumns (jet (angular + 1) cell tau) (jet angular (cell + 1) tau)) tau :=
    radialOrbitJetAction_hasFDerivAt parameters (radialEliminatedBulkKernel parameters L compact state)
      (radialEliminatedBulkKernel_regular parameters L compact state) 0 lower positive bounded tau angular cell
  have smooth := orbitTower_contDiff jet derivative 0 0
  have equality : jet 0 0 = actualEliminatedOrbit parameters L compact lower positive bounded state 0 := by
    funext tau
    exact radialOrbitJetAction_zero parameters (radialEliminatedBulkKernel parameters L compact state)
      (radialEliminatedBulkKernel_regular parameters L compact state) 0 lower positive bounded tau
  rw [equality] at smooth
  exact smooth

def crossKnownBulkOrbit (tau : OrbitParameter) : CrossHighData parameters lower →L[ℂ] DivisionRow 3 lower :=
  (actualEliminatedOrbit parameters L compact lower positive bounded state 0 tau).comp (crossKnownEight parameters lower) +
    crossKnownDirect parameters lower

theorem crossKnownBulkOrbit_contDiff :
    ContDiff ℝ ∞ (crossKnownBulkOrbit parameters L compact lower positive bounded state) :=
  composeAndAdd_smooth _ _ _ (actualEliminatedOrbit_contDiff parameters L compact lower positive bounded state)

/-- Equality to the SAME actual known physical output with the genuinely translated datum. -/
theorem crossKnownBulkOrbit_apply (tau : OrbitParameter) (datum : CrossHighData parameters lower) :
    crossKnownBulkOrbit parameters L compact lower positive bounded state tau datum =
      orbitLpAction (RadialL2 3 lower) tau
        (actualHighKnownBulkOutput parameters L compact lower positive bounded state
          (crossKnownWeighted parameters lower (crossDataTranslation parameters lower (-tau) datum))
          (crossKnownAuxiliary parameters lower (crossDataTranslation parameters lower (-tau) datum))) := by
  unfold crossKnownBulkOrbit actualHighKnownBulkOutput
  rw [crossKnownEight_literal, crossKnownDirect_literal, map_add,
    crossKnownEight_covariant parameters lower (-tau) datum,
    crossKnownDirect_covariant parameters lower (-tau) datum, orbitLpAction_inverse,
    actualEliminatedOrbit_conjugation]
  rfl

end Grad.AnnularCrossOrbit

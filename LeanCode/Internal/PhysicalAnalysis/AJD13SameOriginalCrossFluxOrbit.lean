import AJD11SameCrossPhysicalOutputOrbit
import AJD12OriginalOmegaCoordinateCovariance

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularCrossMaps Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit
open Grad.ActualBoundaryPrimitives Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource
open Grad.AnnularReconstruction Grad.AnnularKernelL2 Grad.AnnularHighInverseOrbit
open Grad.AnnularCurrentBoundary Grad.AnnularCurrentInverse Grad.AnnularPhysicalSolution Grad.AnnularCurrentSolution

attribute [local instance] Grad.AnnularCrossOrbit.crossDataNormed Grad.AnnularCrossOrbit.crossDataSeminormed
  Grad.AnnularCrossOrbit.crossDataRealInner Grad.AnnularCrossOrbit.crossDataRealNormed Grad.AnnularCrossOrbit.crossDataRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)

def crossFluxOrbit (tau : OrbitParameter) :
    CrossHighData parameters lower →L[ℂ] Grad.AnnularOmegaGraph.annularOmegaGraph lower L positive lengthPositive :=
  (fluxTranslation lower L positive lengthPositive tau).comp
    ((crossFluxResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small).comp
      (crossDataTranslation parameters lower (-tau)))

/-- The ambient coordinates are exactly the original value and normalized radial derivative. -/
theorem crossFluxOrbit_inclusion (tau : OrbitParameter) :
    (Grad.AnnularOmegaGraph.annularOmegaGraph lower L positive lengthPositive).subtypeL.comp
      (crossFluxOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau) =
    (Grad.AnnularCurrentGreen.physicalOmegaCoordinates parameters lower L positive lengthPositive widthHalf widthLength).comp
      (crossPhysicalOutputOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau) := by
  apply ContinuousLinearMap.ext
  intro datum
  apply PiLp.ext
  intro coordinate
  apply lp.ext
  funext mode
  change (fluxTranslation lower L positive lengthPositive tau
    (crossFluxResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      (crossDataTranslation parameters lower (-tau) datum))).val coordinate mode =
    Grad.AnnularCurrentGreen.physicalOmegaCoordinates parameters lower L positive lengthPositive widthHalf widthLength
      (crossPhysicalOutputOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau datum) coordinate mode
  rw [fluxTranslation_apply, crossPhysicalOutputOrbit_apply, physicalOmegaCoordinates_covariant]
  rfl

/-- Smoothness in the SAME closed Domega graph follows from its actual ambient output. -/
theorem crossFluxOrbit_contDiff :
    ContDiff ℝ ∞ (crossFluxOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) := by
  apply graphOperator_contDiff_of_inclusion
    (Grad.AnnularOmegaGraph.annularOmegaGraph lower L positive lengthPositive) ∞
  have same : (fun tau => (Grad.AnnularOmegaGraph.annularOmegaGraph lower L positive lengthPositive).subtypeL.comp
      (crossFluxOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau)) =
    (fun tau => (Grad.AnnularCurrentGreen.physicalOmegaCoordinates parameters lower L positive lengthPositive widthHalf widthLength).comp
      (crossPhysicalOutputOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau)) :=
    funext (crossFluxOrbit_inclusion parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
  rw [same]
  exact complexOperatorComposition_contDiff _ _ contDiff_const
    (crossPhysicalOutputOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)

end Grad.AnnularCrossOrbit

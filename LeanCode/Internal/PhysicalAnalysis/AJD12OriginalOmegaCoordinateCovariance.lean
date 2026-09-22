import AJD8ActualKnownZeroFunctionalPullback

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularCrossMaps Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentGreen Grad.AnnularFluxTrace Grad.AnnularReconstruction

variable (lower : ℝ)

def FullOutputCovariant {dimension : ℕ} (mapping : DivisionRow dimension lower →L[ℂ] AnnularBulk lower) : Prop :=
  ∀ (tau : OrbitParameter) (field : DivisionRow dimension lower) (mode : HighAnnularMode),
    mapping (orbitLpAction (RadialL2 dimension lower) tau field) mode =
      orbitCharacter tau mode.val • mapping field mode

theorem highPhysicalOutput_covariant {dimension : ℕ} (slot : Fin dimension) :
    FullOutputCovariant lower (highPhysicalOutput lower slot) := by
  intro tau field mode
  change radialMatrixUnit lower 0 slot (orbitCharacter tau mode.val • field mode.val) =
    orbitCharacter tau mode.val • radialMatrixUnit lower 0 slot (field mode.val)
  exact map_smul (radialMatrixUnit lower 0 slot) _ _

theorem FullOutputCovariant.sub {dimension : ℕ}
    {first second : DivisionRow dimension lower →L[ℂ] AnnularBulk lower}
    (hf : FullOutputCovariant lower first) (hs : FullOutputCovariant lower second) :
    FullOutputCovariant lower (first - second) := by
  intro tau field mode
  change first (orbitLpAction (RadialL2 dimension lower) tau field) mode -
      second (orbitLpAction (RadialL2 dimension lower) tau field) mode =
    orbitCharacter tau mode.val • (first field mode - second field mode)
  rw [hf tau field mode, hs tau field mode, smul_sub]

theorem FullOutputCovariant.smul {dimension : ℕ}
    {mapping : DivisionRow dimension lower →L[ℂ] AnnularBulk lower}
    (covariant : FullOutputCovariant lower mapping) (scalar : ℂ) :
    FullOutputCovariant lower (scalar • mapping) := by
  intro tau field mode
  change scalar • mapping (orbitLpAction (RadialL2 dimension lower) tau field) mode =
    orbitCharacter tau mode.val • (scalar • mapping field mode)
  rw [covariant tau field mode, smul_comm]

variable (parameters : PhaseParameters) (L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L)
  (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))

theorem physicalOmegaOperator_postcompose_covariant {dimension : ℕ}
    {mapping : DivisionRow dimension lower →L[ℂ] AnnularBulk lower}
    (covariant : FullOutputCovariant lower mapping) (slot : Fin 4) :
    FullOutputCovariant lower
      ((physicalOmegaOperator parameters lower L positive lengthPositive widthHalf widthLength slot).comp mapping) := by
  intro tau field mode
  change scalarRadialMap lower (physicalOmegaFactor parameters lower L positive mode slot)
    (physicalOmegaFactorBound slot)
    (physicalOmegaFactor_bound parameters lower L positive lengthPositive widthHalf widthLength slot mode)
    (mapping (orbitLpAction (RadialL2 dimension lower) tau field) mode) =
    orbitCharacter tau mode.val • scalarRadialMap lower (physicalOmegaFactor parameters lower L positive mode slot)
      (physicalOmegaFactorBound slot)
      (physicalOmegaFactor_bound parameters lower L positive lengthPositive widthHalf widthLength slot mode)
      (mapping field mode)
  rw [covariant tau field mode, map_smul]

/-- The original normalized radial derivative coordinate is diagonal under translations. -/
theorem physicalOmegaSlope_covariant :
    FullOutputCovariant lower (physicalOmegaSlope parameters lower L positive lengthPositive widthHalf widthLength) :=
  (((physicalOmegaOperator_postcompose_covariant lower parameters L positive lengthPositive widthHalf widthLength
      (highPhysicalOutput_covariant lower (0 : Fin 3)) 0).sub lower
    (physicalOmegaOperator_postcompose_covariant lower parameters L positive lengthPositive widthHalf widthLength
      (highPhysicalOutput_covariant lower (0 : Fin 3)) 1)).sub lower
    ((physicalOmegaOperator_postcompose_covariant lower parameters L positive lengthPositive widthHalf widthLength
      (highPhysicalOutput_covariant lower (1 : Fin 3)) 2).smul lower Complex.I)).sub lower
    ((physicalOmegaOperator_postcompose_covariant lower parameters L positive lengthPositive widthHalf widthLength
      (highPhysicalOutput_covariant lower (2 : Fin 3)) 3).smul lower Complex.I)

/-- Both coordinates are the SAME original Domega ambient coordinates. -/
theorem physicalOmegaCoordinates_covariant (tau : OrbitParameter) (field : DivisionRow 3 lower)
    (coordinate : Fin 2) (mode : HighAnnularMode) :
    physicalOmegaCoordinates parameters lower L positive lengthPositive widthHalf widthLength
      (orbitLpAction (RadialL2 3 lower) tau field) coordinate mode =
    orbitCharacter tau mode.val •
      physicalOmegaCoordinates parameters lower L positive lengthPositive widthHalf widthLength field coordinate mode := by
  fin_cases coordinate
  · exact highPhysicalOutput_covariant lower (0 : Fin 3) tau field mode
  · exact physicalOmegaSlope_covariant lower parameters L positive lengthPositive widthHalf widthLength tau field mode

end Grad.AnnularCrossOrbit

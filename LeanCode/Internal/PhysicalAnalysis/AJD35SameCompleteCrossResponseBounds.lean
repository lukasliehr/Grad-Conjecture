import AJD34SameCrossEnergyCoordinateBounds
import AJD36UniformClosedGraphAndPair

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2000
set_option synthInstance.maxHeartbeats 200000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularCrossMaps Grad.AnnularKernelOrbit Grad.AnnularCurrentEnergy
open Grad.AnnularCurrentBoundary Grad.AnnularReconstruction Grad.AnnularKernelL2 Grad.AnnularHighInverseOrbit
open Grad.AnnularCurrentGreen Grad.AnnularOmegaGraph
open Grad.AnnularCurrentInverse Grad.AnnularCoupledInverse Grad.GaugeCoefficients.Physical.Allocation

attribute [local instance] crossDataNormed crossDataSeminormed crossDataRealInner crossDataRealNormed crossDataRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace highInverseFamilyRealNormed
  crossHighNormed crossHighSeminormed crossHighComplexNormed crossHighComplexModule
  crossHighRealNormed crossHighRealModule crossResponseRealNormed crossResponseRealModule
  crossBulkOperatorNormed crossBulkOperatorRealNormed crossEnergyOperatorNormed crossEnergyOperatorRealNormed

local instance crossFluxOperatorNormed (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    NormedAddCommGroup (CrossHighData parameters lower →L[ℂ] annularOmegaGraph lower L positive lengthPositive) := inferInstance
local instance crossFluxOperatorRealNormed (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    NormedSpace ℝ (CrossHighData parameters lower →L[ℂ] annularOmegaGraph lower L positive lengthPositive) :=
  NormedSpace.restrictScalars ℝ ℂ (CrossHighData parameters lower →L[ℂ] annularOmegaGraph lower L positive lengthPositive)
local instance crossCompleteOperatorNormed (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    NormedAddCommGroup (CrossHighData parameters lower →L[ℂ] CrossHighSpace lower L positive lengthPositive) := inferInstance

section IsometricComplexComposition
variable {Context : Type*} {X E F : Context → Type*}
  [∀ context, NormedAddCommGroup (X context)] [∀ context, NormedSpace ℂ (X context)]
  [∀ context, NormedAddCommGroup (E context)] [∀ context, NormedSpace ℂ (E context)]
  [∀ context, NormedAddCommGroup (F context)] [∀ context, NormedSpace ℂ (F context)]
  {budget : Context → ℕ → ℝ}

private theorem uniformComplexIsometricPostcompose
    (family : (context : Context) → OrbitParameter → X context →L[ℂ] E context)
    (bound : UniformCoordinateBound budget family) (smooth : ∀ context, ContDiff ℝ ∞ (family context))
    (inclusion : (context : Context) → E context →L[ℂ] F context)
    (isometry : ∀ context value, ‖inclusion context value‖ = ‖value‖) :
    UniformCoordinateBound budget (fun context tau => (inclusion context).comp (family context tau)) := by
  apply bound.postcomposeComplex smooth inclusion 1 (by norm_num)
  intro context
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro value
  exact (isometry context value).le.trans_eq (one_mul _).symm
end IsometricComplexComposition

variable (parameters : PhaseParameters) (L compact : ℝ)

/-- Inclusion into the original W norm costs no additional factor. -/
theorem crossEnergyOrbit_uniformCoordinateBound :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact =>
        crossEnergyOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
          context.widthHalf context.widthLength context.state
          (coupledPrimitive_highSmall parameters L compact context.state context.small)) := by
  have mapped := uniformComplexIsometricPostcompose
    (X := fun context : CoupledCoordinateContext parameters L compact => CrossHighData parameters context.lower)
    (E := fun context : CoupledCoordinateContext parameters L compact => annularInnerZero context.lower L context.positive
      (context.lowerHalf.trans_lt (by norm_num)) context.lengthPositive)
    (F := fun context : CoupledCoordinateContext parameters L compact => annularEnergySpace context.lower L context.positive)
    (fun context => crossZeroEnergyOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small))
    (by
      intro axis order
      let constant : ℝ := (crossZeroEnergyOrbit_uniformCoordinateBound parameters L compact axis order).choose
      refine ⟨constant, (crossZeroEnergyOrbit_uniformCoordinateBound parameters L compact axis order).choose_spec.1, ?_⟩
      intro context base time
      with_unfolding_all
        exact (crossZeroEnergyOrbit_uniformCoordinateBound parameters L compact axis order).choose_spec.2 context base time)
    (fun context => by
      with_unfolding_all
        exact crossZeroEnergyOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
          context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small))
    (fun context => annularZeroInclusion context.lower L context.positive (context.lowerHalf.trans_lt (by norm_num)) context.lengthPositive)
    (fun _ _ => rfl)
  intro axis order
  obtain ⟨constant, nonnegative, estimate⟩ := mapped axis order
  refine ⟨constant, nonnegative, ?_⟩
  intro context base time
  with_unfolding_all exact estimate context base time

/-- The actual three physical outputs retain one high factor through the
SAME elimination operator and cross-energy response. -/
theorem crossPhysicalOutputOrbit_uniformCoordinateBound :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact =>
        crossPhysicalOutputOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
          context.widthHalf context.widthLength context.state
          (coupledPrimitive_highSmall parameters L compact context.state context.small)) := by
  have packet := UniformCoordinateBound.postcomposeComplex
    (X := fun context : CoupledCoordinateContext parameters L compact => CrossHighData parameters context.lower)
    (E := fun context : CoupledCoordinateContext parameters L compact => annularEnergySpace context.lower L context.positive)
    (F := fun context : CoupledCoordinateContext parameters L compact => DivisionRow 8 context.lower)
    (family := fun context : CoupledCoordinateContext parameters L compact => crossEnergyOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small))
    (by
      intro axis order
      let constant : ℝ := (crossEnergyOrbit_uniformCoordinateBound parameters L compact axis order).choose
      refine ⟨constant, (crossEnergyOrbit_uniformCoordinateBound parameters L compact axis order).choose_spec.1, ?_⟩
      intro context base time
      with_unfolding_all
        exact (crossEnergyOrbit_uniformCoordinateBound parameters L compact axis order).choose_spec.2 context base time)
    (fun context => crossEnergyOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small))
    (fun context => highEightEnergyPacket parameters context.lower L context.positive context.lengthPositive context.widthHalf context.widthLength)
    (4 + 2 * |L|) (by positivity)
    (fun context => ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      (highEightEnergyPacket_bound parameters context.lower L context.positive context.lengthPositive context.widthHalf context.widthLength))
  have packetSmooth (context : CoupledCoordinateContext parameters L compact) :
      ContDiff ℝ ∞ (fun tau => (highEightEnergyPacket parameters context.lower L context.positive context.lengthPositive context.widthHalf context.widthLength).comp
        (crossEnergyOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
          context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small) tau)) :=
    complexOperatorComposition_contDiff _ _ contDiff_const
      (crossEnergyOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
        context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small))
  have output := (actualEliminatedOrbit_uniformCoordinateBound parameters L compact).composeComplex
    (X := fun context : CoupledCoordinateContext parameters L compact => CrossHighData parameters context.lower)
    (E := fun context : CoupledCoordinateContext parameters L compact => DivisionRow 8 context.lower)
    (F := fun context : CoupledCoordinateContext parameters L compact => DivisionRow 3 context.lower) packet
    (fun context => actualEliminatedOrbit_contDiff parameters L compact context.lower context.positive
      (context.lowerHalf.trans (by norm_num)) context.state) packetSmooth
    (fun context => context.budget_nonnegative) (fun order => pairBudgetConstant 8 order 1)
    (fun order => pairBudgetConstant_nonnegative 8 order (by norm_num)) (fun context => context.budget_pair)
  exact output.add (crossKnownBulkOrbit_uniformCoordinateBound parameters L compact)
    (fun context => complexOperatorComposition_contDiff _ _
      (actualEliminatedOrbit_contDiff parameters L compact context.lower context.positive
        (context.lowerHalf.trans (by norm_num)) context.state) (packetSmooth context))
    (fun context => crossKnownBulkOrbit_contDiff parameters L compact context.lower context.positive
      (context.lowerHalf.trans (by norm_num)) context.state)

/-- The original Domega norm is controlled through its actual ambient
value/slope coordinates and the fixed orthogonal graph retraction. -/
theorem crossFluxOrbit_uniformCoordinateBound :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact =>
        crossFluxOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
          context.widthHalf context.widthLength context.state
          (coupledPrimitive_highSmall parameters L compact context.state context.small)) := by
  have ambient := UniformCoordinateBound.postcomposeComplex
    (X := fun context : CoupledCoordinateContext parameters L compact => CrossHighData parameters context.lower)
    (E := fun context : CoupledCoordinateContext parameters L compact => DivisionRow 3 context.lower)
    (F := fun context : CoupledCoordinateContext parameters L compact => AnnularOmegaAmbient context.lower)
    (family := fun context : CoupledCoordinateContext parameters L compact => crossPhysicalOutputOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small))
    (by
      intro axis order
      let constant : ℝ := (crossPhysicalOutputOrbit_uniformCoordinateBound parameters L compact axis order).choose
      refine ⟨constant, (crossPhysicalOutputOrbit_uniformCoordinateBound parameters L compact axis order).choose_spec.1, ?_⟩
      intro context base time
      with_unfolding_all
        exact (crossPhysicalOutputOrbit_uniformCoordinateBound parameters L compact axis order).choose_spec.2 context base time)
    (fun context => crossPhysicalOutputOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small))
    (fun context => physicalOmegaCoordinates parameters context.lower L context.positive context.lengthPositive context.widthHalf context.widthLength)
    4 (by norm_num)
    (fun context => ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      (physicalOmegaCoordinates_bound parameters context.lower L context.positive context.lengthPositive context.widthHalf context.widthLength))
  have ambientSmooth (context : CoupledCoordinateContext parameters L compact) :
      ContDiff ℝ ∞ (fun tau => (physicalOmegaCoordinates parameters context.lower L context.positive context.lengthPositive context.widthHalf context.widthLength).comp
        (crossPhysicalOutputOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
          context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small) tau)) :=
    complexOperatorComposition_contDiff _ _ contDiff_const
      (crossPhysicalOutputOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
        context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small))
  have mapped := ambient.postcomposeComplex
    (F := fun context : CoupledCoordinateContext parameters L compact => annularOmegaGraph context.lower L context.positive context.lengthPositive)
    ambientSmooth
    (fun context => (annularOmegaGraph context.lower L context.positive context.lengthPositive).orthogonalProjectionOnto)
    1 (by norm_num)
    (fun context => (annularOmegaGraph context.lower L context.positive context.lengthPositive).orthogonalProjectionOnto_norm_le)
  have same (context : CoupledCoordinateContext parameters L compact) (tau : OrbitParameter) :
      (annularOmegaGraph context.lower L context.positive context.lengthPositive).orthogonalProjectionOnto.comp
        ((physicalOmegaCoordinates parameters context.lower L context.positive context.lengthPositive context.widthHalf context.widthLength).comp
          (crossPhysicalOutputOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
            context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small) tau)) =
      crossFluxOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
        context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small) tau := by
    exact (congrArg (graphOperatorProjection (X := CrossHighData parameters context.lower)
      (annularOmegaGraph context.lower L context.positive context.lengthPositive))
      (crossFluxOrbit_inclusion parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
        context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small) tau).symm).trans
      (graphOperatorProjection_retract _ _)
  intro axis order
  obtain ⟨constant, nonnegative, estimate⟩ := mapped axis order
  refine ⟨constant, nonnegative, ?_⟩
  intro context base time
  have converted := estimate context base time
  simp only [same] at converted
  with_unfolding_all exact converted

/-- Both original W and Domega components of the SAME complete high
cross response satisfy the genuine pure-coordinate one-high tower. -/
theorem actualHighCrossResponseOrbit_uniformCoordinateBound :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact =>
        actualHighCrossResponseOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
          context.widthHalf context.widthLength context.state
          (coupledPrimitive_highSmall parameters L compact context.state context.small)) := by
  have combined := UniformCoordinateBound.pairComplex
    (X := fun context : CoupledCoordinateContext parameters L compact => CrossHighData parameters context.lower)
    (E := fun context : CoupledCoordinateContext parameters L compact => annularEnergySpace context.lower L context.positive)
    (F := fun context : CoupledCoordinateContext parameters L compact => annularOmegaGraph context.lower L context.positive context.lengthPositive)
    (first := fun context : CoupledCoordinateContext parameters L compact => crossEnergyOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small))
    (second := fun context : CoupledCoordinateContext parameters L compact => crossFluxOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small))
    (by
      intro axis order
      let constant : ℝ := (crossEnergyOrbit_uniformCoordinateBound parameters L compact axis order).choose
      refine ⟨constant, (crossEnergyOrbit_uniformCoordinateBound parameters L compact axis order).choose_spec.1, ?_⟩
      intro context base time
      with_unfolding_all
        exact (crossEnergyOrbit_uniformCoordinateBound parameters L compact axis order).choose_spec.2 context base time)
    (by
      intro axis order
      let constant : ℝ := (crossFluxOrbit_uniformCoordinateBound parameters L compact axis order).choose
      refine ⟨constant, (crossFluxOrbit_uniformCoordinateBound parameters L compact axis order).choose_spec.1, ?_⟩
      intro context base time
      with_unfolding_all
        exact (crossFluxOrbit_uniformCoordinateBound parameters L compact axis order).choose_spec.2 context base time)
    (fun context => crossEnergyOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small))
    (fun context => crossFluxOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state (coupledPrimitive_highSmall parameters L compact context.state context.small))
  intro axis order
  obtain ⟨constant, nonnegative, estimate⟩ := combined axis order
  refine ⟨constant, nonnegative, ?_⟩
  intro context base time
  have converted := estimate context base time
  simp only [← actualHighCrossResponseOrbit_pair] at converted
  with_unfolding_all exact converted
end Grad.AnnularCrossOrbit

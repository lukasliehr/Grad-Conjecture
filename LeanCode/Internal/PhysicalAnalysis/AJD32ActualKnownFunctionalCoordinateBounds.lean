import AJD40UniformPhysicalPairingCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2000
set_option synthInstance.maxHeartbeats 200000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularCrossMaps Grad.AnnularKernelOrbit Grad.AnnularCurrentEnergy
open Grad.AnnularCurrentBoundary Grad.AnnularUniformBoundary Grad.AnnularReconstruction Grad.AnnularKernelL2
open Grad.ActualBoundaryPrimitives Grad.AnnularCurrentInverse

attribute [local instance] crossDataNormed crossDataSeminormed crossDataRealInner crossDataRealNormed crossDataRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

local instance crossDataComplexNormed (parameters : PhaseParameters) (lower : ℝ) :
    NormedSpace ℂ (CrossHighData parameters lower) := inferInstance
local instance crossBulkOperatorNormed (parameters : PhaseParameters) (lower : ℝ) (dimension : ℕ) :
    NormedAddCommGroup (CrossHighData parameters lower →L[ℂ] DivisionRow dimension lower) := inferInstance
local instance crossBulkOperatorRealNormed (parameters : PhaseParameters) (lower : ℝ) (dimension : ℕ) :
    NormedSpace ℝ (CrossHighData parameters lower →L[ℂ] DivisionRow dimension lower) := ContinuousLinearMap.toNormedSpace
local instance crossBoundaryOperatorNormed (parameters : PhaseParameters) (lower : ℝ) :
    NormedAddCommGroup (CrossHighData parameters lower →L[ℂ] Grad.BoundaryKernelAction.NegativeTrace parameters 0 0 1) := inferInstance
local instance crossBoundaryOperatorRealNormed (parameters : PhaseParameters) (lower : ℝ) :
    NormedSpace ℝ (CrossHighData parameters lower →L[ℂ] Grad.BoundaryKernelAction.NegativeTrace parameters 0 0 1) := ContinuousLinearMap.toNormedSpace

section IsometricRestriction
variable {Context : Type*} {X W V : Context → Type*}
  [∀ context, NormedAddCommGroup (X context)] [∀ context, NormedSpace ℝ (X context)]
  [∀ context, NormedAddCommGroup (W context)] [∀ context, NormedSpace ℝ (W context)]
  [∀ context, NormedAddCommGroup (V context)] [∀ context, NormedSpace ℝ (V context)]
  {budget : Context → ℕ → ℝ}

private theorem uniformIsometricRestriction
    (family : (context : Context) → OrbitParameter → X context →L[ℝ] W context →L[ℝ] ℝ)
    (bound : UniformCoordinateBound budget family) (smooth : ∀ context, ContDiff ℝ ∞ (family context))
    (inclusion : (context : Context) → V context →L[ℝ] W context)
    (isometry : ∀ context value, ‖inclusion context value‖ = ‖value‖) :
    UniformCoordinateBound budget (fun context tau => operatorTestRestriction (inclusion context) (family context tau)) := by
  apply bound.testRestriction smooth inclusion 1 (by norm_num)
  intro context
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro value
  exact (isometry context value).le.trans_eq (one_mul _).symm
end IsometricRestriction

variable (parameters : PhaseParameters) (L compact : ℝ)

theorem crossKnownBulkOrbit_uniformCoordinateBound :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact =>
        crossKnownBulkOrbit parameters L compact context.lower context.positive
          (context.lowerHalf.trans (by norm_num)) context.state) := by
  have first := (actualEliminatedOrbit_uniformCoordinateBound parameters L compact).precomposeComplex
    (fun context => actualEliminatedOrbit_contDiff parameters L compact context.lower context.positive
      (context.lowerHalf.trans (by norm_num)) context.state)
    (fun context => crossKnownEight parameters context.lower) 1 (by norm_num)
    (fun context => crossKnownEight_norm parameters context.lower)
  have direct := UniformCoordinateBound.const (budget := CoupledCoordinateContext.budget)
    (fun context => context.budget_nonnegative)
    (fun context : CoupledCoordinateContext parameters L compact => crossKnownDirect parameters context.lower)
    2 (by norm_num) (fun context => crossKnownDirect_norm parameters context.lower)
  apply first.add direct
  · intro context
    exact (((ContinuousLinearMap.compL ℂ (CrossHighData parameters context.lower)
      (DivisionRow 8 context.lower) (DivisionRow 3 context.lower)).flip
        (crossKnownEight parameters context.lower)).restrictScalars ℝ).contDiff.comp
      (actualEliminatedOrbit_contDiff parameters L compact context.lower context.positive
        (context.lowerHalf.trans (by norm_num)) context.state)
  · intro context
    exact contDiff_const

theorem crossBoundaryValueOrbit_uniformCoordinateBound :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact => crossBoundaryValueOrbit parameters L compact context.lower context.state) :=
  (actualBoundaryInverseOrbit_uniformCoordinateBound parameters L compact).precomposeComplex
    (fun context => actualBoundaryInverseOrbitJet_contDiff parameters L compact context.state 0 0)
    (fun context => crossBoundaryCoordinate parameters context.lower) 1 (by norm_num)
    (fun context => crossBoundaryCoordinate_norm parameters context.lower)

/-- The exact f/qc/rqv/beta known functional has one high coordinate factor
in the original energy dual, with the actual beta inverse appearing once. -/
theorem crossKnownFunctionalOrbit_uniformCoordinateBound :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact =>
        crossKnownFunctionalOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
          context.widthHalf context.widthLength context.state) := by
  let bulkTest := fun context : CoupledCoordinateContext parameters L compact =>
    (highEnergyTestPacket parameters context.lower L context.positive context.lengthPositive context.widthHalf context.widthLength).restrictScalars ℝ
  let boundaryTest := fun context : CoupledCoordinateContext parameters L compact =>
    (actualCurrentHighOuterTrace parameters context.lower L context.positive context.lowerHalf context.lengthPositive 0 0).restrictScalars ℝ
  have bulk := (crossKnownBulkOrbit_uniformCoordinateBound parameters L compact).pairedComplex
    (V := fun context => annularEnergySpace context.lower L context.positive)
    (fun context => crossKnownBulkOrbit_contDiff parameters L compact context.lower context.positive
      (context.lowerHalf.trans (by norm_num)) context.state)
    bulkTest 5 (by norm_num)
    (fun context => ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      (highEnergyTestPacket_bound parameters context.lower L context.positive context.lengthPositive context.widthHalf context.widthLength))
  have boundary := (crossBoundaryValueOrbit_uniformCoordinateBound parameters L compact).pairedComplex
    (V := fun context => annularEnergySpace context.lower L context.positive)
    (fun context => crossBoundaryValueOrbit_contDiff parameters L compact context.lower context.state)
    boundaryTest
    (uniformOuterTraceConstant L) (uniformOuterTraceConstant_nonnegative L)
    (fun context => ContinuousLinearMap.opNorm_le_bound _ (uniformOuterTraceConstant_nonnegative L)
      (actualCurrentHighOuterTrace_bound parameters context.lower L context.positive context.lowerHalf context.lengthPositive 0 0))
  have bulkSmooth (context : CoupledCoordinateContext parameters L compact) :=
    pairedComplexOperator_contDiff (bulkTest context) _
      (crossKnownBulkOrbit_contDiff parameters L compact context.lower context.positive (context.lowerHalf.trans (by norm_num)) context.state)
  have boundarySmooth (context : CoupledCoordinateContext parameters L compact) :=
    pairedComplexOperator_contDiff (boundaryTest context) _
      (crossBoundaryValueOrbit_contDiff parameters L compact context.lower context.state)
  have combined := bulk.add (boundary.neg boundarySmooth) bulkSmooth (fun context => (boundarySmooth context).neg)
  have same (context : CoupledCoordinateContext parameters L compact) (tau : OrbitParameter) :
      pairedComplexOperator (bulkTest context)
          (crossKnownBulkOrbit parameters L compact context.lower context.positive (context.lowerHalf.trans (by norm_num)) context.state tau) +
        -pairedComplexOperator (boundaryTest context) (crossBoundaryValueOrbit parameters L compact context.lower context.state tau) =
      crossKnownFunctionalOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive context.widthHalf context.widthLength context.state tau := by
    with_unfolding_all
      exact (sub_eq_add_neg
        (pairedComplexOperator (bulkTest context)
          (crossKnownBulkOrbit parameters L compact context.lower context.positive (context.lowerHalf.trans (by norm_num)) context.state tau))
        (pairedComplexOperator (boundaryTest context) (crossBoundaryValueOrbit parameters L compact context.lower context.state tau))).symm
  intro axis order
  obtain ⟨constant, nonnegative, estimate⟩ := combined axis order
  refine ⟨constant, nonnegative, ?_⟩
  intro context base time
  have converted := estimate context base time
  simp only [same] at converted
  with_unfolding_all exact converted

/-- Restriction uses the SAME original zero-inner subspace and costs no
additional radius factor. -/
theorem crossKnownZeroFunctionalOrbit_uniformCoordinateBound :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact =>
        crossKnownZeroFunctionalOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
          context.widthHalf context.widthLength context.state) := by
  exact uniformIsometricRestriction
    (X := fun context : CoupledCoordinateContext parameters L compact => CrossHighData parameters context.lower)
    (W := fun context : CoupledCoordinateContext parameters L compact => annularEnergySpace context.lower L context.positive)
    (V := fun context : CoupledCoordinateContext parameters L compact => annularInnerZero context.lower L context.positive (context.lowerHalf.trans_lt (by norm_num)) context.lengthPositive)
    (fun context => crossKnownFunctionalOrbit parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state)
    (crossKnownFunctionalOrbit_uniformCoordinateBound parameters L compact)
    (fun context => crossKnownFunctionalOrbit_contDiff parameters L compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.widthHalf context.widthLength context.state)
    (fun context => annularZeroRealInclusion context.lower L context.positive
      (context.lowerHalf.trans_lt (by norm_num)) context.lengthPositive)
    (fun _ _ => rfl)

end Grad.AnnularCrossOrbit

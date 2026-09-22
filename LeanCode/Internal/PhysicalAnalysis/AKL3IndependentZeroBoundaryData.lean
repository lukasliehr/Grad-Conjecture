import AKL2SameOriginalUniformRetainedEstimate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.AnnularExhaustionEstimate
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularForwardDatum Grad.AnnularForwardTraces Grad.AnnularStrongOrbit
open Grad.AnnularHighGenerators Grad.AnnularCrossOrbit Grad.AnnularCoupledInverse
open Grad.AnnularCurrentSource Grad.SourceCollarDivision Grad.AnnularSourceGraph
open Grad.AnnularHighTilt Grad.AnnularLowEnergy Grad.SourceCollarFullSource
attribute [local instance] Grad.AnnularStrongOrbit.knownAmbientNormed Grad.AnnularStrongOrbit.knownAmbientSeminormed Grad.AnnularStrongOrbit.knownAmbientRealNormed Grad.AnnularStrongOrbit.knownAmbientRealModule
  Grad.AnnularStrongOrbit.strongCarrierNormed Grad.AnnularStrongOrbit.strongCarrierSeminormed Grad.AnnularStrongOrbit.strongCarrierRealNormed Grad.AnnularStrongOrbit.strongCarrierRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace
  Grad.AnnularCrossOrbit.coupledNormed Grad.AnnularCrossOrbit.coupledSeminormed
  Grad.AnnularCrossOrbit.coupledComplexNormed Grad.AnnularCrossOrbit.coupledComplexModule
  Grad.AnnularCrossOrbit.coupledRealNormed Grad.AnnularCrossOrbit.coupledRealModule
  Grad.AnnularCrossOrbit.coupledOperatorRealNormed Grad.AnnularCrossOrbit.coupledOperatorRealModule



private theorem datumPropertyTransport {E : Type*} (property : E → Prop)
    {first second : E} (same : first = second) (actual : property second) : property first :=
  same.symm ▸ actual

private theorem datumRelationTransport {E : Type*} (relation : E → E → Prop)
    {a b c d : E} (first : a = b) (second : c = d) (actual : relation b d) : relation a c := by
  subst a
  subst c
  exact actual

variable (parameters : PhaseParameters) (lower : ℝ)

/-- Prescribe d=k=0 and the physical outer datum zero independently. The
entire original copied source and full residual tuple is retained. -/
def zeroBoundaryDatum (data : OriginalStrongCarrier parameters lower 0 0) :
    OriginalStrongCarrier parameters lower 0 0 :=
  ⟨WithLp.toLp 2 (data.val.ofLp.1, 0), by
    exact data.property⟩

theorem zeroBoundaryDatum_sources (data : OriginalStrongCarrier parameters lower 0 0) :
    (zeroBoundaryDatum parameters lower data).val.ofLp.1 = data.val.ofLp.1 := rfl

theorem zeroBoundaryDatum_boundary (data : OriginalStrongCarrier parameters lower 0 0) :
    (zeroBoundaryDatum parameters lower data).val.ofLp.2 = 0 := rfl

theorem zeroBoundaryDatum_idempotent (data : OriginalStrongCarrier parameters lower 0 0) :
    zeroBoundaryDatum parameters lower (zeroBoundaryDatum parameters lower data) =
      zeroBoundaryDatum parameters lower data := rfl

variable (length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < length)

theorem zeroBoundaryDatum_weighted_boundary (data : OriginalStrongCarrier parameters lower 0 0) :
    let weighted := originalWeightedDatum parameters lower length positive bounded lengthPositive
      (zeroBoundaryDatum parameters lower data)
    weighted.val.ofLp.1.ofLp.2.ofLp.2.ofLp.1 = 0 ∧
      weighted.val.ofLp.1.ofLp.2.ofLp.2.ofLp.2 = 0 ∧ weighted.val.ofLp.2 = 0 := by
  apply datumPropertyTransport
    (fun weighted : StrongDataCarrier parameters lower positive bounded 0 0 =>
      weighted.val.ofLp.1.ofLp.2.ofLp.2.ofLp.1 = 0 ∧
        weighted.val.ofLp.1.ofLp.2.ofLp.2.ofLp.2 = 0 ∧ weighted.val.ofLp.2 = 0)
    (originalWeightedDatum_explicit parameters lower length positive bounded lengthPositive
      (zeroBoundaryDatum parameters lower data))
  refine ⟨rfl, ?_, ?_⟩
  · change lower ^ (-9 / 4 : ℝ) • (0 : Grad.AnnularVariational.AnnularBoundary) = 0
    exact smul_zero _
  · change originalLowIncomingWeightMap parameters lower length positive bounded lengthPositive 0 = 0
    exact map_zero _

/-- All six weighted bulk entries and both original source graphs survive
the independent homogeneous boundary prescription exactly. -/
theorem zeroBoundaryDatum_weighted_sources (data : OriginalStrongCarrier parameters lower 0 0) :
    let original := originalWeightedDatum parameters lower length positive bounded lengthPositive data
    let weighted := originalWeightedDatum parameters lower length positive bounded lengthPositive
      (zeroBoundaryDatum parameters lower data)
    weighted.val.ofLp.1.ofLp.1 = original.val.ofLp.1.ofLp.1 ∧
      weighted.val.ofLp.1.ofLp.2.ofLp.1 = original.val.ofLp.1.ofLp.2.ofLp.1 := by
  exact datumRelationTransport
    (fun weighted original : StrongDataCarrier parameters lower positive bounded 0 0 =>
      weighted.val.ofLp.1.ofLp.1 = original.val.ofLp.1.ofLp.1 ∧
        weighted.val.ofLp.1.ofLp.2.ofLp.1 = original.val.ofLp.1.ofLp.2.ofLp.1)
    (originalWeightedDatum_explicit parameters lower length positive bounded lengthPositive
      (zeroBoundaryDatum parameters lower data))
    (originalWeightedDatum_explicit parameters lower length positive bounded lengthPositive data)
    ⟨rfl,rfl⟩

variable (compact : ℝ)

/-- The actual physical outer trace includes its original copied-source
argument. Setting its prescribed datum to zero leaves that argument intact. -/
theorem zeroBoundaryDatum_response_traces
    (context : CoupledCoordinateContext parameters length compact)
    (data : OriginalStrongCarrier parameters context.lower 0 0) :
    originalBoundaryTrace parameters length compact context.lower context.positive context.lowerHalf
      context.lengthPositive context.state
      (originalSharedResponse parameters length compact context.lower context.positive context.lowerHalf
        context.lengthPositive context.widthHalf context.widthLength context.state context.small
        (zeroBoundaryDatum parameters context.lower data), data.val.ofLp.1.ofLp.1) = 0 :=
  originalBoundaryTrace_response parameters length compact context.lower context.positive context.lowerHalf
    context.lengthPositive context.state context.widthHalf context.widthLength context.small
    (zeroBoundaryDatum parameters context.lower data)

theorem zeroBoundaryDatum_response_five_sources
    (context : CoupledCoordinateContext parameters length compact)
    (data : OriginalStrongCarrier parameters context.lower 0 0) :
    (originalSolvedFiveBlock parameters length compact context.lower context.positive context.lowerHalf
      context.lengthPositive context.state context.widthHalf context.widthLength context.small
      (zeroBoundaryDatum parameters context.lower data)).ofLp.2 = data.val.ofLp.1 := rfl

end Grad.AnnularExhaustionEstimate

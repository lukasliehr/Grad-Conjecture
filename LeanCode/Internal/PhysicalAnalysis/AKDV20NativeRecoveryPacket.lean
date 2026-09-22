import AKDV1ActualProductRecoverySmallness

noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 900000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.OriginalMainConsumer
open Grad.ActualPuncturedFamily Grad.Constraints Grad.Q24Realization Grad.AxisSplit Grad.ChartAxisLift Grad.ConstrainedTransfer Grad.NonlinearQuotientBounds
open Grad.CartesianState Grad.AnnularFullGraph Grad.AnnularForwardDatum Grad.AnnularStrongOrbit
open Grad.AnnularForwardTraces Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularRestriction
open Grad.AnnularExhaustionEstimate Grad.AnnularWeakExhaustion Grad.AnnularFullSource
open Grad.AnnularHighGenerators Grad.AnnularCrossOrbit Grad.ActualAnnularExhaustion
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.SourceCollarFullSource Grad.ExhaustionSourceAllocation
open Grad.GaugeCoefficients.Physical.Allocation
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  traceCoupledRealNormed traceCoupledRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule
  sourceRadialRealInner sourceGraphRealInner sourceKnownGraphRealInner
  weakRetainedRealInner weakSourcesRealInner weakFiveRealInner

attribute [local instance] weakWeightedRetainedRealInner
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




open Grad.ActualScaledNativeCoefficients Grad.ActualCartesianDescent Grad.OriginalCartesianTameEstimate
open Grad.ActualCartesianWeakEquations Grad.ActualScalarWeakEquations Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.SourceBoundaryTrace Grad.ActualCartesianFlux Grad.ActualNativeCellMoments
open Grad.SourceCollarCoefficients Grad.CartesianStartup Grad.ActualSmoothPhysicalField Grad.ActualPuncturedReconstruction
open Grad.NonlinearProduct


open Grad.RealFixedRanges Grad.PhysicalCoordinates Grad.NashMoser.OriginalIteration
open Grad.NashMoser.OriginalLimit Grad.OriginalInverseNeighborhood Grad.FinitePhysicalJetLift


variable (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
  (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
  (nativeState : RetainedInverseState parameters length compact)
  (nativeSmall : physicalBudget parameters nativeState.val.val.field nativeState.val.val.rho nativeState.val.val.epsilon 8 ≤
    originalExhaustionPrimitiveRadius parameters length compact)
  (residual : SmoothQuotient parameters) (residualFlat : IsFlat residual)
  (fullSource : SmoothQuotient parameters) (nativeConstant cellConstant : ℕ → ℝ) (baseConstant : ℝ) (residualNativeConstant : ℕ → ℝ)

/-- One SAME native family and the original covariant/U/Xi/S witnesses.
The subtype retains both the original residual estimate and its full-source payment
for one actual solve, without generating a large dependent recursor. -/
def NativeRecoveryPacket :=
  { family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength
      nativeState nativeSmall residual residualFlat //
    (∀ index grade, family.nativeNorm index grade ≤
      residualNativeConstant grade *
        (‖quotientEta parameters (grade+8) residual‖+
          physicalBudget parameters nativeState.val.val.field nativeState.val.val.rho nativeState.val.val.epsilon (grade+14)*‖quotientEta parameters 8 residual‖)) ∧
    (∀ index grade, family.nativeNorm index grade ≤
    nativeConstant grade *
      (‖quotientEta parameters (grade+20) fullSource‖+
        physicalBudget parameters nativeState.val.val.field nativeState.val.val.rho nativeState.val.val.epsilon (grade+20)*‖quotientEta parameters 20 fullSource‖)) ∧
    (∀ index, family.nativeNorm index 0 ≤
    baseConstant*‖quotientEta parameters 20 fullSource‖) ∧
    ∃ covariant vector : ACore parameters 3, ∃ xi scalar : ACore parameters 1,
    (∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ cell : ℤ,
    (covariant.val cell).value point=actualCartesianCovariantCell parameters length compact
      lengthPositive widthHalf widthLength nativeState nativeSmall residual residualFlat family.limit
      (fun index => (family.equations index).1) (fun index => (family.equations index).2.1)
      (fun index grade => ⟨family.graded index grade,family.inserted index grade⟩) cell point.val) ∧
    (∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
    (originalPhysicalClosedJet parameters covariant).value (point,(axial : CellCircle))=
      actualCartesianCovariantFamilyField parameters length compact lengthPositive widthHalf widthLength
        nativeState nativeSmall residual residualFlat family.limit (fun index => (family.equations index).1)
        (fun index => (family.equations index).2.1)
        (fun index grade => ⟨family.graded index grade,family.inserted index grade⟩) (point.val,axial)) ∧
    (∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
    (originalPhysicalClosedJet parameters xi).value (point,(axial : CellCircle))=
      actualCartesianXiFamilyField parameters length compact lengthPositive widthHalf widthLength
        nativeState nativeSmall residual residualFlat family.limit (fun index => (family.equations index).1)
        (fun index => (family.equations index).2.1)
        (fun index grade => ⟨family.graded index grade,family.inserted index grade⟩) (point.val,axial)) ∧
    (∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
    (originalPhysicalClosedJet parameters scalar).value (point,(axial : CellCircle))=
      actualNativeScalarField parameters length compact lengthPositive widthHalf widthLength
        nativeState nativeSmall residual residualFlat family.limit (fun index => (family.equations index).1)
        (fun index => (family.equations index).2.1)
        (fun index grade => ⟨family.graded index grade,family.inserted index grade⟩) (point.val,axial)) ∧
    (∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
    (originalPhysicalClosedJet parameters vector).value (point,(axial : CellCircle))=
      actualCartesianVectorField parameters length compact lengthPositive widthHalf widthLength
        nativeState nativeSmall residual residualFlat family.limit (fun index => (family.equations index).1)
        (fun index => (family.equations index).2.1)
        (fun index grade => ⟨family.graded index grade,family.inserted index grade⟩) (point.val,axial)) ∧
    (∀ grade, originalGradeNorm grade vector+originalGradeNorm grade scalar ≤
    actualOriginalUSNormConstant parameters length grade *
      (originalGradeNorm grade covariant+originalGradeNorm grade (cartesianSourceVector residual)+
        (1+physicalBudget parameters nativeState.val.val.field nativeState.val.val.rho nativeState.val.val.epsilon (5+grade))*originalGradeNorm 0 covariant)) ∧
    (∀ grade, originalCellNorm parameters grade covariant ≤
    cellConstant grade *
      (‖quotientEta parameters (grade+20) fullSource‖+
        physicalBudget parameters nativeState.val.val.field nativeState.val.val.rho nativeState.val.val.epsilon (grade+20)*‖quotientEta parameters 20 fullSource‖)) }

namespace NativeRecoveryPacket
variable {parameters length compact lengthPositive widthHalf widthLength nativeState nativeSmall residual residualFlat
  fullSource nativeConstant cellConstant baseConstant residualNativeConstant}
  (packet : NativeRecoveryPacket parameters length compact lengthPositive widthHalf widthLength
    nativeState nativeSmall residual residualFlat fullSource nativeConstant cellConstant baseConstant residualNativeConstant)

def family := packet.val
/-- The sharper estimate is retained for this exact family, with its original residual. -/
theorem residualNativeBound :
    ∀ index grade, packet.family.nativeNorm index grade ≤
      residualNativeConstant grade *
        (‖quotientEta parameters (grade+8) residual‖+
          physicalBudget parameters nativeState.val.val.field nativeState.val.val.rho nativeState.val.val.epsilon (grade+14)*‖quotientEta parameters 8 residual‖) := packet.property.1
theorem nativeBound :
    ∀ index grade, packet.family.nativeNorm index grade ≤
    nativeConstant grade *
      (‖quotientEta parameters (grade+20) fullSource‖+
        physicalBudget parameters nativeState.val.val.field nativeState.val.val.rho nativeState.val.val.epsilon (grade+20)*‖quotientEta parameters 20 fullSource‖) := packet.property.2.1
theorem nativeBase :
    ∀ index, packet.family.nativeNorm index 0 ≤
    baseConstant*‖quotientEta parameters 20 fullSource‖ := packet.property.2.2.1
def covariant := packet.property.2.2.2.choose
def vector := packet.property.2.2.2.choose_spec.choose
def xi := packet.property.2.2.2.choose_spec.choose_spec.choose
def scalar := packet.property.2.2.2.choose_spec.choose_spec.choose_spec.choose
theorem covariantCells :
    ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ cell : ℤ,
    (packet.covariant.val cell).value point=actualCartesianCovariantCell parameters length compact
      lengthPositive widthHalf widthLength nativeState nativeSmall residual residualFlat packet.family.limit
      (fun index => (packet.family.equations index).1) (fun index => (packet.family.equations index).2.1)
      (fun index grade => ⟨packet.family.graded index grade,packet.family.inserted index grade⟩) cell point.val := packet.property.2.2.2.choose_spec.choose_spec.choose_spec.choose_spec.1
theorem covariantSame :
    ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
    (originalPhysicalClosedJet parameters packet.covariant).value (point,(axial : CellCircle))=
      actualCartesianCovariantFamilyField parameters length compact lengthPositive widthHalf widthLength
        nativeState nativeSmall residual residualFlat packet.family.limit (fun index => (packet.family.equations index).1)
        (fun index => (packet.family.equations index).2.1)
        (fun index grade => ⟨packet.family.graded index grade,packet.family.inserted index grade⟩) (point.val,axial) := packet.property.2.2.2.choose_spec.choose_spec.choose_spec.choose_spec.2.1
theorem xiSame :
    ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
    (originalPhysicalClosedJet parameters packet.xi).value (point,(axial : CellCircle))=
      actualCartesianXiFamilyField parameters length compact lengthPositive widthHalf widthLength
        nativeState nativeSmall residual residualFlat packet.family.limit (fun index => (packet.family.equations index).1)
        (fun index => (packet.family.equations index).2.1)
        (fun index grade => ⟨packet.family.graded index grade,packet.family.inserted index grade⟩) (point.val,axial) := packet.property.2.2.2.choose_spec.choose_spec.choose_spec.choose_spec.2.2.1
theorem scalarSame :
    ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
    (originalPhysicalClosedJet parameters packet.scalar).value (point,(axial : CellCircle))=
      actualNativeScalarField parameters length compact lengthPositive widthHalf widthLength
        nativeState nativeSmall residual residualFlat packet.family.limit (fun index => (packet.family.equations index).1)
        (fun index => (packet.family.equations index).2.1)
        (fun index grade => ⟨packet.family.graded index grade,packet.family.inserted index grade⟩) (point.val,axial) := packet.property.2.2.2.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.1
theorem vectorSame :
    ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
    (originalPhysicalClosedJet parameters packet.vector).value (point,(axial : CellCircle))=
      actualCartesianVectorField parameters length compact lengthPositive widthHalf widthLength
        nativeState nativeSmall residual residualFlat packet.family.limit (fun index => (packet.family.equations index).1)
        (fun index => (packet.family.equations index).2.1)
        (fun index grade => ⟨packet.family.graded index grade,packet.family.inserted index grade⟩) (point.val,axial) := packet.property.2.2.2.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.2.1
theorem recovery :
    ∀ grade, originalGradeNorm grade packet.vector+originalGradeNorm grade packet.scalar ≤
    actualOriginalUSNormConstant parameters length grade *
      (originalGradeNorm grade packet.covariant+originalGradeNorm grade (cartesianSourceVector residual)+
        (1+physicalBudget parameters nativeState.val.val.field nativeState.val.val.rho nativeState.val.val.epsilon (5+grade))*originalGradeNorm 0 packet.covariant) := packet.property.2.2.2.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.2.2.1
theorem cellBound :
    ∀ grade, originalCellNorm parameters grade packet.covariant ≤
    cellConstant grade *
      (‖quotientEta parameters (grade+20) fullSource‖+
        physicalBudget parameters nativeState.val.val.field nativeState.val.val.rho nativeState.val.val.epsilon (grade+20)*‖quotientEta parameters 20 fullSource‖) := packet.property.2.2.2.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.2.2.2

end NativeRecoveryPacket
end Grad.OriginalMainConsumer

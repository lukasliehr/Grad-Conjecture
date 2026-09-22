import AKEG5ActualPhysicalUnitNativeRows
import AKEF3ActualPacketCompactData
import AKEF4UnitKnownRowFidelity
import AKEF5ActualUnitCoreField
import AKEH1OriginalSourceNormPacket
import AKEG4NativeFourOperatorRealization
import AKDW5ActualOriginalUnitCurrentRecovery
import AKDW7OriginalUnitNativeSpatialEquation
import AKBT25ActualOriginalNativeH1

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option maxRecDepth 3000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace Grad.ActualScaledNativeCoefficients
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





open Grad.AnnularKernelContinuity
open Grad.AnnularPhysicalReconstruction Grad.AnnularKernelL2 Grad.SourceCollarDivision


open Grad.ActualPuncturedReconstruction Grad.AnnularCurrentEnergy

open Grad.ActualPuncturedFamily Grad.ActualPhysicalField

variable (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      originalExhaustionPrimitiveRadius parameters length compact)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (fields : ∀ index, OriginalFiveBlockAmbient parameters (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index))


variable
    (member : ∀ index, fields index ∈ OriginalObservedEquationGraph parameters length compact
      (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index)
      (originalExhaustionRadius_half length lengthPositive index) lengthPositive widthHalf widthLength state)
    (sameSources : ∀ index, (fields index).ofLp.2 =
      (cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0).val.ofLp.1)
    (allGrades : ∀ index grade : ℕ, ∃ weighted : CoupledSpace (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index) lengthPositive,
      CoupledInsertedGrade (originalExhaustionRadius length index) length
        (originalExhaustionRadius_positive length lengthPositive index) lengthPositive grade
        (originalWeightedRetainedObservation parameters (originalExhaustionRadius length index) length
          (originalExhaustionRadius_positive length lengthPositive index)
          ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index)) weighted)


open Grad.ActualCartesianFlux
open Grad.ActualCartesianDescent Grad.ClosedJets Grad.DiskExtension.Operator Grad.BoundaryTrace Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.AnnularGeneralSourceRegularity Grad.ActualSmoothPhysicalField Grad.PuncturedRetainedEnergy
variable (compatible : ∀ first second (included : originalExhaustionRadius length first ≤ originalExhaustionRadius length second),
      originalFiveBlockRestriction parameters (originalExhaustionRadius length first) (originalExhaustionRadius length second) length
        (originalExhaustionRadius_positive length lengthPositive first) (originalExhaustionRadius_positive length lengthPositive second)
        ((originalExhaustionRadius_half length lengthPositive second).trans_lt (by norm_num)) lengthPositive included (fields first) = fields second)

open Grad.PhysicalFamily Grad.PDEBootstrap Grad.Constraints
open Grad.ActualScalarWeakEquations Grad.ActualForceMoments Grad.ActualCartesianEquations Grad.Constraints.Gauges

open Grad.ActualCurrentPrimitives

include compatible

variable (M : ℝ) (Mnonnegative : 0 ≤ M)
    (stateBound : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 14 ≤ M)
    (vanishing : SourceHigherVanishing source)
    (nativeBound : ∀ index, originalWeightedRetainedNorm parameters (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index)
      ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index).ofLp.1 ≤
        2 * independentCoupledDataConstant parameters length compact *
          (originalSourceAllocationConstant parameters length 0 * (1 + M) * ‖quotientEta parameters 8 source‖))

open Grad.PhysicalAxisEquation
include Mnonnegative stateBound vanishing nativeBound

open Grad.CartesianStartup Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ActualNativeCellMoments Grad.ActualOriginalSourceMoments
variable (graded : ∀ index (_grade : ℕ), CoupledSpace (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index) lengthPositive)
    (sameGrade : ∀ index grade, CoupledInsertedGrade (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index) lengthPositive grade
      (originalWeightedRetainedObservation parameters (originalExhaustionRadius length index) length
        (originalExhaustionRadius_positive length lengthPositive index)
        ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index)) (graded index grade))
    (constants : ℕ → ℝ) (estimate : ∀ index grade, ‖graded index grade‖ ≤ constants grade)
include sameGrade estimate



open Grad.SpatialDilation


open Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets Grad.ActualOriginalSourceFirst Grad.AnalyticWeights.Calculus
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Ledger
open Grad.OriginalCoreRealization

open Grad.OriginalMainConsumer Grad.WeightedJets.ZeroExtension Grad.ActualCartesianWeakEquations Grad.ActualPuncturedReconstruction

/-- The SAME actual native solution supplies the complete compact PDE data
on original unit coordinates, retaining the physical length in every coefficient and flux. -/
theorem actualOriginalUnit_compactData {radius : ℝ}
    (radiusNonnegative : 0≤radius) (coefficient : OriginalUnitRankState parameters length radius)
    (sameData : coefficient.val=(state.val.val.rho,state.val.val.alpha,state.val.val.delta,
      state.val.val.parameter,state.val.val.epsilon,state.val.val.field))
    (covariant circle : ACore parameters 3)
    (covariantSame : ∀ (point : ClosedDisk),0<‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters covariant).value (point,(axial : CellCircle))=
        actualCartesianCovariantFamilyField parameters length compact lengthPositive widthHalf widthLength state small
          source flat fields member sameSources allGrades (point.val,axial))
    (circleSame : originalSourceFieldLinear parameters circle=originalCircleKernel (originalSourceFieldLinear parameters covariant))
    (cutoff : Spatial → ℝ) (cutSmooth : ContDiff ℝ ∞ cutoff) (cutCompact : HasCompactSupport cutoff) (order : ℕ) :
    let packet := originalSourceNormPacket coefficient circle source;
    ∃ data : StartupCompactSpatialEquation order (tsupport cutoff),
      base 3 order openUnitDisk (fun _ => 0) data.field=startupCutoffL2 cutoff cutSmooth cutCompact packet.field.field ∧
      (∀ outer inner,base 3 order openUnitDisk (fun _ => 0) (data.tensor outer inner)=
        startupCutoffL2 cutoff cutSmooth cutCompact (packet.tensorFamily radiusNonnegative outer inner).field) ∧
      base 3 order openUnitDisk (fun _ => 0) data.zeroth=
        startupCutoffEquationZeroth cutoff cutSmooth cutCompact packet.field.field
          (startupSignedPhaseZeroth parameters one_ne_zero startupOriginalUnitScale packet.field
            (packet.tensorFamily radiusNonnegative) (packet.fluxFamily radiusNonnegative length⁻¹) 0)
          (fun outer inner => (packet.tensorFamily radiusNonnegative outer inner).field)
          (startupSignedPhaseFlux parameters one_ne_zero startupOriginalUnitScale packet.field
            (packet.tensorFamily radiusNonnegative) (packet.fluxFamily radiusNonnegative length⁻¹) 0) ∧
      ∀ direction,base 3 order openUnitDisk (fun _ => 0) (data.flux direction)=
        startupCutoffEquationFlux cutoff cutSmooth cutCompact packet.field.field
          (fun outer inner => (packet.tensorFamily radiusNonnegative outer inner).field)
          (startupSignedPhaseFlux parameters one_ne_zero startupOriginalUnitScale packet.field
            (packet.tensorFamily radiusNonnegative) (packet.fluxFamily radiusNonnegative length⁻¹) 0) direction := by
  let packet := originalSourceNormPacket coefficient circle source
  let result := actualOriginalUnit_nativeRows parameters length compact lengthPositive widthHalf widthLength state small source flat
    fields member sameSources allGrades compatible M Mnonnegative stateBound vanishing nativeBound graded sameGrade constants estimate
    radiusNonnegative coefficient sameData
  let weighted := result.choose
  let forceCertificate := result.choose_spec
  let weightedForce := forceCertificate.choose
  let cofactorCertificate := forceCertificate.choose_spec
  let weightedCofactor := cofactorCertificate.choose
  have facts := cofactorCertificate.choose_spec
  have covariantRep := facts.1
  let rowCertificate := facts.2
  let rawRows := rowCertificate.choose
  let psiCertificate := rowCertificate.choose_spec
  let psi := psiCertificate.choose
  have rowFacts := psiCertificate.choose_spec
  let rows := nativeERRows weighted weightedForce weightedCofactor
    ((originalSourceMoments parameters (cartesianSourceVector source)).dilate startupOriginalUnitScale)
    (((originalSourceMoments parameters (source 3)).dilate startupOriginalUnitScale).smul (length : ℂ)⁻¹)
    (((originalSourceMoments parameters (source 2)).dilate startupOriginalUnitScale).smul ((1 : ℂ)/(length : ℂ)))
  have coreSame := actualOriginalUnit_covariantCore_field parameters length compact lengthPositive widthHalf widthLength state small
    source flat fields member sameSources allGrades covariant covariantSame weighted covariantRep
  have fieldBase : packet.field.field=rows.circle.field := by
    change originalSourceFieldLinear parameters circle=originalCircleKernel weighted.field
    rw [circleSame]
    exact congrArg originalCircleKernel coreSame
  have known := startupOriginalUnitRows_knownBases parameters length source weighted weightedForce weightedCofactor
  have forceBase : packet.knownForce.field=rows.knownForce.field := known.1
  have thirdBase : packet.knownThird.field=rows.knownThird.field := known.2.1
  have detBase : packet.determinant.field=rows.determinant.field := known.2.2
  have weak : StartupNativeWeakRows length⁻¹ psi rawRows := by
    rw [← one_div length]
    exact rowFacts.2.1
  exact StartupOriginalUnitNormPacket.explicitCompactData parameters length radius radiusNonnegative packet length⁻¹
    rows rawRows psi rowFacts.1 weak fieldBase forceBase thirdBase detBase rowFacts.2.2.1 rowFacts.2.2.2.1
    rowFacts.2.2.2.2.1 rowFacts.2.2.2.2.2
    (originalSourceNormPacket_field_allSpatial coefficient circle source)
    (originalSourceNormPacket_force_allSpatial coefficient circle source)
    (originalSourceNormPacket_third_allSpatial coefficient circle source)
    (originalSourceNormPacket_determinant_allSpatial coefficient circle source) cutoff cutSmooth cutCompact order

end Grad.ActualScaledNativeCoefficients

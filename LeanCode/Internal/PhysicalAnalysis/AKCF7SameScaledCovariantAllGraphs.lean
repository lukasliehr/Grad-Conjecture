import AKCF6ActualNativePuncturedGraphs
import AKAY11ActualCutoffWeakProducts

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace Grad.NativePuncturedGraph
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


open Grad.ActualCartesianDescent Grad.ClosedJets Grad.DiskExtension.Operator Grad.BoundaryTrace Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.PuncturedRetainedEnergy
variable (compatible : ∀ first second (included : originalExhaustionRadius length first ≤ originalExhaustionRadius length second),
      originalFiveBlockRestriction parameters (originalExhaustionRadius length first) (originalExhaustionRadius length second) length
        (originalExhaustionRadius_positive length lengthPositive first) (originalExhaustionRadius_positive length lengthPositive second)
        ((originalExhaustionRadius_half length lengthPositive second).trans_lt (by norm_num)) lengthPositive included (fields first) = fields second)


open Grad.ActualCartesianFlux Grad.ActualNativeCellMoments Grad.CartesianStartup Grad.WeightedJets
open Grad.PDEBootstrap Grad.GenericCarriers Grad.SourceCollarFullSource


variable (data : OriginalNativeMoments parameters
    (actualCartesianCovariantCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades)
    (actualCartesianXiOverRadiusCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades))
    (scale : Grad.SpatialDilation.Scale)
    (cutoff : SpatialPlane→ℝ) (compactSupport : HasCompactSupport cutoff)
    (punctured : tsupport cutoff⊆{point | 0<‖scale.val • point‖ ∧ ‖scale.val • point‖<1})
    (cutoffSmooth : ContDiff ℝ ∞ cutoff)

include compatible in
/-- Exact base identification with the existing BF scaledCovariant carrier,
before fixed Q0: this is the SAME field used by differentiated startup. -/
theorem actualCovariantCutoffGraph_base (order weight : ℕ) :
    base 3 order openUnitDisk (fun _ => weight)
      (actualCovariantCutoffGraph parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades
        scale.val cutoff compactSupport punctured cutoffSmooth order weight)=
      startupCutoffL2 cutoff cutoffSmooth compactSupport (data.scaledCovariant scale).field := by
  apply Lp.ext
  filter_upwards [actualCovariantCutoffGraph_same parameters length compact lengthPositive widthHalf widthLength state small source flat
    fields member sameSources allGrades compatible scale.val cutoff compactSupport punctured cutoffSmooth order weight,
    data.scaledCovariant_same scale,startupCutoffL2_ae cutoff cutoffSmooth compactSupport (data.scaledCovariant scale).field]
    with point graph native localized
  apply lp.ext
  funext cell
  rw [graph cell,localized cell,native cell,Complex.coe_smul]
  congr 1
  exact congrArg (fun value : ℝ => value • actualCartesianCovariantCell parameters length compact lengthPositive widthHalf widthLength state small
    source flat fields member sameSources allGrades cell (scale.val • point))
    (startupPhysicalWeight_dilation parameters.sigma0 parameters.gamma scale.val scale.property.1.le cell point).symm

include compatible punctured in
/-- Public all-order annular reserve for the literal native covariant, for
any real smooth compact cutoff (including all nonradial cutoff derivatives). -/
theorem actualScaledCovariant_punctured_allGraphs :
    ∃ graphs : ∀ order weight : ℕ, GraphGrade 3 order weight openUnitDisk,
      ∀ order weight, base 3 order openUnitDisk (fun _ => weight) (graphs order weight)=
        startupCutoffL2 cutoff cutoffSmooth compactSupport (data.scaledCovariant scale).field :=
  ⟨actualCovariantCutoffGraph parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades
      scale.val cutoff compactSupport punctured cutoffSmooth,
    actualCovariantCutoffGraph_base parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades
      compatible data scale cutoff compactSupport punctured cutoffSmooth⟩

end Grad.NativePuncturedGraph

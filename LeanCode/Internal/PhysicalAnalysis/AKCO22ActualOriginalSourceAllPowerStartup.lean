import AKCO21ActualB10AllPowerStartup
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 3000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped Topology ContDiff
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

open Grad.ActualPuncturedFamily Grad.ActualPhysicalField Grad.ActualSmoothPhysicalField

open Grad.ActualCartesianDescent Grad.ClosedJets Grad.DiskExtension.Operator Grad.BoundaryTrace Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients

open Grad.CartesianStartup Grad.GaugeCoefficients.Physical.RadialLedger Grad.Constraints.Gauges
open Grad.ActualOriginalSourceMoments Grad.ActualScalarWeakEquations Grad.ActualCurrentPrimitives
open Grad.PhysicalFamily Grad.PDEBootstrap Grad.ActualForceMoments


open Grad.SpatialDilation
open Grad.AnalyticWeights.Calculus
/-- Genuine original source consumer of all-power startup. The compatible
family, all natural native moments, exact weak ER identities, all signed
source first graphs and punctured complement graphs are actually supplied.
Every signed axial power of the SAME weighted Q0(a_C) has a global first graph. -/
theorem actualCartesianSource_allSignedPowers_first
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
    (M : ℝ) (Mnonnegative : 0 ≤ M)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      originalExhaustionPrimitiveRadius parameters length compact)
    (stateBound : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 14 ≤ M)
    (source : SmoothQuotient parameters) (flat : IsFlat source) (vanishing : SourceHigherVanishing source)
    (outer inside : Spatial → ℝ) (outerSmooth : ContDiff ℝ ∞ outer) (insideSmooth : ContDiff ℝ ∞ inside)
    (outerCompact : HasCompactSupport outer) (insideCompact : HasCompactSupport inside)
    (outerDisk : tsupport outer ⊆ openUnitDisk) (insideDisk : tsupport inside ⊆ openUnitDisk)
    (plateau : Set.EqOn outer (fun _ => 1) (tsupport inside))
    (radial : ∀ first second : Spatial, ‖first‖ = ‖second‖ → inside first = inside second)
    (low : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 <
      actualNativeStartupRadius parameters length compact lengthPositive state.val.val.compactNonnegative
        outer outerSmooth outerCompact outerDisk)
    (annular : Spatial → ℝ) (annularSmooth : ContDiff ℝ ∞ annular) (annularCompact : HasCompactSupport annular)
    (annularRadial : ∀ first second : Spatial, ‖first‖ = ‖second‖ → annular first = annular second)
    (annularPartition : ∀ point ∈ openUnitDisk, annular point = 1-inside point)
    (annularPunctured : tsupport annular ⊆ {point | 0 < ‖(originalStartupScale length lengthPositive).val • point‖ ∧
      ‖(originalStartupScale length lengthPositive).val • point‖ < 1}) :
    ∃ (fields : ∀ index, OriginalFiveBlockAmbient parameters (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index)),
    ∃ (member : ∀ index, fields index ∈ OriginalObservedEquationGraph parameters length compact
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
          ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index)) weighted),
      (∀ index, originalWeightedRetainedNorm parameters (originalExhaustionRadius length index) length
        (originalExhaustionRadius_positive length lengthPositive index)
        ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index).ofLp.1 ≤
          2 * independentCoupledDataConstant parameters length compact *
            (originalSourceAllocationConstant parameters length 0 * (1+M) * ‖quotientEta parameters 8 source‖)) ∧
      ( ∀ first second (included : originalExhaustionRadius length first ≤ originalExhaustionRadius length second),
      originalFiveBlockRestriction parameters (originalExhaustionRadius length first) (originalExhaustionRadius length second) length
        (originalExhaustionRadius_positive length lengthPositive first) (originalExhaustionRadius_positive length lengthPositive second)
        ((originalExhaustionRadius_half length lengthPositive second).trans_lt (by norm_num)) lengthPositive included (fields first) = fields second) ∧
      (∃ weighted : StartupAllMoments 3,
        (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
          weighted.field point cell = physicalWeight parameters.sigma0 parameters.gamma (originalStartupScale length lengthPositive).val cell point •
            actualCartesianCovariantCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell
              ((originalStartupScale length lengthPositive).val • point)) ∧
        ∀ power : ℕ, ∃ graph : StartupFirst 3, Grad.WeightedJets.base 3 1 openUnitDisk (fun _ => 0) graph =
          ((StartupSignedFamily.ofNatural weighted length (originalStartupScale length lengthPositive).val).circle).moment power) := by
  have certificate := actualCartesianSource_compatibleSolution parameters length compact lengthPositive M Mnonnegative
  obtain ⟨fields,graded,laws⟩ := certificate.choose_spec.2 widthHalf widthLength state small stateBound source flat vanishing
  let member := fun index => (laws.1 index).1
  let sameSources := fun index => (laws.1 index).2.1
  let allGrades := fun index grade => Exists.intro (graded index grade) (laws.2.2 index grade).1
  refine ⟨fields,member,sameSources,allGrades,(fun index => (laws.1 index).2.2.2),laws.2.1,?_⟩
  exact actualOriginalNative_B10_allSignedPowers_first parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades laws.2.1
    M Mnonnegative stateBound vanishing (fun index => (laws.1 index).2.2.2)
    graded (fun index grade => (laws.2.2 index grade).1)
    (fun grade => certificate.choose grade * (‖quotientEta parameters (grade+8) source‖ +
      physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+14) * ‖quotientEta parameters 8 source‖))
    (fun index grade => (laws.2.2 index grade).2)
    outer inside outerSmooth insideSmooth outerCompact insideCompact outerDisk insideDisk plateau radial low
    annular annularSmooth annularCompact annularRadial annularPartition annularPunctured

end Grad.ActualScaledNativeCoefficients

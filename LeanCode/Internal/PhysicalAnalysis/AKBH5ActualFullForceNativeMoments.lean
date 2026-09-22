import AKBH4NativeForceCurveBound

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace Grad.ActualForceMoments
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

variable (vanishing : SourceHigherVanishing source)
    (graded : ∀ index (_grade : ℕ), CoupledSpace (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index) lengthPositive)
    (sameGrade : ∀ index grade, CoupledInsertedGrade (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index) lengthPositive grade
      (originalWeightedRetainedObservation parameters (originalExhaustionRadius length index) length
        (originalExhaustionRadius_positive length lengthPositive index)
        ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index)) (graded index grade))
    (constants : ℕ → ℝ) (estimate : ∀ index grade, ‖graded index grade‖ ≤ constants grade)
include compatible vanishing sameGrade estimate

open Grad.ActualCartesianFlux

open Grad.ActualNativeCellMoments Grad.ActualCurrentPrimitives

/-- Full actual force-matrix output, including all coefficient-induced
angular and axial mixing, on the SAME reconstructed covariant family. -/
def actualCartesianForceMatrixCell (cell : ℤ) : SpatialPlane → ComplexEuclidean 3 :=
  matrixFluxCell parameters (forceMatrixFamily parameters length state.val.val.epsilon state.val.val.field)
    (forceMatrixFamily_coherent parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
      (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small))
    (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length)
    (fun index => cartesianCovariantRow (originalExhaustionRadius length index)
      (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields index))
    (fun index => (cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small
      source flat fields member sameSources allGrades index).cartesianCovariant) cell

/-- The actual completed force output has original-width joint-cell moments
of orders zero, one and two, derived from native all-grade energy. -/
theorem actualCartesianForceMatrix_nativeMoments :
    ∃ family : Grad.CartesianStartup.StartupMoments 3,
      ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
        family.field point cell = cartesianWeight parameters cell point •
          actualCartesianForceMatrixCell parameters length compact lengthPositive widthHalf widthLength state small
            source flat fields member sameSources allGrades cell point := by
  let lowSmall := originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small
  let coefficient := forceMatrixFamily parameters length state.val.val.epsilon state.val.val.field
  have coefficientCoherent := forceMatrixFamily_coherent parameters length state.val.val.rho state.val.val.epsilon state.val.val.field lowSmall
  let rows := fun index => cartesianCovariantRow (originalExhaustionRadius length index)
    (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields index)
  let curves := fun index => (cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small
    source flat fields member sameSources allGrades index).cartesianCovariant
  have coherent := cartesianCovariantRows_compatible (originalExhaustionRadius length)
    (originalExhaustionRadius_antitone length lengthPositive)
    (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields)
    (fun first second ordered => (cartesianSourcePolarAndXi_compatible parameters length compact lengthPositive widthHalf widthLength state small
      source flat fields compatible first second ordered).1)
  let forceRows := matrixFluxRows parameters coefficient coefficientCoherent (originalExhaustionRadius length)
    (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) rows
  let forceCurves := matrixFluxCurves parameters coefficient coefficientCoherent (originalExhaustionRadius length)
    (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) rows curves
  have forceCoherent := matrixFluxRows_compatible parameters coefficient coefficientCoherent (originalExhaustionRadius length)
    (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_antitone length lengthPositive) rows coherent
  obtain ⟨C,Cnonnegative,bound⟩ := forceCurve_uniformBound parameters length compact state.val
    state.val.val.rho state.val.val.epsilon state.val.val.field lowSmall 2
  exact actualCartesianFamily_outputMoments parameters length compact lengthPositive widthHalf widthLength state small
    source flat fields member sameSources allGrades vanishing graded sameGrade constants estimate
    forceRows forceCurves forceCoherent C Cnonnegative (fun index radius => bound
      (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index)
      ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) _
      (actualCartesianSevenCurves parameters length compact (originalExhaustionRadius length index)
        (originalExhaustionRadius_positive length lengthPositive index) (originalExhaustionRadius_half length lengthPositive index)
        lengthPositive widthHalf widthLength state
        (originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
        lowSmall source flat (fields index) (member index) (sameSources index) (allGrades index)) radius)

end Grad.ActualForceMoments

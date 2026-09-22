import AKBY2SameNativeAllCellCarrier

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace Grad.ActualNativeCellMoments
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


open Grad.CartesianStartup

/-- The SAME native covariant has every natural full integer-cell moment at the original width. -/
theorem actualCartesianCovariant_nativeAllCellMoments :
    ∃ family : StartupAllMoments 3,
      ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
        family.field point cell = cartesianWeight parameters cell point •
          actualCartesianCovariantCell parameters length compact lengthPositive widthHalf widthLength state small
            source flat fields member sameSources allGrades cell point := by
  let rows := fun index => cartesianCovariantRow (originalExhaustionRadius length index)
    (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields index)
  let curves := fun index => (cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small
    source flat fields member sameSources allGrades index).cartesianCovariant
  have coherent := cartesianCovariantRows_compatible (originalExhaustionRadius length)
    (originalExhaustionRadius_antitone length lengthPositive)
    (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields)
    (fun first second ordered => (cartesianSourcePolarAndXi_compatible parameters length compact lengthPositive widthHalf widthLength state small
      source flat fields compatible first second ordered).1)
  have finite (power : ℕ) :
      (∫⁻ radius in Ioc (0 : ℝ) 1, ENNReal.ofReal
        (‖gluedWeightedFamilyCurve parameters (originalExhaustionRadius length)
          (originalExhaustionRadius_positive length lengthPositive) (originalExhaustionRadius_tendsto length)
          rows curves power radius‖ ^ 2)) < ⊤ := by
    obtain ⟨C,Cnonnegative,coefficientBound⟩ := covariantCurve_uniformBound parameters length compact state.val power
    obtain ⟨constant,nonnegative,energy⟩ := actualOutputWeightedCurve_allGradeEnergy parameters length compact lengthPositive
      widthHalf widthLength state small source flat fields member sameSources allGrades vanishing graded sameGrade constants estimate
      rows curves coherent power C Cnonnegative (fun index radius => coefficientBound (originalExhaustionRadius length index)
        (originalExhaustionRadius_positive length lengthPositive index)
        ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) _
        (actualCartesianSevenCurves parameters length compact (originalExhaustionRadius length index)
          (originalExhaustionRadius_positive length lengthPositive index) (originalExhaustionRadius_half length lengthPositive index)
          lengthPositive widthHalf widthLength state
          (originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
          (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
          source flat (fields index) (member index) (sameSources index) (allGrades index)) radius)
    exact energy.trans_lt ENNReal.ofReal_lt_top
  exact ⟨sameNativeAllCellMoments parameters (originalExhaustionRadius length)
    (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive)
    rows curves coherent finite,
    sameNativeAllCellMoments_same parameters (originalExhaustionRadius length)
    (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive)
    rows curves coherent finite⟩

/-- Xi/r is extracted from the SAME seven packet at every natural inserted grade. -/
theorem actualCartesianXiOverRadius_nativeAllCellMoments :
    ∃ family : StartupAllMoments 1,
      ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
        family.field point cell = cartesianWeight parameters cell point •
          actualCartesianXiOverRadiusCell parameters length compact lengthPositive widthHalf widthLength state small
            source flat fields member sameSources allGrades cell point := by
  let rows := cartesianOriginalScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields
  let curves := cartesianSourceXiOverRadiusCurves parameters length compact lengthPositive widthHalf widthLength state small
    source flat fields member sameSources allGrades
  have coherent := fun first second ordered => (cartesianSourcePolarAndXi_compatible parameters length compact lengthPositive widthHalf widthLength
    state small source flat fields compatible first second ordered).2
  have finite (power : ℕ) :
      (∫⁻ radius in Ioc (0 : ℝ) 1, ENNReal.ofReal
        (‖gluedWeightedFamilyCurve parameters (originalExhaustionRadius length)
          (originalExhaustionRadius_positive length lengthPositive) (originalExhaustionRadius_tendsto length)
          rows curves power radius‖ ^ 2)) < ⊤ := by
    obtain ⟨constant,nonnegative,energy⟩ := actualOutputWeightedCurve_allGradeEnergy parameters length compact lengthPositive
      widthHalf widthLength state small source flat fields member sameSources allGrades vanishing graded sameGrade constants estimate
      rows curves coherent power ‖nativeXiProjection parameters‖ (norm_nonneg _) (fun _ radius => xiCurve_uniformBound _ power radius)
    exact energy.trans_lt ENNReal.ofReal_lt_top
  exact ⟨sameNativeAllCellMoments parameters (originalExhaustionRadius length)
    (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive)
    rows curves coherent finite,
    sameNativeAllCellMoments_same parameters (originalExhaustionRadius length)
    (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive)
    rows curves coherent finite⟩

end Grad.ActualNativeCellMoments

import AKBK10SameOriginalForceFamily

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace Grad.ActualCartesianWeakEquations
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

include compatible

/-- Exact Fourier fidelity of the original planar force, on the SAME
native Xi/covariant/correction cells, with actual spatial derivatives. -/
theorem actualCartesianPlanarForceCell_original (cell : ℤ) (index : ℕ) (radius : ℝ)
    (inside : radius ∈ Ioo (originalExhaustionRadius length index) 1) (polar : ℝ) :
    angularCoefficient (fun axial => planarPartMap
      (actualCartesianRawForceFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index radius ⟨inside.1.le,inside.2.le⟩ (polar,axial))) cell =
      actualCartesianPlanarForceCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell (polarPlane (radius,polar)) := by
  let a := (cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index)
  let scalarFull := (cartesianPhysicalField (originalPhysicalComponentField parameters (originalExhaustionRadius length index) length (originalExhaustionRadius_positive length lengthPositive index) ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) lengthPositive (originalWeightedRetainedObservation parameters (originalExhaustionRadius length index) length (originalExhaustionRadius_positive length lengthPositive index) ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index)) 1))
  let nativeMatrix := (sameForceMatrixCurves parameters length state.val.val.rho state.val.val.epsilon state.val.val.field (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small) (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index) ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) a)
  let point := polarPlane (radius,polar)
  let xiCell := actualCartesianXiCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell
  let covariantCell := actualCartesianCovariantCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell
  let correctionCell := actualCartesianForceCorrectionCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell
  have radiusPositive : 0 < radius := (originalExhaustionRadius_positive length lengthPositive index).trans inside.1
  have pointInside : ‖point‖ ∈ Ioo (originalExhaustionRadius length index) 1 := by
    simpa only [point,polarPlane_norm,abs_of_pos radiusPositive] using inside
  have angularDirection : radius • planeQuarterTurn (radialDirection polar) = planeQuarterTurn point := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp [point,polarPlane,collarPlane,radialDirection,planeQuarterTurn]
  have xiDerivativeContinuous := actualCartesianXiOriginal_fderiv_circle_continuous parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible index radius inside
  have xiAt : Continuous (fun axial => fderiv ℝ scalarFull (point,axial)) :=
    xiDerivativeContinuous.comp (continuous_const.prodMk continuous_id)
  have aDerivativeContinuous := nativeLocalField_fderiv_circle_continuous a.cartesianCovariant ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) radius inside
  have aAt : Continuous (fun axial => fderiv ℝ (a.cartesianCovariant.cartesianField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))) (point,axial)) :=
    aDerivativeContinuous.comp (continuous_const.prodMk continuous_id)
  have aContinuous : Continuous (fun axial => a.cartesianCovariant.fullField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (radius,polar,axial)) :=
    (a.cartesianCovariant.fullField_continuous_angles ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) radius ⟨inside.1.le,inside.2.le⟩).comp
      (continuous_const.prodMk continuous_id)
  have matrixContinuous : Continuous (fun axial => nativeMatrix.fullField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (radius,polar,axial)) :=
    (nativeMatrix.fullField_continuous_angles ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) radius ⟨inside.1.le,inside.2.le⟩).comp
      (continuous_const.prodMk continuous_id)
  have original : (fun axial => planarPartMap
      (actualCartesianRawForceFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index radius ⟨inside.1.le,inside.2.le⟩ (polar,axial))) =
      fun axial => planarPartMap (cartesianForceValue
        (planarGradientValue (fderiv ℝ scalarFull (point,axial)))
        (fderiv ℝ (a.cartesianCovariant.cartesianField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))) (point,axial) (planeQuarterTurn point,0))
        (a.cartesianCovariant.fullField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (radius,polar,axial))
        ((2 : ℂ) • nativeMatrix.fullField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (radius,polar,axial))) := by
    funext axial
    rw [actualCartesianRawForceFamily_native parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index radius ⟨inside.1.le,inside.2.le⟩ (polar,axial)]
    simp only [angularDirection]
    rfl
  rw [original]
  change _ = nativePlanarForceCell xiCell covariantCell correctionCell point
  apply nativePlanarForceCell_fourier xiCell covariantCell correctionCell point cell
    (fun axial => planarGradientValue (fderiv ℝ scalarFull (point,axial)))
    (fun axial => fderiv ℝ (a.cartesianCovariant.cartesianField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))) (point,axial) (planeQuarterTurn point,0))
    (fun axial => a.cartesianCovariant.fullField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (radius,polar,axial))
    (fun axial => (2 : ℂ) • nativeMatrix.fullField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (radius,polar,axial))
    (planarGradientValue_continuous.comp xiAt) (aAt.clm_apply continuous_const) aContinuous ((continuous_const (y := (2 : ℂ))).smul matrixContinuous)
  · apply nativeScalarGradient_axialCell
    · intro direction
      exact actualCartesianXiCell_fderiv_original parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible cell index point pointInside direction
    · intro direction
      exact xiAt.clm_apply continuous_const
  · exact (actualCartesianCovariantCell_fderiv_local parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible cell index point pointInside (planeQuarterTurn point)).symm
  · have same := actualCartesianCovariantCell_local parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible cell index point pointInside
    have cartesianSame : (fun axial => a.cartesianCovariant.cartesianField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (point,axial)) =
        fun axial => a.cartesianCovariant.fullField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (radius,polar,axial) := by
      funext axial
      simpa only [point,polarPlane_originalParametrization] using
        a.cartesianCovariant.cartesianField_polar ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) radius radiusPositive polar axial
    change covariantCell point = angularCoefficient (fun axial => a.cartesianCovariant.cartesianField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (point,axial)) cell at same
    rw [cartesianSame] at same
    exact same.symm
  · have same := nativeForceCorrectionCell_planar parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
      (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small) (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
      (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
      (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive)
      (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields)
      (cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades)
      (fun first second ordered => (cartesianSourcePolarAndXi_compatible parameters length compact lengthPositive widthHalf widthLength state small source flat fields compatible first second ordered).1)
      cell index radius ⟨inside.1.le,inside.2.le⟩ polar
    rw [polarPlane_originalParametrization] at same
    exact same.symm

end Grad.ActualCartesianWeakEquations

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

private theorem originalPolarQuarter_continuous : Continuous polarQuarter := by
  unfold polarQuarter
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℂ)).comp
  apply continuous_pi
  intro coordinate
  fin_cases coordinate <;> dsimp <;> fun_prop

private theorem originalPlanarPart_continuous : Continuous Grad.ActualCartesianEquations.planarPart := by
  unfold Grad.ActualCartesianEquations.planarPart
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℂ)).comp
  apply continuous_pi
  intro coordinate
  fin_cases coordinate <;> dsimp <;> fun_prop

theorem originalForceValue_continuous {S : Type} [TopologicalSpace S]
    (gradient rotation covariant correction : S → ComplexEuclidean 3)
    (gradientContinuous : Continuous gradient) (rotationContinuous : Continuous rotation)
    (covariantContinuous : Continuous covariant) (correctionContinuous : Continuous correction) :
    Continuous (fun point => cartesianForceValue (gradient point) (rotation point) (covariant point) (correction point)) :=
  originalPlanarPart_continuous.comp
    (((gradientContinuous.sub rotationContinuous).sub (originalPolarQuarter_continuous.comp covariantContinuous)).add correctionContinuous)

include compatible

/-- The literal original force expression is jointly continuous in both
angles at each strict collar radius. All derivatives are the actual ones. -/
theorem actualCartesianRawForceFamily_continuous (index : ℕ) (radius : ℝ)
    (inside : radius ∈ Ioo (originalExhaustionRadius length index) 1) :
    Continuous (actualCartesianRawForceFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index radius ⟨inside.1.le,inside.2.le⟩) := by
  let a := (cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index)
  let scalarFull := (cartesianPhysicalField (originalPhysicalComponentField parameters (originalExhaustionRadius length index) length (originalExhaustionRadius_positive length lengthPositive index) ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) lengthPositive (originalWeightedRetainedObservation parameters (originalExhaustionRadius length index) length (originalExhaustionRadius_positive length lengthPositive index) ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index)) 1))
  let nativeMatrix := (sameForceMatrixCurves parameters length state.val.val.rho state.val.val.epsilon state.val.val.field (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small) (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index) ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) a)
  have scalarDerivativeContinuous := actualCartesianXiOriginal_fderiv_circle_continuous parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible index radius inside
  have aDerivativeContinuous := nativeLocalField_fderiv_circle_continuous a.cartesianCovariant ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) radius inside
  have directionContinuous : Continuous (fun angles : ℝ × ℝ =>
      (radius • planeQuarterTurn (radialDirection angles.1),(0 : ℝ))) :=
    ((Grad.NonlinearQuotient.quarterTurnCLM.continuous.comp (radialDirection_smooth.continuous.comp continuous_fst)).const_smul radius).prodMk continuous_const
  have same : actualCartesianRawForceFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index radius ⟨inside.1.le,inside.2.le⟩ =
      fun angles : ℝ × ℝ => cartesianForceValue
        (planarGradientValue (fderiv ℝ scalarFull (polarPlane (radius,angles.1),angles.2)))
        (fderiv ℝ (a.cartesianCovariant.cartesianField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))) (polarPlane (radius,angles.1),angles.2)
          (radius • planeQuarterTurn (radialDirection angles.1),0))
        (a.cartesianCovariant.fullField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (radius,angles))
        ((2 : ℂ) • nativeMatrix.fullField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (radius,angles)) := by
    funext angles
    exact actualCartesianRawForceFamily_native parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index radius ⟨inside.1.le,inside.2.le⟩ angles
  rw [same]
  exact originalForceValue_continuous _ _ _ _
    (planarGradientValue_continuous.comp scalarDerivativeContinuous)
    (aDerivativeContinuous.clm_apply directionContinuous)
    (a.cartesianCovariant.fullField_continuous_angles ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) radius ⟨inside.1.le,inside.2.le⟩)
    ((continuous_const (y := (2 : ℂ))).smul (nativeMatrix.fullField_continuous_angles ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) radius ⟨inside.1.le,inside.2.le⟩))

end Grad.ActualCartesianWeakEquations

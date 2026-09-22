import AKBJ3SameGlobalXiFidelityAndMean
import AKBK1SameGlobalCellDerivatives

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace Grad.ActualScalarWeakEquations
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
open Grad.AnnularGeneralSourceRegularity Grad.ActualSmoothPhysicalField Grad.PuncturedRetainedEnergy
variable (compatible : ∀ first second (included : originalExhaustionRadius length first ≤ originalExhaustionRadius length second),
      originalFiveBlockRestriction parameters (originalExhaustionRadius length first) (originalExhaustionRadius length second) length
        (originalExhaustionRadius_positive length lengthPositive first) (originalExhaustionRadius_positive length lengthPositive second)
        ((originalExhaustionRadius_half length lengthPositive second).trans_lt (by norm_num)) lengthPositive included (fields first) = fields second)

open Grad.ActualCartesianWeakEquations Grad.PDEBootstrap
include compatible

/-- Genuine punctured Cartesian smoothness of the SAME scalar Xi. -/
theorem actualCartesianXiFamilyField_smooth :
    ContDiffOn ℝ ∞ (actualCartesianXiFamilyField parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades)
      ((openUnitDisk \ {(0 : Spatial)}) ×ˢ (univ : Set ℝ)) := by
  intro point inside
  have nonzero : point.1 ≠ 0 := by simpa only [mem_singleton_iff] using inside.1.2
  have radiusSmooth : ContDiffAt ℝ ∞ (fun current : Spatial × ℝ => ‖current.1‖) point :=
    (contDiffAt_norm ℝ nonzero).comp point contDiffAt_fst
  exact radiusSmooth.contDiffWithinAt.smul
    (nativeFamilyField_smooth parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive) (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive) (cartesianOriginalScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields) (cartesianSourceXiOverRadiusCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades) (fun first second ordered => (cartesianSourcePolarAndXi_compatible parameters length compact lengthPositive widthHalf widthLength state small source flat fields compatible first second ordered).2) point inside)

/-- Xi's exact all-angle Cartesian cell is the axial coefficient of this same globally glued field. -/
theorem actualCartesianXiCell_actual (cell : ℤ) (point : Spatial) (nonzero : point ≠ 0) (inside : ‖point‖ < 1) :
    actualCartesianXiCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point =
      angularCoefficient (fun axial => actualCartesianXiFamilyField parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades (point,axial)) cell := by
  have actual := nativeFamilyCell_actual parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive) (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive) (cartesianOriginalScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields) (cartesianSourceXiOverRadiusCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades) (fun first second ordered => (cartesianSourcePolarAndXi_compatible parameters length compact lengthPositive widthHalf widthLength state small source flat fields compatible first second ordered).2) cell point nonzero inside
  change actualCartesianXiOverRadiusCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point =
    angularCoefficient (fun axial => actualCartesianXiOverRadiusFamilyField parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades (point,axial)) cell at actual
  unfold actualCartesianXiCell actualCartesianXiFamilyField
  rw [actual]
  simp_rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact (angularCoefficient_smul_continuous (‖point‖ : ℂ)
    (fun axial => actualCartesianXiOverRadiusFamilyField parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades (point,axial)) cell).symm

/-- The full Cartesian derivative agrees with the original scalar derivative throughout every strict collar. -/
theorem actualCartesianXiFamilyField_fderiv_same (index : ℕ) (point : Spatial × ℝ)
    (inside : ‖point.1‖ ∈ Ioo (originalExhaustionRadius length index) 1) :
    fderiv ℝ (actualCartesianXiFamilyField parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades) point =
      fderiv ℝ (cartesianPhysicalField (originalPhysicalComponentField parameters (originalExhaustionRadius length index) length (originalExhaustionRadius_positive length lengthPositive index) ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) lengthPositive (originalWeightedRetainedObservation parameters (originalExhaustionRadius length index) length (originalExhaustionRadius_positive length lengthPositive index) ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index)) 1)) point := by
  have neighborhood : {current : Spatial × ℝ | ‖current.1‖ ∈ Ioo (originalExhaustionRadius length index) 1} ∈ 𝓝 point :=
    (isOpen_Ioo.preimage (continuous_norm.comp continuous_fst)).mem_nhds inside
  have same : actualCartesianXiFamilyField parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades =ᶠ[𝓝 point] cartesianPhysicalField (originalPhysicalComponentField parameters (originalExhaustionRadius length index) length (originalExhaustionRadius_positive length lengthPositive index) ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) lengthPositive (originalWeightedRetainedObservation parameters (originalExhaustionRadius length index) length (originalExhaustionRadius_positive length lengthPositive index) ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index)) 1) := by
    filter_upwards [neighborhood] with current collarMembership
    exact actualCartesianXiFamilyField_same parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible index current.1 ⟨collarMembership.1.le,collarMembership.2.le⟩ current.2
  exact same.fderiv_eq

/-- Spatial differentiation of the SAME Xi cell commutes with genuine axial Fourier projection. -/
theorem actualCartesianXiCell_fderiv_apply (cell : ℤ) (point : Spatial) (nonzero : point ≠ 0)
    (inside : ‖point‖ < 1) (direction : Spatial) :
    fderiv ℝ (actualCartesianXiCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) point direction =
      angularCoefficient (fun axial => fderiv ℝ (actualCartesianXiFamilyField parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades) (point,axial) (direction,0)) cell := by
  let domain : Set Spatial := openUnitDisk \ {(0 : Spatial)}
  have openDomain : IsOpen domain := openUnitDisk_isOpen.sdiff isClosed_singleton
  have pointInside : point ∈ domain := ⟨inside,by simpa only [mem_singleton_iff] using nonzero⟩
  have same : actualCartesianXiCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell =ᶠ[𝓝 point]
      (fun current => angularCoefficient (fun axial => actualCartesianXiFamilyField parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades (current,axial)) cell) := by
    filter_upwards [openDomain.mem_nhds pointInside] with current membership
    exact actualCartesianXiCell_actual parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible cell current
      (by simpa only [mem_singleton_iff] using membership.2) membership.1
  rw [same.fderiv_eq,originalCell_fderiv_apply openDomain _
    (actualCartesianXiFamilyField_smooth parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible) cell point pointInside direction]
  rfl

/-- Direct shared consumer: exact original scalar derivative, same axial cell, original collar. -/
theorem actualCartesianXiCell_fderiv_original (cell : ℤ) (index : ℕ) (point : Spatial)
    (inside : ‖point‖ ∈ Ioo (originalExhaustionRadius length index) 1) (direction : Spatial) :
    fderiv ℝ (actualCartesianXiCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) point direction =
      angularCoefficient (fun axial => fderiv ℝ (cartesianPhysicalField (originalPhysicalComponentField parameters (originalExhaustionRadius length index) length (originalExhaustionRadius_positive length lengthPositive index) ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) lengthPositive (originalWeightedRetainedObservation parameters (originalExhaustionRadius length index) length (originalExhaustionRadius_positive length lengthPositive index) ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index)) 1)) (point,axial) (direction,0)) cell := by
  rw [actualCartesianXiCell_fderiv_apply parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible cell point
    (norm_pos_iff.mp ((originalExhaustionRadius_positive length lengthPositive index).trans inside.1)) inside.2 direction]
  congr 1
  funext axial
  rw [actualCartesianXiFamilyField_fderiv_same parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible index (point,axial) inside]

end Grad.ActualScalarWeakEquations

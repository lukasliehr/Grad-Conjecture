import AKCA5ActualCriticalInsertedOutput

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace Grad.OriginalCoreRealization
open Grad.ActualNativeCellMoments
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
include vanishing sameGrade estimate

/-- Cofinal native energy for any SAME compatible output with a proved
uniform all-grade action bound on the actual seven packet. -/
theorem actualOutputWeightedCurve_criticalAllGradeEnergy {dimension : ℕ}
    (rows : ∀ index, DivisionRow dimension (originalExhaustionRadius length index))
    (curves : ∀ index, SmoothLowPhysicalRow parameters (originalExhaustionRadius length index)
      (originalExhaustionRadius_positive length lengthPositive index) (rows index))
    (coherent : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction dimension (originalExhaustionRadius length second) (originalExhaustionRadius length first)
        (originalExhaustionRadius_antitone length lengthPositive ordered) (rows second) = rows first)
    (grade : ℕ) (C : ℝ) (Cnonnegative : 0 ≤ C)
    (coefficientBound : ∀ index radius, ‖(curves index).curve grade radius‖ ≤ C *
      ‖(actualCartesianSevenCurves parameters length compact (originalExhaustionRadius length index)
        (originalExhaustionRadius_positive length lengthPositive index) (originalExhaustionRadius_half length lengthPositive index)
        lengthPositive widthHalf widthLength state
        (originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
        (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
        source flat (fields index) (member index) (sameSources index) (allGrades index)).curve grade radius‖) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      (∫⁻ radius in Ioc (0 : ℝ) 1, ENNReal.ofReal
        (‖radius ^ (-(3 / 2 : ℝ)) • gluedWeightedFamilyCurve parameters (originalExhaustionRadius length)
          (originalExhaustionRadius_positive length lengthPositive) (originalExhaustionRadius_tendsto length)
          rows curves
          grade radius‖ ^ 2)) ≤ ENNReal.ofReal (constant ^ 2) := by
  let lowSmall := originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small
  let payment := originalSourceAllocationConstant parameters length grade *
    (‖quotientEta parameters (grade+8) source‖ + physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+14) * ‖quotientEta parameters 8 source‖)
  let bound := (11+4*length) * constants grade + 3 * payment
  have constantsNonnegative : 0 ≤ constants grade := (norm_nonneg (graded 0 grade)).trans (estimate 0 grade)
  have paymentNonnegative : 0 ≤ payment := mul_nonneg (originalSourceAllocationConstant_positive parameters length grade).le
    (add_nonneg (norm_nonneg _) (mul_nonneg (physicalBudget_nonnegative _ _ _ _ _) (norm_nonneg _)))
  have boundNonnegative : 0 ≤ bound := by dsimp [bound]; positivity
  refine ⟨C * bound,mul_nonneg Cnonnegative boundNonnegative,?_⟩
  have collarBound (index : ℕ) :
      (∫⁻ radius in Icc (originalExhaustionRadius length index) 1, ENNReal.ofReal
        (‖radius ^ (-(3 / 2 : ℝ)) • gluedWeightedFamilyCurve parameters (originalExhaustionRadius length)
          (originalExhaustionRadius_positive length lengthPositive) (originalExhaustionRadius_tendsto length)
          rows curves grade radius‖ ^ 2)) ≤ ENNReal.ofReal ((C * bound)^2) := by
    have localEnergy := actualObservedOutput_criticalInsertedEnergy parameters length compact (originalExhaustionRadius length index)
      (originalExhaustionRadius_positive length lengthPositive index) (originalExhaustionRadius_half length lengthPositive index)
      lengthPositive widthHalf widthLength state
      (originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
      lowSmall source flat (fields index) (member index) (sameSources index) (allGrades index) grade ((curves index).curve grade)
      (graded index grade) (sameGrade index grade) C Cnonnegative (coefficientBound index)
    have paid := actualOriginalSourceDatum_EX_bound parameters length state.val.val.rho state.val.val.epsilon lengthPositive state.val.val.field
      lowSmall grade (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index)
      ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) source flat vanishing
    calc
      _ = ∫⁻ radius in Icc (originalExhaustionRadius length index) 1, ENNReal.ofReal (‖radius ^ (-(3 / 2 : ℝ)) • (curves index).curve grade radius‖^2) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
        rw [gluedWeightedFamilyCurve_same parameters (originalExhaustionRadius length)
          (originalExhaustionRadius_positive length lengthPositive)
          (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
          (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive)
          rows curves coherent grade index radius inside]
      _ ≤ _ := localEnergy.trans (ENNReal.ofReal_le_ofReal ((sq_le_sq₀ (by positivity) (mul_nonneg Cnonnegative boundNonnegative)).mpr
        (mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_left (estimate index grade) (by positivity : 0 ≤ 11+4*length))
          (mul_le_mul_of_nonneg_left paid (by norm_num : (0 : ℝ) ≤ 3))) Cnonnegative)))
  have global := cofinalEnergy_bound 1 (originalExhaustionRadius length)
    (originalExhaustionRadius_positive length lengthPositive) (originalExhaustionRadius_antitone length lengthPositive)
    (originalExhaustionRadius_tendsto length)
    (fun radius => ENNReal.ofReal (‖radius ^ (-(3 / 2 : ℝ)) • gluedWeightedFamilyCurve parameters (originalExhaustionRadius length)
      (originalExhaustionRadius_positive length lengthPositive) (originalExhaustionRadius_tendsto length)
      rows curves grade radius‖ ^ 2)) 0 (ENNReal.ofReal ((C * bound)^2))
    (fun index => by simpa only [add_zero] using collarBound index)
  simpa only [add_zero] using global

end Grad.OriginalCoreRealization

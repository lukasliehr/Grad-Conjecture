import GaugeModeAlgebra

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers Grad.GaugeCoefficients.Algebra

/-- Generic sandwich collapse for two norm-summable operator mode families
whose sandwiched pair compositions collapse to scalar multiples of a fixed
shifted family with delta-convolution rows. -/
theorem sandwich_operator_collapse {Space : Type*} [NormedAddCommGroup Space]
    [NormedSpace ℂ Space] [CompleteSpace Space]
    (sandwich : Space →L[ℂ] Space) (firstMode secondMode : ℤ → Space →L[ℂ] Space)
    (firstTotal secondTotal : Space →L[ℂ] Space)
    (firstNorms : Summable (fun shift => ‖firstMode shift‖))
    (secondNorms : Summable (fun shift => ‖secondMode shift‖))
    (firstHasSum : HasSum firstMode firstTotal)
    (secondHasSum : HasSum secondMode secondTotal)
    (base : ℤ → Space →L[ℂ] Space) (scalarWeight : ℤ → ℤ → ℂ)
    (collapse : ∀ firstShift secondShift : ℤ,
      sandwich.comp ((firstMode firstShift).comp ((secondMode secondShift).comp sandwich)) =
        scalarWeight firstShift secondShift • base (firstShift + secondShift))
    (rowSummable : ∀ target : ℤ, Summable (fun shift => scalarWeight shift (target - shift)))
    (rowDelta : ∀ target : ℤ, (∑' shift, scalarWeight shift (target - shift)) =
      if target = 0 then 1 else 0)
    (baseZero : base 0 = sandwich) :
    sandwich.comp (firstTotal.comp (secondTotal.comp sandwich)) = sandwich := by
  have secondStep : HasSum (fun shift => (secondMode shift).comp sandwich)
      (secondTotal.comp sandwich) :=
    (((ContinuousLinearMap.compL ℂ Space Space Space).flip sandwich)).hasSum secondHasSum
  have innerStep (shift : ℤ) : HasSum
      (fun inner => sandwich.comp ((firstMode shift).comp ((secondMode inner).comp sandwich)))
      (sandwich.comp ((firstMode shift).comp (secondTotal.comp sandwich))) :=
    (ContinuousLinearMap.compL ℂ Space Space Space sandwich).hasSum
      ((ContinuousLinearMap.compL ℂ Space Space Space (firstMode shift)).hasSum secondStep)
  have outerStep : HasSum (fun shift => sandwich.comp ((firstMode shift).comp
      (secondTotal.comp sandwich)))
      (sandwich.comp (firstTotal.comp (secondTotal.comp sandwich))) :=
    (ContinuousLinearMap.compL ℂ Space Space Space sandwich).hasSum
      (((ContinuousLinearMap.compL ℂ Space Space Space).flip
        (secondTotal.comp sandwich)).hasSum firstHasSum)
  have pairNormBound (pair : ℤ × ℤ) :
      ‖sandwich.comp ((firstMode pair.1).comp ((secondMode pair.2).comp sandwich))‖ ≤
      (‖sandwich‖ * ‖firstMode pair.1‖) * (‖secondMode pair.2‖ * ‖sandwich‖) := by
    calc ‖sandwich.comp ((firstMode pair.1).comp ((secondMode pair.2).comp sandwich))‖
        ≤ ‖sandwich‖ * ‖(firstMode pair.1).comp ((secondMode pair.2).comp sandwich)‖ :=
          sandwich.opNorm_comp_le _
      _ ≤ ‖sandwich‖ * (‖firstMode pair.1‖ * ‖(secondMode pair.2).comp sandwich‖) :=
          mul_le_mul_of_nonneg_left ((firstMode pair.1).opNorm_comp_le _) (norm_nonneg sandwich)
      _ ≤ ‖sandwich‖ * (‖firstMode pair.1‖ * (‖secondMode pair.2‖ * ‖sandwich‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            ((secondMode pair.2).opNorm_comp_le sandwich) (norm_nonneg _)) (norm_nonneg sandwich)
      _ = (‖sandwich‖ * ‖firstMode pair.1‖) * (‖secondMode pair.2‖ * ‖sandwich‖) := by ring
  have pairMajorant : Summable (fun pair : ℤ × ℤ =>
      (‖sandwich‖ * ‖firstMode pair.1‖) * (‖secondMode pair.2‖ * ‖sandwich‖)) :=
    Summable.mul_of_nonneg (firstNorms.mul_left ‖sandwich‖) (secondNorms.mul_right ‖sandwich‖)
      (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have pairNorm : Summable (fun pair : ℤ × ℤ =>
      ‖sandwich.comp ((firstMode pair.1).comp ((secondMode pair.2).comp sandwich))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) pairNormBound pairMajorant
  have pairSummable : Summable (fun pair : ℤ × ℤ =>
      sandwich.comp ((firstMode pair.1).comp ((secondMode pair.2).comp sandwich))) :=
    pairNorm.of_norm
  have iteratedIdentity : sandwich.comp (firstTotal.comp (secondTotal.comp sandwich)) =
      ∑' pair : ℤ × ℤ,
        sandwich.comp ((firstMode pair.1).comp ((secondMode pair.2).comp sandwich)) := by
    rw [← outerStep.tsum_eq, pairSummable.tsum_prod]
    exact tsum_congr (fun shift => ((innerStep shift).tsum_eq).symm)
  have collapsedSummable : Summable (fun pair : ℤ × ℤ =>
      scalarWeight pair.1 pair.2 • base (pair.1 + pair.2)) :=
    pairSummable.congr (fun pair => collapse pair.1 pair.2)
  have reindexedSummable : Summable (fun pair : ℤ × ℤ =>
      scalarWeight (cellConvolutionEquiv pair).1 (cellConvolutionEquiv pair).2 •
        base ((cellConvolutionEquiv pair).1 + (cellConvolutionEquiv pair).2)) :=
    cellConvolutionEquiv.summable_iff.mpr collapsedSummable
  have pairIdentity : (∑' pair : ℤ × ℤ,
      sandwich.comp ((firstMode pair.1).comp ((secondMode pair.2).comp sandwich))) =
      ∑' target : ℤ, ∑' shift : ℤ,
        scalarWeight (cellConvolutionEquiv (target, shift)).1
            (cellConvolutionEquiv (target, shift)).2 •
          base ((cellConvolutionEquiv (target, shift)).1 +
            (cellConvolutionEquiv (target, shift)).2) := by
    rw [tsum_congr (fun pair : ℤ × ℤ => collapse pair.1 pair.2),
      ← cellConvolutionEquiv.tsum_eq (fun pair : ℤ × ℤ =>
        scalarWeight pair.1 pair.2 • base (pair.1 + pair.2)),
      reindexedSummable.tsum_prod]
  have innerIdentity (target : ℤ) : (∑' shift : ℤ,
      scalarWeight (cellConvolutionEquiv (target, shift)).1
          (cellConvolutionEquiv (target, shift)).2 •
        base ((cellConvolutionEquiv (target, shift)).1 +
          (cellConvolutionEquiv (target, shift)).2)) =
      (if target = 0 then (1 : ℂ) else 0) • base target := by
    have termIdentity (shift : ℤ) :
        scalarWeight (cellConvolutionEquiv (target, shift)).1
            (cellConvolutionEquiv (target, shift)).2 •
          base ((cellConvolutionEquiv (target, shift)).1 +
            (cellConvolutionEquiv (target, shift)).2) =
        scalarWeight shift (target - shift) • base target := by
      have shiftIdentity : shift + (target - shift) = target := by ring
      show scalarWeight shift (target - shift) • base (shift + (target - shift)) = _
      rw [shiftIdentity]
    rw [tsum_congr termIdentity,
      ((rowSummable target).hasSum.smul_const (base target)).tsum_eq, rowDelta target]
  have deltaIdentity : (∑' target : ℤ, (if target = 0 then (1 : ℂ) else 0) • base target) =
      sandwich := by
    have pointIdentity (target : ℤ) : (if target = 0 then (1 : ℂ) else 0) • base target =
        if target = 0 then base 0 else 0 := by
      by_cases zeroTarget : target = 0
      · rw [if_pos zeroTarget, if_pos zeroTarget, zeroTarget, one_smul]
      · rw [if_neg zeroTarget, if_neg zeroTarget, zero_smul]
    rw [tsum_congr pointIdentity, tsum_ite_eq, baseZero]
  rw [iteratedIdentity, pairIdentity, tsum_congr innerIdentity, deltaIdentity]

/-- Sandwiching the composition of two completed cell multipliers between two
tangential projections collapses to the tangential projection whenever the
scalar trace convolution of the two coefficient families is the literal
delta family of twice the identity, exactly as in the written N13 computation. -/
theorem tangentialCompleted_multiplier_sandwich {grade : ℕ} (parameters : PhaseParameters)
    (firstCoefficients secondCoefficients : ℤ → ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (firstSummable : Summable (envelopeTerm parameters grade firstCoefficients))
    (secondSummable : Summable (envelopeTerm parameters grade secondCoefficients))
    (traceSummable : ∀ target : ℤ, Summable (fun shift =>
      operatorTrace ((firstCoefficients shift).comp (secondCoefficients (target - shift)))))
    (traceDelta : ∀ target : ℤ, (∑' shift,
        operatorTrace ((firstCoefficients shift).comp (secondCoefficients (target - shift)))) =
      if target = 0 then 2 else 0) :
    (tangentialCompleted (grade := grade) parameters).comp
        ((completedMultiplier parameters firstCoefficients).comp
          ((completedMultiplier parameters secondCoefficients).comp
            (tangentialCompleted parameters))) =
      tangentialCompleted parameters := by
  have firstNorms : Summable (fun shift =>
      ‖singleModeCompleted (grade := grade) parameters shift (firstCoefficients shift)‖) :=
    singleModeCompleted_norm_summable parameters firstCoefficients firstSummable
  have secondNorms : Summable (fun shift =>
      ‖singleModeCompleted (grade := grade) parameters shift (secondCoefficients shift)‖) :=
    singleModeCompleted_norm_summable parameters secondCoefficients secondSummable
  apply sandwich_operator_collapse (tangentialCompleted parameters)
    (fun shift => singleModeCompleted parameters shift (firstCoefficients shift))
    (fun shift => singleModeCompleted parameters shift (secondCoefficients shift))
    (completedMultiplier parameters firstCoefficients)
    (completedMultiplier parameters secondCoefficients)
    firstNorms secondNorms firstNorms.of_norm.hasSum secondNorms.of_norm.hasSum
    (fun target => (singleModeCompleted parameters target
      (ContinuousLinearMap.id ℂ (ComplexEuclidean 2))).comp (tangentialCompleted parameters))
    (fun firstShift secondShift => operatorTrace
      ((firstCoefficients firstShift).comp (secondCoefficients secondShift)) / 2)
  · intro firstShift secondShift
    rw [← ContinuousLinearMap.comp_assoc (singleModeCompleted parameters firstShift
      (firstCoefficients firstShift)) (singleModeCompleted parameters secondShift
      (secondCoefficients secondShift)) (tangentialCompleted parameters),
      singleModeCompleted_comp]
    exact tangentialCompleted_mode_collapse parameters (firstShift + secondShift) _
  · intro target
    exact (traceSummable target).div_const 2
  · intro target
    rw [((traceSummable target).hasSum.div_const 2).tsum_eq, traceDelta target]
    by_cases zeroTarget : target = 0
    · rw [if_pos zeroTarget, if_pos zeroTarget]
      norm_num
    · rw [if_neg zeroTarget, if_neg zeroTarget]
      norm_num
  · rw [singleModeCompleted_zero_id, ContinuousLinearMap.id_comp]

/-- Descent of the completed sandwich collapse to the original smooth core. -/
theorem tangentialCore_multiplier_sandwich (parameters : PhaseParameters)
    (firstCoefficients secondCoefficients : ℤ → ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (firstSummable : ∀ grade, Summable (envelopeTerm parameters grade firstCoefficients))
    (secondSummable : ∀ grade, Summable (envelopeTerm parameters grade secondCoefficients))
    (traceSummable : ∀ target : ℤ, Summable (fun shift =>
      operatorTrace ((firstCoefficients shift).comp (secondCoefficients (target - shift)))))
    (traceDelta : ∀ target : ℤ, (∑' shift,
        operatorTrace ((firstCoefficients shift).comp (secondCoefficients (target - shift)))) =
      if target = 0 then 2 else 0)
    (field : ACore parameters 2) :
    tangentialCore parameters (smoothMultiplier parameters firstCoefficients firstSummable
        (smoothMultiplier parameters secondCoefficients secondSummable
          (tangentialCore parameters field))) =
      tangentialCore parameters field := by
  have etaTangential (inner : ACore parameters 2) :
      aGradeEta parameters (GradeCore.ofCoreLinear (grade := 0) (tangentialCore parameters inner)) =
        tangentialCompleted parameters (aGradeEta parameters (GradeCore.ofCoreLinear inner)) := by
    calc aGradeEta parameters
          (GradeCore.ofCoreLinear (grade := 0) (tangentialCore parameters inner))
        = aGradeEta parameters (tangentialGradeCore parameters (GradeCore.ofCoreLinear inner)) :=
          congrArg (aGradeEta parameters) (GradeCore.toCore_injective rfl)
      _ = tangentialCompleted parameters
            (aGradeEta parameters (GradeCore.ofCoreLinear inner)) :=
          (tangentialCompleted_eta parameters (GradeCore.ofCoreLinear inner)).symm
  have completedIdentity := congrFun (congrArg DFunLike.coe
    (tangentialCompleted_multiplier_sandwich (grade := 0) parameters firstCoefficients
      secondCoefficients (firstSummable 0) (secondSummable 0) traceSummable traceDelta))
    (aGradeEta parameters (GradeCore.ofCoreLinear (grade := 0) field))
  simp only [ContinuousLinearMap.comp_apply] at completedIdentity
  have leftChain : aGradeEta parameters (GradeCore.ofCoreLinear (grade := 0)
      (tangentialCore parameters (smoothMultiplier parameters firstCoefficients firstSummable
        (smoothMultiplier parameters secondCoefficients secondSummable
          (tangentialCore parameters field))))) =
      aGradeEta parameters (GradeCore.ofCoreLinear (grade := 0)
        (tangentialCore parameters field)) := by
    rw [etaTangential, smoothMultiplier_eta, smoothMultiplier_eta, etaTangential,
      completedIdentity]
  have etaInjective : ∀ first second : GradeCore parameters 2 0,
      aGradeEta parameters first = aGradeEta parameters second → first = second := by
    intro first second equal
    have zeroNorm : ‖first - second‖ = 0 := by
      rw [← aGradeEta_norm parameters (first - second), map_sub, equal, sub_self, norm_zero]
    exact sub_eq_zero.mp (norm_eq_zero.mp zeroNorm)
  have coreEqual := etaInjective _ _ leftChain
  have := congrArg (fun value : GradeCore parameters 2 0 => value.toCore) coreEqual
  exact this

end Grad.Constraints.Gauges

import GC10Bilinear

noncomputable section

set_option maxHeartbeats 3000000

open Set
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets
open Grad.GaugeCoefficients.Envelope
open scoped BigOperators ContDiff ENNReal Topology

namespace Grad.GaugeCoefficients.Algebra

theorem gradeProductConstant_nonnegative (grade : ℕ) :
    0 ≤ gradeProductConstant grade := by
  unfold gradeProductConstant
  positivity

def rawCompositionLeftLinear {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (inner : WeightedAmbient grade inputDimension middleDimension) :
    WeightedAmbient grade middleDimension outputDimension →ₗ[ℂ]
      WeightedAmbient grade inputDimension outputDimension where
  toFun outer := rawComposition admissible grade outer inner
  map_add' outerFirst outerSecond :=
    rawComposition_add_outer admissible grade outerFirst outerSecond inner
  map_smul' scalar outer :=
    rawComposition_smul_outer admissible grade scalar outer inner

theorem rawComposition_zero_outer {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (inner : WeightedAmbient grade inputDimension middleDimension) :
    rawComposition admissible grade
        (0 : WeightedAmbient grade middleDimension outputDimension) inner = 0 :=
  (rawCompositionLeftLinear admissible grade inner).map_zero

def rawCompositionLeft {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (inner : WeightedAmbient grade inputDimension middleDimension) :
    WeightedAmbient grade middleDimension outputDimension →L[ℂ]
      WeightedAmbient grade inputDimension outputDimension :=
  (rawCompositionLeftLinear admissible grade inner).mkContinuous
    (gradeProductConstant grade * ‖inner‖) (fun outer => by
      change ‖rawComposition admissible grade outer inner‖ ≤
        (gradeProductConstant grade * ‖inner‖) * ‖outer‖
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        (rawComposition_norm_le admissible grade outer inner))

@[simp]
theorem rawCompositionLeft_apply {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (inner : WeightedAmbient grade inputDimension middleDimension)
    (outer : WeightedAmbient grade middleDimension outputDimension) :
    rawCompositionLeft admissible grade inner outer =
      rawComposition admissible grade outer inner := rfl

def rawCompositionRightLinear {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : WeightedAmbient grade middleDimension outputDimension) :
    WeightedAmbient grade inputDimension middleDimension →ₗ[ℂ]
      WeightedAmbient grade inputDimension outputDimension where
  toFun inner := rawComposition admissible grade outer inner
  map_add' innerFirst innerSecond :=
    rawComposition_add_inner admissible grade outer innerFirst innerSecond
  map_smul' scalar inner :=
    rawComposition_smul_inner admissible grade scalar outer inner

theorem rawComposition_zero_inner {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : WeightedAmbient grade middleDimension outputDimension) :
    rawComposition admissible grade outer
        (0 : WeightedAmbient grade inputDimension middleDimension) = 0 :=
  (rawCompositionRightLinear admissible grade outer).map_zero

def rawCompositionRight {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : WeightedAmbient grade middleDimension outputDimension) :
    WeightedAmbient grade inputDimension middleDimension →L[ℂ]
      WeightedAmbient grade inputDimension outputDimension :=
  (rawCompositionRightLinear admissible grade outer).mkContinuous
    (gradeProductConstant grade * ‖outer‖) (fun inner => by
      change ‖rawComposition admissible grade outer inner‖ ≤
        (gradeProductConstant grade * ‖outer‖) * ‖inner‖
      simpa only [mul_assoc] using
        (rawComposition_norm_le admissible grade outer inner))

@[simp]
theorem rawCompositionRight_apply {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : WeightedAmbient grade middleDimension outputDimension)
    (inner : WeightedAmbient grade inputDimension middleDimension) :
    rawCompositionRight admissible grade outer inner =
      rawComposition admissible grade outer inner := rfl

theorem rawComposition_mem_smoothCore {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : smoothCore L sigma gamma ell grade middleDimension outputDimension)
    (inner : smoothCore L sigma gamma ell grade inputDimension middleDimension) :
    rawComposition admissible grade outer.1 inner.1 ∈
      smoothCore L sigma gamma ell grade inputDimension outputDimension := by
  let target := smoothCore L sigma gamma ell grade inputDimension outputDimension
  have generators (outerCell innerCell : ℤ)
      (outerField : SmoothOperatorJet middleDimension outputDimension)
      (innerField : SmoothOperatorJet inputDimension middleDimension) :
      rawComposition admissible grade
          (weightedSingle L sigma gamma ell grade outerCell outerField)
          (weightedSingle L sigma gamma ell grade innerCell innerField) ∈ target := by
    rw [rawComposition_weightedSingle]
    exact Submodule.subset_span
      (Set.mem_range.mpr
        ⟨(outerCell + innerCell, smoothOperatorCompose outerField innerField), rfl⟩)
  refine Submodule.span_induction₂
    (p := fun outerValue innerValue _ _ =>
      rawComposition admissible grade outerValue innerValue ∈ target)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ outer.2 inner.2
  · intro outerGenerator innerGenerator outerMembership innerMembership
    rcases outerMembership with ⟨outerPair, rfl⟩
    rcases innerMembership with ⟨innerPair, rfl⟩
    exact generators outerPair.1 innerPair.1 outerPair.2 innerPair.2
  · intro innerValue _innerMembership
    rw [rawComposition_zero_outer]
    exact target.zero_mem
  · intro outerValue _outerMembership
    rw [rawComposition_zero_inner]
    exact target.zero_mem
  · intro outerFirst outerSecond innerValue _ _ _ firstMembership secondMembership
    rw [rawComposition_add_outer]
    exact target.add_mem firstMembership secondMembership
  · intro outerValue innerFirst innerSecond _ _ _ firstMembership secondMembership
    rw [rawComposition_add_inner]
    exact target.add_mem firstMembership secondMembership
  · intro scalar outerValue innerValue _ _ valueMembership
    rw [rawComposition_smul_outer]
    exact target.smul_mem scalar valueMembership
  · intro scalar outerValue innerValue _ _ valueMembership
    rw [rawComposition_smul_inner]
    exact target.smul_mem scalar valueMembership

theorem rawComposition_left_closure {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : Coefficient L sigma gamma ell grade middleDimension outputDimension)
    (inner : smoothCore L sigma gamma ell grade inputDimension middleDimension) :
    rawComposition admissible grade outer.1 inner.1 ∈
      (smoothCore L sigma gamma ell grade inputDimension outputDimension).topologicalClosure := by
  let source := smoothCore L sigma gamma ell grade middleDimension outputDimension
  let target := smoothCore L sigma gamma ell grade inputDimension outputDimension
  let left := rawCompositionLeft (outputDimension := outputDimension)
    admissible grade inner.1
  have sourceMapLe : source.map (left : _ →ₗ[ℂ] _) ≤ target := by
    intro output outputMembership
    rcases outputMembership with ⟨input, inputMembership, rfl⟩
    exact rawComposition_mem_smoothCore admissible grade
      ⟨input, inputMembership⟩ inner
  have sourceClosureMembership : outer.1 ∈ source.topologicalClosure := outer.2
  have mapClosureMembership : left outer.1 ∈ source.topologicalClosure.map
      (left : _ →ₗ[ℂ] _) := ⟨outer.1, sourceClosureMembership, rfl⟩
  exact (Submodule.topologicalClosure_mono sourceMapLe)
    ((source.topologicalClosure_map left) mapClosureMembership)

theorem rawComposition_closure {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : Coefficient L sigma gamma ell grade middleDimension outputDimension)
    (inner : Coefficient L sigma gamma ell grade inputDimension middleDimension) :
    rawComposition admissible grade outer.1 inner.1 ∈
      (smoothCore L sigma gamma ell grade inputDimension outputDimension).topologicalClosure := by
  let source := smoothCore L sigma gamma ell grade inputDimension middleDimension
  let target := smoothCore L sigma gamma ell grade inputDimension outputDimension
  let right := rawCompositionRight (inputDimension := inputDimension)
    admissible grade outer.1
  have sourceMapLe : source.map (right : _ →ₗ[ℂ] _) ≤ target.topologicalClosure := by
    intro output outputMembership
    rcases outputMembership with ⟨input, inputMembership, rfl⟩
    exact rawComposition_left_closure admissible grade outer
      ⟨input, inputMembership⟩
  have sourceClosureMembership : inner.1 ∈ source.topologicalClosure := inner.2
  have mapClosureMembership : right inner.1 ∈ source.topologicalClosure.map
      (right : _ →ₗ[ℂ] _) := ⟨inner.1, sourceClosureMembership, rfl⟩
  have inClosureOfTargetClosure : right inner.1 ∈ target.topologicalClosure.topologicalClosure :=
    (Submodule.topologicalClosure_mono sourceMapLe)
      ((source.topologicalClosure_map right) mapClosureMembership)
  have closureIdempotent : target.topologicalClosure.topologicalClosure =
      target.topologicalClosure :=
    target.isClosed_topologicalClosure.submodule_topologicalClosure_eq
  rw [closureIdempotent] at inClosureOfTargetClosure
  exact inClosureOfTargetClosure

def coefficientComposition {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : Coefficient L sigma gamma ell grade middleDimension outputDimension)
    (inner : Coefficient L sigma gamma ell grade inputDimension middleDimension) :
    Coefficient L sigma gamma ell grade inputDimension outputDimension :=
  ⟨rawComposition admissible grade outer.1 inner.1,
    rawComposition_closure admissible grade outer inner⟩

@[simp]
theorem coefficientComposition_coe {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : Coefficient L sigma gamma ell grade middleDimension outputDimension)
    (inner : Coefficient L sigma gamma ell grade inputDimension middleDimension) :
    (coefficientComposition admissible grade outer inner).1 =
      rawComposition admissible grade outer.1 inner.1 := rfl

end Grad.GaugeCoefficients.Algebra

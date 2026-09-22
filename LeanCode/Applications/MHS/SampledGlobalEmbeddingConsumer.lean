import SampledNormalizedCover

noncomputable section

open Set
open scoped ContDiff

namespace Grad.PhysicalFamily.SampledGlobalEmbedding.Consumer

open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalFamily.IntegerSampling
open Grad.PhysicalFamily.SampledSmoothFamily Grad.PhysicalFamily.SampledGlobalEmbedding
open Grad.PhysicalFamily.SampledConfigurationRegularity
open Grad.PhysicalFamily.SampledFullGeometry.Consumer
open Grad.MainAssembly.PhysicalNormalHessian

local instance : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩

theorem sampledRepresentative_position_continuous
    (cellLength : ℝ) (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (parameter : Icc family.lower family.upper) :
    Continuous (sampledRepresentativeFamily cellLength family period epsilonIn potential parameter).position := by
  let quotient : ClosedDisk × ℝ → Reference := fun argument => (argument.1, (argument.2 : CellCircle))
  have idOpen : IsOpenMap (id : ClosedDisk → ClosedDisk) := by
    intro set setOpen
    simpa using setOpen
  have quotientOpen : IsOpenMap quotient :=
    idOpen.prodMap QuotientAddGroup.isOpenMap_coe
  have quotientContinuous : Continuous quotient :=
    continuous_fst.prodMk ((AddCircle.continuous_mk' (2 * Real.pi)).comp continuous_snd)
  have quotientSurjective : Function.Surjective quotient := by
    intro point
    let representative := (AddCircle.equivIco (2 * Real.pi) 0 point.2).val
    refine ⟨(point.1, representative), ?_⟩
    apply Prod.ext
    · rfl
    · exact (AddCircle.equivIco (2 * Real.pi) 0).symm_apply_apply point.2
  apply (quotientOpen.isQuotientMap quotientContinuous quotientSurjective).continuous_iff.mpr
  let insertion : ClosedDisk × ℝ → ℝ × Vec := fun argument =>
    (parameter.val, coordinateDirection argument.1.val argument.2)
  have insertionContinuous : Continuous insertion := by
    apply continuous_const.prodMk
    have packingSmooth : ContDiff ℝ ∞ (fun argument : Plane × ℝ =>
        coordinateDirection argument.1 argument.2) := by
      rw [contDiff_piLp]
      intro coordinate
      fin_cases coordinate <;> simp [coordinateDirection, vector] <;> fun_prop
    exact packingSmooth.continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have insertionIn (argument : ClosedDisk × ℝ) :
      insertion argument ∈ sampledPhysicalCollar cellLength family := by
    refine ⟨parameter_mem_open cellLength family parameter, ?_⟩
    change planarPart (coordinateDirection argument.1.val argument.2) ∈ Metric.ball 0 family.collarRadius
    rw [planarPart_coordinateDirection]
    exact closed_disk_mem_collar cellLength family argument.1.val argument.1.property
  have composed := (sampledPositionJointLift_contDiffOn cellLength family period epsilonIn).continuousOn
    |>.comp_continuous insertionContinuous insertionIn
  have identity : sampledPositionJointLift cellLength family period ∘ insertion =
      (sampledRepresentativeFamily cellLength family period epsilonIn potential parameter).position ∘ quotient := by
    funext argument
    rw [Function.comp_apply, Function.comp_apply, sampledPositionJointLift_eq]
    simp [insertion, quotient, sampledRepresentativeFamily, sampledRepresentativeExtension,
      parameter_mem_open cellLength family parameter]
  rw [identity] at composed
  exact composed

theorem sampledRepresentative_position_isEmbedding_of_injective
    (cellLength : ℝ) (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (parameter : Icc family.lower family.upper)
    (injective : Function.Injective
      (sampledRepresentativeFamily cellLength family period epsilonIn potential parameter).position) :
    Topology.IsEmbedding
      (sampledRepresentativeFamily cellLength family period epsilonIn potential parameter).position := by
  have compactDisk : IsCompact {point : Plane | ‖point‖ ≤ 1} := by
    simpa [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : Plane) 1
  let : CompactSpace ClosedDisk := isCompact_iff_compactSpace.mp compactDisk
  exact ((sampledRepresentative_position_continuous cellLength family period epsilonIn potential parameter).isClosedEmbedding
    injective).isEmbedding

/-- The sampled physical position maps are actual topological embeddings,
uniformly for all parameters and all integers above one finite threshold. -/
theorem exists_sampledRepresentativeEmbeddingThreshold
    (cellLength : ℝ) (cellLengthPositive : 0 < cellLength) (family : CellSolutionFamily cellLength) :
    ∃ firstPeriod : ℕ, 1 ≤ firstPeriod ∧
      ∀ period : ℕ, firstPeriod ≤ period →
        sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero ∧
        ∀ (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
          (potential : ℝ) (parameter : Icc family.lower family.upper),
          Topology.IsEmbedding
            (sampledRepresentativeFamily cellLength family period epsilonIn potential parameter).position := by
  obtain ⟨firstPeriod, firstPositive, threshold⟩ :=
    exists_sampledRepresentativeInjectivityThreshold cellLength cellLengthPositive family
  refine ⟨firstPeriod, firstPositive, ?_⟩
  intro period periodAfter
  obtain ⟨epsilonIn, injective⟩ := threshold period periodAfter
  exact ⟨epsilonIn, fun epsilonProof potential parameter =>
    sampledRepresentative_position_isEmbedding_of_injective cellLength family period
      epsilonProof potential parameter (injective epsilonProof potential parameter)⟩

/-- Immediate main-target consumer: the exact existing representatives now
satisfy the complete smooth configuration predicate with no embedding premise. -/
theorem exists_sampledRepresentativeConfigurationThreshold
    (cellLength : ℝ) (cellLengthPositive : 0 < cellLength) (family : CellSolutionFamily cellLength) :
    ∃ firstPeriod : ℕ, 1 ≤ firstPeriod ∧
      ∀ period : ℕ, firstPeriod ≤ period →
        sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero ∧
        ∀ (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
          (potential : ℝ) (parameter : Icc family.lower family.upper),
          IsConfiguration .smooth
            (sampledRepresentativeFamily cellLength family period epsilonIn potential parameter) := by
  obtain ⟨embeddingPeriod, embeddingPositive, embeddingThreshold⟩ :=
    exists_sampledRepresentativeEmbeddingThreshold cellLength cellLengthPositive family
  obtain ⟨derivativePeriod, _, derivativeThreshold⟩ :=
    exists_sampledRepresentativeDerivativeThreshold cellLength cellLengthPositive family
  refine ⟨max embeddingPeriod derivativePeriod, embeddingPositive.trans (le_max_left _ _), ?_⟩
  intro period periodAfter
  obtain ⟨epsilonIn, embedding⟩ := embeddingThreshold period ((le_max_left _ _).trans periodAfter)
  refine ⟨epsilonIn, ?_⟩
  intro epsilonProof potential parameter
  exact sampledRepresentative_isConfiguration_of_embedding cellLength family period epsilonProof
    potential parameter (embedding epsilonProof potential parameter)
    (derivativeThreshold period ((le_max_right _ _).trans periodAfter) epsilonProof potential parameter)

end Grad.PhysicalFamily.SampledGlobalEmbedding.Consumer

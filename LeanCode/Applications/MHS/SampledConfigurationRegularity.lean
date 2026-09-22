import SampledSmoothFamily

noncomputable section

open Set
open scoped ContDiff

namespace Grad.PhysicalFamily.SampledConfigurationRegularity

open Grad.MainTarget
open Grad.PhysicalFamily
open Grad.PhysicalFamily.IntegerSampling
open Grad.PhysicalFamily.SampledSmoothFamily

private def fixedPhysicalCollar (family : CellSolutionFamily cellLength) :
    Set Vec := planarPart ⁻¹' Metric.ball 0 family.collarRadius

private theorem fixedPhysicalCollar_isOpen
    (family : CellSolutionFamily cellLength) :
    IsOpen (fixedPhysicalCollar family) :=
  Metric.isOpen_ball.preimage planarPart_contDiff.continuous

private theorem cylinder_subset_fixedPhysicalCollar
    (family : CellSolutionFamily cellLength) :
    cylinder ⊆ fixedPhysicalCollar family := by
  intro point pointIn
  change planarPart point ∈ Metric.ball 0 family.collarRadius
  rw [Metric.mem_ball, dist_zero_right]
  exact lt_of_le_of_lt pointIn family.collarLarge

def sampledMagneticCoordinateValue (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ) (parameter : ℝ)
    (point : Vec) : Vec :=
  sampledMagneticJointLift cellLength family period (parameter, point)

def sampledPressureCoordinateValue (potential : ℝ) (point : Vec) : ℝ :=
  sampledPressureLift potential (planarPart point) (point 2)

theorem sampledRepresentative_position_hasRegularity
    (cellLength : ℝ) (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (parameter : Set.Icc family.lower family.upper) :
    HasRegularity .smooth
      (sampledRepresentativeFamily cellLength family period epsilonIn potential
        parameter).position := by
  intro point pointIn
  let neighborhood := fixedPhysicalCollar family
  have pointNeighborhood : point ∈ neighborhood :=
    cylinder_subset_fixedPhysicalCollar family pointIn
  refine ⟨neighborhood, fixedPhysicalCollar_isOpen family, pointNeighborhood,
    (fun argument =>
      sampledPositionJointLift cellLength family period
        (parameter.val, argument)), ?_, ?_⟩
  · have insertionSmooth : ContDiff ℝ ∞
        (fun argument : Vec => (parameter.val, argument)) := by
      fun_prop
    exact (sampledPositionJointLift_contDiffOn cellLength family period
      epsilonIn).comp insertionSmooth.contDiffOn (by
        intro argument argumentIn
        exact ⟨parameter_mem_open cellLength family parameter, argumentIn⟩)
  · intro argument argumentIn
    change sampledPositionJointLift cellLength family period
        (parameter.val, argument) = periodicLift
      (sampledRepresentativeExtension cellLength family period epsilonIn
        potential parameter.val).position argument
    rw [sampledPositionJointLift_eq]
    symm
    exact periodicLift_sampledRepresentativeExtension_position cellLength family
      period epsilonIn potential parameter.val
        (parameter_mem_open cellLength family parameter) argument
        argumentIn.2

theorem sampledRepresentative_magnetic_hasRegularity
    (cellLength : ℝ) (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (parameter : Set.Icc family.lower family.upper) :
    HasRegularity .smooth
      (sampledRepresentativeFamily cellLength family period epsilonIn potential
        parameter).magnetic := by
  intro point pointIn
  let neighborhood := fixedPhysicalCollar family
  have pointNeighborhood : point ∈ neighborhood :=
    cylinder_subset_fixedPhysicalCollar family pointIn
  refine ⟨neighborhood, fixedPhysicalCollar_isOpen family, pointNeighborhood,
    sampledMagneticCoordinateValue cellLength family period parameter.val,
    ?_, ?_⟩
  · have insertionSmooth : ContDiff ℝ ∞
        (fun argument : Vec => (parameter.val, argument)) := by
      fun_prop
    exact (sampledMagneticJointLift_contDiffOn cellLength family period
      epsilonIn).comp insertionSmooth.contDiffOn (by
        intro argument argumentIn
        exact ⟨parameter_mem_open cellLength family parameter, argumentIn⟩)
  · intro argument argumentIn
    have collarIn :
        (parameter.val, argument) ∈ sampledPhysicalCollar cellLength family :=
      ⟨parameter_mem_open cellLength family parameter, argumentIn.1⟩
    change sampledMagneticJointLift cellLength family period
        (parameter.val, argument) = periodicLift
      (sampledRepresentativeExtension cellLength family period epsilonIn
        potential parameter.val).magnetic argument
    rw [sampledMagneticJointLift_eq cellLength family period epsilonIn
      (parameter.val, argument) collarIn]
    symm
    exact periodicLift_sampledRepresentativeExtension_magnetic cellLength family
      period epsilonIn potential parameter.val
        (parameter_mem_open cellLength family parameter) argument
        argumentIn.2

theorem sampledRepresentative_pressure_hasRegularity
    (cellLength : ℝ) (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (parameter : Set.Icc family.lower family.upper) :
    HasRegularity .smooth
      (sampledRepresentativeFamily cellLength family period epsilonIn potential
        parameter).pressure := by
  intro point pointIn
  let neighborhood := fixedPhysicalCollar family
  have pointNeighborhood : point ∈ neighborhood :=
    cylinder_subset_fixedPhysicalCollar family pointIn
  refine ⟨neighborhood, fixedPhysicalCollar_isOpen family, pointNeighborhood,
    sampledPressureCoordinateValue potential, ?_, ?_⟩
  · unfold sampledPressureCoordinateValue
    unfold sampledPressureLift
    exact (contDiff_const.sub
      ((contDiff_norm_sq ℝ).comp planarPart_contDiff)).contDiffOn
  · intro argument argumentIn
    change sampledPressureLift potential (planarPart argument) (argument 2) =
      periodicLift
        (sampledRepresentativeExtension cellLength family period epsilonIn
          potential parameter.val).pressure argument
    symm
    exact periodicLift_sampledRepresentativeExtension_pressure cellLength family
      period epsilonIn potential parameter.val
        (parameter_mem_open cellLength family parameter) argument
        argumentIn.2

/-- For the exact sampled representative, all three regularity clauses are
already automatic.  Smooth configuration validity is therefore reduced to
the genuine geometric embedding and differential-injectivity obligations. -/
theorem sampledRepresentative_isConfiguration_of_embedding
    (cellLength : ℝ) (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (parameter : Set.Icc family.lower family.upper)
    (embedding : Topology.IsEmbedding
      (sampledRepresentativeFamily cellLength family period epsilonIn potential
        parameter).position)
    (derivativeInjective : ∀ point ∈ cylinder,
      Function.Injective (fderivWithin ℝ
        (periodicLift
          (sampledRepresentativeFamily cellLength family period epsilonIn
            potential parameter).position)
        cylinder point)) :
    IsConfiguration .smooth
      (sampledRepresentativeFamily cellLength family period epsilonIn potential
        parameter) := by
  exact
    ⟨⟨sampledRepresentative_position_hasRegularity cellLength family period
        epsilonIn potential parameter, embedding, derivativeInjective⟩,
      sampledRepresentative_magnetic_hasRegularity cellLength family period
        epsilonIn potential parameter,
      sampledRepresentative_pressure_hasRegularity cellLength family period
        epsilonIn potential parameter⟩

end Grad.PhysicalFamily.SampledConfigurationRegularity

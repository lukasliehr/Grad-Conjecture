import AKDL4CanonicalAmbientExtension

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 3500
open Set
open scoped ContDiff

namespace Grad.PhysicalAmbient
open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalFamily.IntegerSampling
open Grad.PhysicalFamily.SampledSmoothFamily Grad.PhysicalFamily.SampledConfigurationRegularity
open Grad.MainAssembly.SampledAxisBasics

/-- The unchanged collar from the literal cell family. -/
def sampledAmbientCollar (family : CellSolutionFamily cellLength) : Set Vec :=
  planarPart ⁻¹' Metric.ball 0 family.collarRadius

theorem sampledAmbientCollar_isOpen (family : CellSolutionFamily cellLength) :
    IsOpen (sampledAmbientCollar family) :=
  Metric.isOpen_ball.preimage planarPart_contDiff.continuous

theorem sampledAmbientCollar_contains (family : CellSolutionFamily cellLength) :
    cylinder ⊆ sampledAmbientCollar family := by
  intro point pointIn
  change ‖planarPart point - 0‖ < family.collarRadius
  rw [sub_zero]
  exact pointIn.trans_lt family.collarLarge

theorem sampled_actual_lifts_smooth
    (cellLength : ℝ) (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (parameter : Icc family.lower family.upper) :
    ContDiffOn ℝ ∞ (sampledPositionCoordinateValue cellLength family period parameter.val)
      (sampledAmbientCollar family) ∧
    ContDiffOn ℝ ∞ (sampledMagneticCoordinateValue cellLength family period parameter.val)
      (sampledAmbientCollar family) ∧
    ContDiffOn ℝ ∞ (sampledPressureCoordinateValue potential) (sampledAmbientCollar family) := by
  have insertionSmooth : ContDiff ℝ ∞ (fun point : Vec => (parameter.val, point)) := by fun_prop
  have inclusion : MapsTo (fun point : Vec => (parameter.val, point))
      (sampledAmbientCollar family) (sampledPhysicalCollar cellLength family) := by
    intro point pointIn
    exact ⟨parameter_mem_open cellLength family parameter, pointIn⟩
  refine ⟨(sampledPositionJointLift_contDiffOn cellLength family period epsilonIn).comp
    insertionSmooth.contDiffOn inclusion,
    (sampledMagneticJointLift_contDiffOn cellLength family period epsilonIn).comp
    insertionSmooth.contDiffOn inclusion, ?_⟩
  unfold sampledPressureCoordinateValue sampledPressureLift
  exact (contDiff_const.sub ((contDiff_norm_sq ℝ).comp planarPart_contDiff)).contDiffOn

theorem sampled_actual_lifts_values
    (cellLength : ℝ) (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (parameter : Icc family.lower family.upper)
    (argument : ClosedDisk × ℝ) :
    let configuration := sampledRepresentativeFamily cellLength family period epsilonIn potential parameter
    sampledPositionCoordinateValue cellLength family period parameter.val (referenceCoverPoint argument) =
      configuration.position (referenceCover argument) ∧
    sampledMagneticCoordinateValue cellLength family period parameter.val (referenceCoverPoint argument) =
      configuration.magnetic (referenceCover argument) ∧
    sampledPressureCoordinateValue potential (referenceCoverPoint argument) =
      configuration.pressure (referenceCover argument) := by
  have pointIn := referenceCoverPoint_mem argument
  have position := periodicLift_sampledRepresentativeExtension_position cellLength family period epsilonIn
    potential parameter.val (parameter_mem_open cellLength family parameter) (referenceCoverPoint argument) pointIn
  have magnetic := periodicLift_sampledRepresentativeExtension_magnetic cellLength family period epsilonIn
    potential parameter.val (parameter_mem_open cellLength family parameter) (referenceCoverPoint argument) pointIn
  have pressure := periodicLift_sampledRepresentativeExtension_pressure cellLength family period epsilonIn
    potential parameter.val (parameter_mem_open cellLength family parameter) (referenceCoverPoint argument) pointIn
  simp only [periodicLift, dif_pos pointIn, referenceCover_quotientPoint] at position magnetic pressure
  refine ⟨?_, ?_, pressure.symm⟩
  · change sampledPositionJointLift cellLength family period (parameter.val, referenceCoverPoint argument) = _
    rw [sampledPositionJointLift_eq]
    exact position.symm
  · change sampledMagneticJointLift cellLength family period (parameter.val, referenceCoverPoint argument) = _
    have collarIn : (parameter.val, referenceCoverPoint argument) ∈ sampledPhysicalCollar cellLength family :=
      ⟨parameter_mem_open cellLength family parameter, sampledAmbientCollar_contains family pointIn⟩
    rw [sampledMagneticJointLift_eq cellLength family period epsilonIn
      (parameter.val, referenceCoverPoint argument) collarIn]
    exact magnetic.symm

end Grad.PhysicalAmbient

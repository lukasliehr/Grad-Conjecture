import AKAA27ActualFixedFirstGraph

noncomputable section

set_option maxHeartbeats 1700000

open MeasureTheory Set
open scoped BigOperators ContDiff Topology

namespace Grad.CartesianStartup

open Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.ActualAngularInverse Grad.Constraints

abbrev StartupFirst (dimension : ℕ) := GraphGrade dimension 1 0 openUnitDisk

def StartupCompatible {input output : ℕ} (coarse : StartupL2 input →L[ℂ] StartupL2 output)
    (fine : StartupFirst input →L[ℂ] StartupFirst output) : Prop :=
  ∀ field, base output 1 openUnitDisk (fun _ => 0) (fine field) =
    coarse (base input 1 openUnitDisk (fun _ => 0) field)

theorem startupCompatible_id (dimension : ℕ) :
    StartupCompatible (ContinuousLinearMap.id ℂ (StartupL2 dimension))
      (ContinuousLinearMap.id ℂ (StartupFirst dimension)) := fun _ => rfl

theorem startupCompatible_add {input output : ℕ}
    {first second : StartupL2 input →L[ℂ] StartupL2 output}
    {firstFine secondFine : StartupFirst input →L[ℂ] StartupFirst output}
    (firstSame : StartupCompatible first firstFine) (secondSame : StartupCompatible second secondFine) :
    StartupCompatible (first + second) (firstFine + secondFine) := by
  intro field
  change base output 1 openUnitDisk (fun _ => 0) (firstFine field + secondFine field) = _
  rw [map_add, firstSame, secondSame]
  rfl

theorem startupCompatible_sub {input output : ℕ}
    {first second : StartupL2 input →L[ℂ] StartupL2 output}
    {firstFine secondFine : StartupFirst input →L[ℂ] StartupFirst output}
    (firstSame : StartupCompatible first firstFine) (secondSame : StartupCompatible second secondFine) :
    StartupCompatible (first - second) (firstFine - secondFine) := by
  intro field
  change base output 1 openUnitDisk (fun _ => 0) (firstFine field - secondFine field) = _
  rw [map_sub, firstSame, secondSame]
  rfl

theorem startupCompatible_smul {input output : ℕ} (scalar : ℂ)
    {coarse : StartupL2 input →L[ℂ] StartupL2 output}
    {fine : StartupFirst input →L[ℂ] StartupFirst output}
    (same : StartupCompatible coarse fine) : StartupCompatible (scalar • coarse) (scalar • fine) := by
  intro field
  change base output 1 openUnitDisk (fun _ => 0) (scalar • fine field) = _
  rw [map_smul, same]
  rfl

theorem startupCompatible_comp {input middle output : ℕ}
    {first : StartupL2 middle →L[ℂ] StartupL2 output}
    {second : StartupL2 input →L[ℂ] StartupL2 middle}
    {firstFine : StartupFirst middle →L[ℂ] StartupFirst output}
    {secondFine : StartupFirst input →L[ℂ] StartupFirst middle}
    (firstSame : StartupCompatible first firstFine) (secondSame : StartupCompatible second secondFine) :
    StartupCompatible (first.comp second) (firstFine.comp secondFine) := by
  intro field
  change base output 1 openUnitDisk (fun _ => 0) (firstFine (secondFine field)) = _
  rw [firstSame, secondSame]
  rfl

def startupAngularFirstGraph (dimension : ℕ) (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight) :
    StartupFirst dimension →L[ℂ] StartupFirst dimension :=
  startupFixedFirstGraph (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) planeRotationEquiv
    (fun angle => by
      intro point
      change (‖planeRotationEquiv angle point‖ < 1 ↔ ‖point‖ < 1)
      rw [(planeRotationEquiv angle).norm_map])
    continuous_planeRotation_joint.measurable (startupAngularCoefficient dimension weight)
    (startupAngularCoefficient_continuous dimension weight smooth).measurable
    (startupAngularCoefficient_continuous dimension weight smooth).integrableOn_Icc

theorem startupAngularFirstGraph_compatible (dimension : ℕ) (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight) :
    StartupCompatible (startupAngularKernel dimension weight smooth) (startupAngularFirstGraph dimension weight smooth) :=
  startupFixedFirstGraph_base _ _ _ _ _ _ _

def startupPointFirstGraph {input output : ℕ} (mapping : OperatorValue input output)
    (orthogonal : Grad.PDEBootstrap.Spatial ≃ₗᵢ[ℝ] Grad.PDEBootstrap.Spatial) :
    StartupFirst input →L[ℂ] StartupFirst output :=
  startupFixedFirstGraph (Measure.dirac (0 : ℝ)) (fun _ => orthogonal)
    (fun _ => by
      intro point
      change (‖orthogonal point‖ < 1 ↔ ‖point‖ < 1)
      rw [orthogonal.norm_map])
    (orthogonal.continuous.comp continuous_snd).measurable
    (fun _ => mapping) measurable_const (integrable_const mapping)

theorem startupPointFirstGraph_compatible {input output : ℕ} (mapping : OperatorValue input output)
    (orthogonal : Grad.PDEBootstrap.Spatial ≃ₗᵢ[ℝ] Grad.PDEBootstrap.Spatial) :
    StartupCompatible (startupPointKernel mapping orthogonal) (startupPointFirstGraph mapping orthogonal) :=
  startupFixedFirstGraph_base _ _ _ _ _ _ _

def startupCharacterFirstGraph (dimension : ℕ) (mode : ℤ) :=
  startupAngularFirstGraph dimension (angularCharacter mode) (angularCharacter_smooth mode)

def startupPrimitiveFirstGraph (dimension : ℕ) (shift : ℤ) :=
  startupAngularFirstGraph dimension (shiftPrimitiveKernel shift) (shiftPrimitiveKernel_smooth shift)

def startupTrueAngularFirstGraph (dimension : ℕ) (shift : ℤ) :
    StartupFirst dimension →L[ℂ] StartupFirst dimension :=
  (startupPrimitiveFirstGraph dimension shift).comp
    (ContinuousLinearMap.id ℂ _ - startupCharacterFirstGraph dimension (-shift))

theorem startupCharacterFirstGraph_compatible (dimension : ℕ) (mode : ℤ) :
    StartupCompatible (startupCharacterKernel dimension mode) (startupCharacterFirstGraph dimension mode) :=
  startupAngularFirstGraph_compatible _ _ _

theorem startupTrueAngularFirstGraph_compatible (dimension : ℕ) (shift : ℤ) :
    StartupCompatible (startupTrueAngularInverse dimension shift) (startupTrueAngularFirstGraph dimension shift) :=
  startupCompatible_comp (startupAngularFirstGraph_compatible _ _ _)
    (startupCompatible_sub (startupCompatible_id dimension) (startupCharacterFirstGraph_compatible dimension (-shift)))

theorem startupMatrixFirstGraph_compatible {L sigma gamma ell : ℝ}
    (admissible : Grad.GaugeCoefficients.Envelope.Admissible L sigma gamma ell) {input output : ℕ}
    (family : Grad.GaugeCoefficients.Physical.Allocation.CoefficientFamily L sigma gamma ell input output)
    (coherent : Grad.GaugeCoefficients.Physical.Allocation.FamilyCoherent family) :
    StartupCompatible (originalMatrixKernel admissible family coherent) (startupMatrixFirstGraphCLM admissible family coherent) :=
  startupMatrixFirstGraph_base admissible family coherent

end Grad.CartesianStartup

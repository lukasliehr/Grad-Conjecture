import AKDT17TorusCoordinateCalculus

noncomputable section
open Set
open scoped ContDiff

namespace Grad.PhysicalGeometry
open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalAmbient
open Grad.PhysicalFamily.IntegerSampling Grad.PhysicalFamily.SampledSmoothFamily
open Grad.PhysicalFamily.SampledFullGeometry
open Grad.MainAssembly.SampledAxisBasics Grad.MainAssembly.PhysicalNormalHessian
open Grad.MainTarget.SemanticBridges

variable (length : ℝ) (family : CellSolutionFamily length) (period : ℕ)
  (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
  (potential : ℝ) (parameter : Icc family.lower family.upper)

def actualTorus (radius : Ioc (0 : ℝ) 1) : Torus → Vec :=
  (sampledRepresentativeFamily length family period epsilonIn potential parameter).position ∘ referenceTorus radius

theorem actualTorusLift_eq (radius : Ioc (0 : ℝ) 1) :
    torusLift (actualTorus length family period epsilonIn potential parameter radius) =
      actualPolarExtension length family period parameter ∘ torusCoordinateInsertion radius.val := by
  funext point
  symm
  rw [Function.comp_apply, actualPolarExtension_values length family period epsilonIn potential parameter _
    (torusCoordinateInsertion_mem radius point)]
  unfold foliationLift
  rw [dif_pos (torusCoordinateInsertion_mem radius point)]
  rfl

theorem actualTorusLift_smooth (radius : Ioc (0 : ℝ) 1) :
    ContDiff ℝ ∞ (torusLift (actualTorus length family period epsilonIn potential parameter radius)) := by
  rw [actualTorusLift_eq]
  apply contDiff_iff_contDiffAt.mpr
  intro point
  have outer := (actualPolarExtension_smooth length family period epsilonIn potential parameter).contDiffAt
    ((actualPolarDomain_open length family).mem_nhds
      (actualPolarDomain_contains length family (torusCoordinateInsertion_mem radius point)))
  exact outer.comp point (torusCoordinateInsertion_smooth radius.val).contDiffAt

include epsilonIn potential in
theorem actualPolarExtension_derivative_injective
    (injective : ∀ (point : Plane), ‖point‖ ≤ 1 → ∀ time : ℝ,
      Function.Injective (fderiv ℝ (sampledPositionCoordinateValue length family period parameter.val)
        (coordinateDirection point time))) (point : Vec) (membership : point ∈ foliationCylinder) :
    Function.Injective (fderiv ℝ (actualPolarExtension length family period parameter) point) := by
  rw [← localExtension_fderivWithin (regularity := .smooth) uniqueDiffOn_foliationCylinder membership
    (actualPolarDomain_open length family) (actualPolarDomain_contains length family membership)
    (actualPolarExtension_smooth length family period epsilonIn potential parameter)
    (fun argument membership => actualPolarExtension_values length family period epsilonIn potential parameter argument membership.2)
    (by simp [Regularity.order])]
  exact actualFoliation_derivative_injective length family period epsilonIn potential parameter injective point membership

theorem actualTorusLift_derivative_injective
    (injective : ∀ (point : Plane), ‖point‖ ≤ 1 → ∀ time : ℝ,
      Function.Injective (fderiv ℝ (sampledPositionCoordinateValue length family period parameter.val)
        (coordinateDirection point time))) (radius : Ioc (0 : ℝ) 1) (point : Plane) :
    Function.Injective (fderiv ℝ (torusLift (actualTorus length family period epsilonIn potential parameter radius)) point) := by
  rw [actualTorusLift_eq]
  have outer := ((actualPolarExtension_smooth length family period epsilonIn potential parameter).contDiffAt
    ((actualPolarDomain_open length family).mem_nhds
      (actualPolarDomain_contains length family (torusCoordinateInsertion_mem radius point)))).differentiableAt (by simp)
  rw [fderiv_comp point outer (torusCoordinateInsertion_hasFDerivAt radius.val point).differentiableAt,
    (torusCoordinateInsertion_hasFDerivAt radius.val point).fderiv]
  exact (actualPolarExtension_derivative_injective length family period epsilonIn potential parameter injective _
    (torusCoordinateInsertion_mem radius point)).comp torusDirectionCLM_injective

/-- The SAME actual pressure level at every radius 0<r≤1 is an embedded
smooth torus with a full-rank literal torus lift. -/
theorem actual_pressure_embedded_torus
    (valid : IsConfiguration .smooth (sampledRepresentativeFamily length family period epsilonIn potential parameter))
    (injective : ∀ (point : Plane), ‖point‖ ≤ 1 → ∀ time : ℝ,
      Function.Injective (fderiv ℝ (sampledPositionCoordinateValue length family period parameter.val)
        (coordinateDirection point time)))
    (pressure : Vec → ℝ)
    (same : ∀ argument,
      pressure ((sampledRepresentativeFamily length family period epsilonIn potential parameter).position argument) =
        (sampledRepresentativeFamily length family period epsilonIn potential parameter).pressure argument)
    (radius : Ioc (0 : ℝ) 1) :
    IsEmbeddedTorus (pressureLevel (range (sampledRepresentativeFamily length family period epsilonIn potential parameter).position)
      pressure (potential - radius.val ^ 2)) := by
  refine ⟨actualTorus length family period epsilonIn potential parameter radius,
    actualTorusLift_smooth length family period epsilonIn potential parameter radius,
    valid.1.2.1.comp (referenceTorus_isEmbedding radius),
    actual_pressure_level_range length family period epsilonIn potential parameter pressure same radius, ?_⟩
  exact actualTorusLift_derivative_injective length family period epsilonIn potential parameter injective radius

end Grad.PhysicalGeometry

import AKDT14ReferencePolarLifts

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

def actualFoliation : FoliationDomain → Vec :=
  (sampledRepresentativeFamily length family period epsilonIn potential parameter).position ∘ referenceFoliation

def actualPolarExtension : Vec → Vec :=
  sampledPositionCoordinateValue length family period parameter.val ∘ polarCylinderLift

def actualPolarDomain : Set Vec := polarCylinderLift ⁻¹' sampledAmbientCollar family

theorem actualPolarDomain_open : IsOpen (actualPolarDomain length family) :=
  (sampledAmbientCollar_isOpen family).preimage polarCylinderLift_smooth.continuous

theorem actualPolarDomain_contains : foliationCylinder ⊆ actualPolarDomain length family := by
  intro point membership
  exact sampledAmbientCollar_contains family (polarCylinderLift_mem point membership)

include epsilonIn potential in
theorem actualPolarExtension_smooth : ContDiffOn ℝ ∞ (actualPolarExtension length family period parameter) (actualPolarDomain length family) :=
  (sampled_actual_lifts_smooth length family period epsilonIn potential parameter).1.comp
    polarCylinderLift_smooth.contDiffOn (fun _ membership => membership)

theorem actualPolarExtension_values (point : Vec) (membership : point ∈ foliationCylinder) :
    actualPolarExtension length family period parameter point =
      foliationLift (actualFoliation length family period epsilonIn potential parameter) point := by
  have same := (sampled_actual_lifts_values length family period epsilonIn potential parameter (foliationCover point membership)).1
  rw [foliationCover_point, foliationCover_reference] at same
  unfold foliationLift
  rw [dif_pos membership]
  exact same

theorem actualFoliation_local_extensions :
    HasLocalExtensions .smooth (foliationLift (actualFoliation length family period epsilonIn potential parameter)) foliationCylinder := by
  intro point membership
  exact ⟨actualPolarDomain length family, actualPolarDomain_open length family, actualPolarDomain_contains length family membership,
    actualPolarExtension length family period parameter,
    actualPolarExtension_smooth length family period epsilonIn potential parameter,
    fun argument membership => actualPolarExtension_values length family period epsilonIn potential parameter argument membership.2⟩

/-- The actual foliation derivative is the full original position derivative
composed with the explicit nonsingular polar differential, including r=1. -/
theorem actualFoliation_fderivWithin (point : Vec) (membership : point ∈ foliationCylinder) :
    fderivWithin ℝ (foliationLift (actualFoliation length family period epsilonIn potential parameter)) foliationCylinder point =
      (fderiv ℝ (sampledPositionCoordinateValue length family period parameter.val) (polarCylinderLift point)).comp
        (fderiv ℝ polarCylinderLift point) := by
  rw [localExtension_fderivWithin (regularity := .smooth) uniqueDiffOn_foliationCylinder membership
    (actualPolarDomain_open length family) (actualPolarDomain_contains length family membership)
    (actualPolarExtension_smooth length family period epsilonIn potential parameter)
    (fun argument membership => actualPolarExtension_values length family period epsilonIn potential parameter argument membership.2)
    (by simp [Regularity.order])]
  exact fderiv_comp point
    (((sampled_actual_lifts_smooth length family period epsilonIn potential parameter).1.contDiffAt
      ((sampledAmbientCollar_isOpen family).mem_nhds (actualPolarDomain_contains length family membership))).differentiableAt (by simp))
    (polarCylinderLift_smooth.differentiable (by simp)).differentiableAt

theorem actualFoliation_derivative_injective
    (injective : ∀ (point : Plane), ‖point‖ ≤ 1 → ∀ time : ℝ,
      Function.Injective (fderiv ℝ (sampledPositionCoordinateValue length family period parameter.val)
        (coordinateDirection point time))) (point : Vec) (membership : point ∈ foliationCylinder) :
    Function.Injective (fderivWithin ℝ (foliationLift (actualFoliation length family period epsilonIn potential parameter)) foliationCylinder point) := by
  rw [actualFoliation_fderivWithin length family period epsilonIn potential parameter point membership]
  have polarSame : polarCylinderLift point = coordinateDirection (planarPart (polarCylinderLift point)) (point 2) := by
    ext coordinate
    fin_cases coordinate <;> simp [coordinateDirection, planarPart, polarCylinderLift, vector]
  have outer := injective (planarPart (polarCylinderLift point)) (polarCylinderLift_mem point membership) (point 2)
  rw [← polarSame] at outer
  exact outer.comp (polarCylinderLift_fderiv_injective point membership.1.ne')

end Grad.PhysicalGeometry

import AKDL6ActualAmbientFields

noncomputable section
open Set
open scoped ContDiff

namespace Grad.PhysicalAmbient
open Grad.MainTarget Grad.MainTarget.SemanticBridges
open Grad.MainAssembly.PhysicalNormalHessian

/-- Equality on the original closed reference cylinder determines every
ambient derivative there, including at the outer boundary. -/
theorem closedCylinder_iteratedFDeriv_eq
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (first second : Vec → Target) (domain : Set Vec) (domainOpen : IsOpen domain)
    (contains : cylinder ⊆ domain) (firstSmooth : ContDiffOn ℝ ∞ first domain)
    (secondSmooth : ContDiffOn ℝ ∞ second domain) (agrees : EqOn first second cylinder)
    (point : Vec) (pointIn : point ∈ cylinder) (order : ℕ) :
    iteratedFDeriv ℝ order first point = iteratedFDeriv ℝ order second point := by
  have firstWithin := iteratedFDerivWithin_eq_iteratedFDeriv uniqueDiffOn_cylinder
    ((firstSmooth.contDiffAt (domainOpen.mem_nhds (contains pointIn))).of_le (by norm_cast; exact le_top : (order : ℕ∞ω) ≤ ∞)) pointIn
  have secondWithin := iteratedFDerivWithin_eq_iteratedFDeriv uniqueDiffOn_cylinder
    ((secondSmooth.contDiffAt (domainOpen.mem_nhds (contains pointIn))).of_le (by norm_cast; exact le_top : (order : ℕ∞ω) ≤ ∞)) pointIn
  rw [← firstWithin, ← secondWithin]
  exact iteratedFDerivWithin_congr agrees pointIn order

/-- The same closed-cylinder equality yields the actual ambient chain rule
for reconstructed magnetic or pressure fields. -/
theorem reconstructedField_fderiv
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (position : Reference → Vec) (field : Reference → Target)
    (positionLift : Vec → Vec) (fieldLift : Vec → Target) (ambient : Vec → Target)
    (domain : Set Vec) (domainOpen : IsOpen domain) (contains : cylinder ⊆ domain)
    (positionSmooth : ContDiffOn ℝ ∞ positionLift domain)
    (fieldSmooth : ContDiffOn ℝ ∞ fieldLift domain) (ambientSmooth : ContDiff ℝ ∞ ambient)
    (positionSame : ∀ argument : ClosedDisk × ℝ,
      positionLift (referenceCoverPoint argument) = position (referenceCover argument))
    (fieldSame : ∀ argument : ClosedDisk × ℝ,
      fieldLift (referenceCoverPoint argument) = field (referenceCover argument))
    (ambientSame : ∀ point, ambient (position point) = field point)
    (point : Vec) (pointIn : point ∈ cylinder) :
    (fderiv ℝ ambient (positionLift point)).comp (fderiv ℝ positionLift point) =
      fderiv ℝ fieldLift point := by
  have agrees : EqOn (ambient ∘ positionLift) fieldLift cylinder := by
    intro argument argumentIn
    let lift : ClosedDisk × ℝ := (⟨planarPart argument, argumentIn⟩, argument 2)
    have liftSame : referenceCoverPoint lift = argument := by
      ext coordinate
      fin_cases coordinate <;> simp [referenceCoverPoint, lift, coordinateDirection, planarPart, vector]
    rw [← liftSame, Function.comp_apply, positionSame, fieldSame, ambientSame]
  have positionDiff := (positionSmooth.contDiffAt (domainOpen.mem_nhds (contains pointIn))).differentiableAt (by simp)
  have fieldDiff := (fieldSmooth.contDiffAt (domainOpen.mem_nhds (contains pointIn))).differentiableAt (by simp)
  have ambientDiff := (ambientSmooth.differentiable (by simp)).differentiableAt (x := positionLift point)
  have equality : fderivWithin ℝ (ambient ∘ positionLift) cylinder point =
      fderivWithin ℝ fieldLift cylinder point := fderivWithin_congr' agrees pointIn
  rw [fderivWithin_eq_fderiv (uniqueDiffOn_cylinder point pointIn) (ambientDiff.comp point positionDiff),
    fderivWithin_eq_fderiv (uniqueDiffOn_cylinder point pointIn) fieldDiff,
    fderiv_comp point ambientDiff positionDiff] at equality
  exact equality

end Grad.PhysicalAmbient

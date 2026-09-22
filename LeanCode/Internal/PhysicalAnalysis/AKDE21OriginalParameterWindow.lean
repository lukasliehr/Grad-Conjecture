import AKDE20ActualZeroLimitFields

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set
open scoped ContDiff
namespace Grad.OriginalCellFamily
open Grad.CartesianState Grad.ClosedJets Grad.Constraints Grad.PhysicalFamily Grad.MainTarget
open Grad.NashMoser.OriginalIteration Grad.NashMoser.OriginalLimit

variable {parameters : PhaseParameters} {reference : Seed.Parameters}
    {inside : reference ∈ Seed.parameterDomain} {base loss : ℕ} {cellLength : ℝ}
    {neighborhood : OriginalNewtonNeighborhood parameters reference inside base}
    {inverse : OriginalNewtonInverse neighborhood cellLength loss}

def cellFiniteParameter (rho alpha delta epsilon parameter : ℝ) : OriginalFiniteParameter :=
  (![rho,alpha,delta,parameter],epsilon)

theorem cellFiniteParameter_smooth (rho alpha delta : ℝ) :
    ContDiff ℝ ∞ (fun point : ℝ × ℝ => cellFiniteParameter rho alpha delta point.1 point.2) := by
  have seed : ContDiff ℝ ∞ (fun point : ℝ × ℝ => (![rho,alpha,delta,point.2] : Seed.Parameters)) := by
    apply contDiff_pi.mpr
    intro coordinate
    fin_cases coordinate <;> simp <;> fun_prop
  exact seed.prodMk contDiff_fst

/-- A geometric rectangle inside the SAME open Newton parameter patch.
It carries no fields, equations, derivative or inverse hypotheses. -/
structure ConstructedParameterWindow (scale : OriginalNewtonScale inverse) where
  rho : ℝ
  alpha : ℝ
  delta : ℝ
  lower : ℝ
  upper : ℝ
  parameterLower : ℝ
  parameterUpper : ℝ
  radius : ℝ
  rhoPositive : 0 < rho
  rhoSmall : rho < 1/4
  deltaNonzero : delta ≠ 0
  alphaNonresonant : ∀ multiple : ℤ, alpha ≠ (Real.pi/2)*(multiple:ℝ)
  lowerPositive : 0 < lower
  intervalNontrivial : lower < upper
  upperSmall : upper < 1/2
  parameterContains : parameterLower < lower ∧ upper < parameterUpper
  positive : 0 < radius
  included : ∀ epsilon ∈ Ioo (-radius) radius, ∀ parameter ∈ Ioo parameterLower parameterUpper,
    cellFiniteParameter rho alpha delta epsilon parameter ∈ scale.openParameterDomain

variable (scale : OriginalNewtonScale inverse) (window : ConstructedParameterWindow scale)

namespace ConstructedParameterWindow

def v (epsilon parameter : ℝ) := constructedCellVector scale (cellFiniteParameter window.rho window.alpha window.delta epsilon parameter)
def w (epsilon parameter : ℝ) := constructedCellPotential scale (cellFiniteParameter window.rho window.alpha window.delta epsilon parameter)
def remainder (epsilon parameter : ℝ) := constructedCellRemainder scale (cellFiniteParameter window.rho window.alpha window.delta epsilon parameter)
def tilt (epsilon parameter : ℝ) := constructedTilt scale (cellFiniteParameter window.rho window.alpha window.delta epsilon parameter)

theorem parameter_mem {parameter : ℝ} (member : parameter ∈ Icc window.lower window.upper) :
    parameter ∈ Ioo window.parameterLower window.parameterUpper :=
  ⟨window.parameterContains.1.trans_le member.1,member.2.trans_lt window.parameterContains.2⟩

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem cell_pullback_smooth (field : OriginalFiniteParameter × (SpatialPlane × ℝ) → Y)
    (smooth : ContDiffOn ℝ ∞ field (constructedCellDomain scale)) :
    ContDiffOn ℝ ∞ (fun point : CellArgument => field
      (cellFiniteParameter window.rho window.alpha window.delta point.1 point.2.1,
        (coordinateDisk point.2.2,point.2.2 1)))
      (Ioo (-window.radius) window.radius ×ˢ
        (Ioo window.parameterLower window.parameterUpper ×ˢ coordinateCollar (4/3))) := by
  have seed := (cellFiniteParameter_smooth window.rho window.alpha window.delta).comp
    (show ContDiff ℝ ∞ (fun point : CellArgument => (point.1,point.2.1)) by fun_prop)
  have spatial : ContDiff ℝ ∞ (fun point : CellArgument => (coordinateDisk point.2.2,point.2.2 1)) :=
    (physicalCoordinateDiskCLM.contDiff.comp (contDiff_snd.comp contDiff_snd)).prodMk
    (by fun_prop)
  exact smooth.comp (seed.prodMk spatial).contDiffOn (fun point member =>
    ⟨window.included point.1 member.1 point.2.1 member.2.1,member.2.2,mem_univ _⟩)

theorem circle_pullback_smooth (field : OriginalFiniteParameter × ℝ → Y)
    (smooth : ContDiffOn ℝ ∞ field (scale.openParameterDomain ×ˢ Set.univ)) :
    ContDiffOn ℝ ∞ (fun point : CircleArgument => field
      (cellFiniteParameter window.rho window.alpha window.delta point.1 point.2.1,point.2.2))
      (Ioo (-window.radius) window.radius ×ˢ
        (Ioo window.parameterLower window.parameterUpper ×ˢ Set.univ)) := by
  have seed := (cellFiniteParameter_smooth window.rho window.alpha window.delta).comp
    (show ContDiff ℝ ∞ (fun point : CircleArgument => (point.1,point.2.1)) by fun_prop)
  exact smooth.comp (seed.prodMk (contDiff_snd.comp contDiff_snd)).contDiffOn
    (fun point member => ⟨window.included point.1 member.1 point.2.1 member.2.1,mem_univ _⟩)

theorem fields_smooth (leftLaw : inverse.LeftLaw) :
    ContDiffOn ℝ ∞ (uncurriedCell (window.v scale))
      (Ioo (-window.radius) window.radius ×ˢ (Ioo window.parameterLower window.parameterUpper ×ˢ coordinateCollar (4/3))) ∧
    ContDiffOn ℝ ∞ (uncurriedCell (window.w scale))
      (Ioo (-window.radius) window.radius ×ˢ (Ioo window.parameterLower window.parameterUpper ×ˢ coordinateCollar (4/3))) ∧
    ContDiffOn ℝ ∞ (uncurriedCell (window.remainder scale))
      (Ioo (-window.radius) window.radius ×ˢ (Ioo window.parameterLower window.parameterUpper ×ˢ coordinateCollar (4/3))) ∧
    ContDiffOn ℝ ∞ (uncurriedCircle (window.tilt scale))
      (Ioo (-window.radius) window.radius ×ˢ (Ioo window.parameterLower window.parameterUpper ×ˢ Set.univ)) :=
  ⟨window.cell_pullback_smooth scale _ (constructedCellVector_joint_smooth scale leftLaw),
    window.cell_pullback_smooth scale _ (constructedCellPotential_joint_smooth scale leftLaw),
    window.cell_pullback_smooth scale _ (constructedCellRemainder_joint_smooth scale leftLaw),
    window.circle_pullback_smooth scale _ (constructedTilt_joint_smooth scale leftLaw)⟩

end ConstructedParameterWindow
end Grad.OriginalCellFamily

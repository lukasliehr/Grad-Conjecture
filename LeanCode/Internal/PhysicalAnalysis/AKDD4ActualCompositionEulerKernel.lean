import AKDD3RectangularEulerLeibniz

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.AnnularRadialSmoothness

attribute [local irreducible] fullKernelComposition fullKernelAdd fullKernelSmul polynomialKernelAction

def operatorCompositionBilinear (source middle target : ℕ) :
    (CellL2 middle →L[ℂ] CellL2 target) →L[ℝ]
      (CellL2 source →L[ℂ] CellL2 middle) →L[ℝ] (CellL2 source →L[ℂ] CellL2 target) :=
  (ContinuousLinearMap.compL ℂ (CellL2 source) (CellL2 middle) (CellL2 target)).bilinearRestrictScalars ℝ

/-- Literal full-kernel convolution in every allocated ordered term. -/
def compositionEulerKernel {parameters : PhaseParameters} {source middle target : ℕ}
    (radius : RadialPoint) (outer : ℕ → RadialKernel parameters radius middle target)
    (inner : ℕ → RadialKernel parameters radius source middle) (terms : List (ℕ × ℕ)) :
    RadialKernel parameters radius source target :=
  List.rec (fullKernelSmul 0 (fullKernelComposition (outer 0) (inner 0)))
    (fun term _ previous => fullKernelAdd (fullKernelComposition (outer term.1) (inner term.2)) previous) terms

theorem compositionEulerKernel_zero {parameters : PhaseParameters} {source middle target : ℕ}
    (radius : RadialPoint) (outer : ℕ → RadialKernel parameters radius middle target)
    (inner : ℕ → RadialKernel parameters radius source middle) :
    compositionEulerKernel radius outer inner (eulerLeibnizTerms 0) = fullKernelComposition (outer 0) (inner 0) := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift input
  change (fullKernelAdd (fullKernelComposition (outer 0) (inner 0))
    (fullKernelSmul (0 : ℂ) (fullKernelComposition (outer 0) (inner 0)))).entry shift input = _
  rw [fullKernelAdd_entry,fullKernelSmul_entry]
  ext value coordinate
  change (fullKernelComposition (outer 0) (inner 0)).entry shift input value coordinate+
    (0 : ℂ)*(fullKernelComposition (outer 0) (inner 0)).entry shift input value coordinate = _
  ring

theorem compositionEulerKernel_collar_action {source middle target : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (outer : ℕ → (radius : RadialPoint) → RadialKernel parameters radius middle target)
    (inner : ℕ → (radius : RadialPoint) → RadialKernel parameters radius source middle)
    (terms : List (ℕ × ℕ)) (point : ℝ) :
    radialPolynomialAction parameters lower positive bounded
      (fun radius => compositionEulerKernel radius (fun rank => outer rank radius) (fun rank => inner rank radius) terms) 0 point =
      bilinearEulerPolynomial (operatorCompositionBilinear source middle target)
        (fun rank => radialPolynomialAction parameters lower positive bounded (outer rank) 0)
        (fun rank => radialPolynomialAction parameters lower positive bounded (inner rank) 0) terms point := by
  induction terms with
  | nil =>
      change polynomialKernelAction (radialKernelParameters parameters (collarRadius lower positive bounded point)) 0
        (fullKernelSmul (0 : ℂ) (fullKernelComposition
          (outer 0 (collarRadius lower positive bounded point)) (inner 0 (collarRadius lower positive bounded point)))) = 0
      rw [polynomialKernelAction_smul,zero_smul ℂ]
  | cons term terms previous =>
      change polynomialKernelAction (radialKernelParameters parameters (collarRadius lower positive bounded point)) 0 (fullKernelAdd
        (fullKernelComposition (outer term.1 (collarRadius lower positive bounded point))
          (inner term.2 (collarRadius lower positive bounded point)))
        (compositionEulerKernel (collarRadius lower positive bounded point)
          (fun rank => outer rank (collarRadius lower positive bounded point))
          (fun rank => inner rank (collarRadius lower positive bounded point)) terms)) = _
      rw [polynomialKernelAction_add,polynomialKernelAction_comp]
      change _ + radialPolynomialAction parameters lower positive bounded
        (fun radius => compositionEulerKernel radius (fun rank => outer rank radius) (fun rank => inner rank radius) terms) 0 point = _
      rw [previous]
      rfl

/-- Genuine rectangular composition closure of actual Euler operators,
proved before observing entries or estimating any norms. -/
theorem KernelEulerDerivativeTower.comp {source middle target : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (outer : ℕ → (radius : RadialPoint) → RadialKernel parameters radius middle target)
    (inner : ℕ → (radius : RadialPoint) → RadialKernel parameters radius source middle)
    (outerDerivative : KernelEulerDerivativeTower parameters lower positive bounded outer)
    (innerDerivative : KernelEulerDerivativeTower parameters lower positive bounded inner) :
    KernelEulerDerivativeTower parameters lower positive bounded
      (fun rank radius => compositionEulerKernel radius (fun raw => outer raw radius) (fun raw => inner raw radius) (eulerLeibnizTerms rank)) := by
  intro rank radius inside
  have result := bilinearEulerPolynomial_hasDerivWithinAt (operatorCompositionBilinear source middle target) (Icc lower 1)
    (fun order => radialPolynomialAction parameters lower positive bounded (outer order) 0)
    (fun order => radialPolynomialAction parameters lower positive bounded (inner order) 0) radius
    (fun order => outerDerivative order radius inside) (fun order => innerDerivative order radius inside) (eulerLeibnizTerms rank)
  rw [← compositionEulerKernel_collar_action parameters lower positive bounded outer inner (eulerLeibnizStep (eulerLeibnizTerms rank)) radius] at result
  apply result.congr_of_eventuallyEq
  · exact Filter.Eventually.of_forall (compositionEulerKernel_collar_action parameters lower positive bounded outer inner (eulerLeibnizTerms rank))
  · exact compositionEulerKernel_collar_action parameters lower positive bounded outer inner (eulerLeibnizTerms rank) radius

end Grad.OriginalCartesianTameEstimate

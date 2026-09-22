import AJH4SamePolynomialInverse
import AJH7ActualMatrixSeriesSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter
open scoped BigOperators ENNReal Topology ContDiff
namespace Grad.AnnularRadialSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction

variable {source middle target : ℕ} (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)

/-- Literal same physical kernel on the closed collar, in polynomial cell
coordinates used solely to prove smooth-core membership. -/
def radialPolynomialAction (kernel : (radius : RadialPoint) → RadialKernel parameters radius source target)
    (power : ℕ) (radius : ℝ) : CellL2 source →L[ℂ] CellL2 target :=
  polynomialKernelAction (radialKernelParameters parameters (collarRadius lower positive bounded radius)) power
    (kernel (collarRadius lower positive bounded radius))

def SmoothPolynomialFamily (kernel : (radius : RadialPoint) → RadialKernel parameters radius source target) : Prop :=
  ∀ power, ContDiffOn ℝ ∞ (radialPolynomialAction parameters lower positive bounded kernel power) (Icc lower 1)

theorem smoothPolynomialFamily_fixed
    (family : (p : PhaseParameters) → FullTwoFrequencyKernel p source target)
    (same : ∀ first second, SameKernelEntries (family first) (family second)) :
    SmoothPolynomialFamily parameters lower positive bounded (fun radius => family (radialKernelParameters parameters radius)) := by
  intro power
  have smooth : ContDiffOn ℝ ∞ (fun _ : ℝ => polynomialKernelAction parameters power (family parameters)) (Icc lower 1) := contDiffOn_const
  apply smooth.congr
  intro radius _
  exact polynomialKernelAction_congr _ parameters power _ _ (same _ _)

variable {parameters lower positive bounded}

theorem SmoothPolynomialFamily.add
    {first second : (radius : RadialPoint) → RadialKernel parameters radius source target}
    (one : SmoothPolynomialFamily parameters lower positive bounded first)
    (two : SmoothPolynomialFamily parameters lower positive bounded second) :
    SmoothPolynomialFamily parameters lower positive bounded (fun radius => fullKernelAdd (first radius) (second radius)) := by
  intro power
  apply ((one power).add (two power)).congr
  intro radius _
  exact polynomialKernelAction_add _ power _ _

theorem SmoothPolynomialFamily.neg
    {kernel : (radius : RadialPoint) → RadialKernel parameters radius source target}
    (smooth : SmoothPolynomialFamily parameters lower positive bounded kernel) :
    SmoothPolynomialFamily parameters lower positive bounded (fun radius => fullKernelNeg (kernel radius)) := by
  intro power
  apply (smooth power).neg.congr
  intro radius _
  exact polynomialKernelAction_neg _ power _

theorem SmoothPolynomialFamily.sub
    {first second : (radius : RadialPoint) → RadialKernel parameters radius source target}
    (one : SmoothPolynomialFamily parameters lower positive bounded first)
    (two : SmoothPolynomialFamily parameters lower positive bounded second) :
    SmoothPolynomialFamily parameters lower positive bounded (fun radius => fullKernelSub (first radius) (second radius)) :=
  SmoothPolynomialFamily.add one (SmoothPolynomialFamily.neg two)

theorem SmoothPolynomialFamily.comp
    {outer : (radius : RadialPoint) → RadialKernel parameters radius middle target}
    {inner : (radius : RadialPoint) → RadialKernel parameters radius source middle}
    (one : SmoothPolynomialFamily parameters lower positive bounded outer)
    (two : SmoothPolynomialFamily parameters lower positive bounded inner) :
    SmoothPolynomialFamily parameters lower positive bounded (fun radius => fullKernelComposition (outer radius) (inner radius)) := by
  intro power
  have smooth : ContDiffOn ℝ ∞ (fun radius =>
      (radialPolynomialAction parameters lower positive bounded outer power radius).comp
      (radialPolynomialAction parameters lower positive bounded inner power radius)) (Icc lower 1) :=
    ((ContinuousLinearMap.compL ℂ (CellL2 source) (CellL2 middle) (CellL2 target)).bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff.comp₂_contDiffOn (one power) (two power)
  apply smooth.congr
  intro radius _
  exact polynomialKernelAction_comp _ power _ _

variable (parameters lower positive bounded)

theorem smoothPolynomialFamily_identity (dimension : ℕ) :
    SmoothPolynomialFamily (source := dimension) (target := dimension) parameters lower positive bounded
      (fun radius => fullIdentityKernel (radialKernelParameters parameters radius) dimension) := by
  intro power
  have smooth : ContDiffOn ℝ ∞ (fun _ : ℝ => ContinuousLinearMap.id ℂ (CellL2 dimension)) (Icc lower 1) := contDiffOn_const
  apply smooth.congr
  intro radius _
  exact polynomialKernelAction_identity _ power dimension

variable {parameters lower positive bounded}

/-- The SAME original inverse is smooth in radius in every polynomial grade.
Only its existing zero-moment smallness is used for invertibility. -/
theorem SmoothPolynomialFamily.negativeInverse {dimension : ℕ}
    {kernel : (radius : RadialPoint) → RadialKernel parameters radius dimension dimension}
    (smooth : SmoothPolynomialFamily parameters lower positive bounded kernel)
    (low : ℝ) (lowSmall : low < 1)
    (small : ∀ radius, fullKernelMoment (radialKernelParameters parameters radius) 0 (kernel radius) ≤ low) :
    SmoothPolynomialFamily parameters lower positive bounded (fun radius =>
      fullKernelNegativeIdentityInverse (radialKernelParameters parameters radius) (kernel radius) low (small radius) lowSmall) := by
  have forwardSmooth := SmoothPolynomialFamily.sub smooth (smoothPolynomialFamily_identity parameters lower positive bounded dimension)
  intro power
  apply sameEndomorphismInverse_contDiffOn (Icc lower 1)
    (radialPolynomialAction parameters lower positive bounded
      (fun radius => fullKernelNegativeIdentityPerturbation (radialKernelParameters parameters radius) (kernel radius)) power)
  · intro radius _
    exact (polynomialKernelAction_inverse _ power _ low (small _) lowSmall).1
  · intro radius _
    exact (polynomialKernelAction_inverse _ power _ low (small _) lowSmall).2
  · exact forwardSmooth power

end Grad.AnnularRadialSmoothness

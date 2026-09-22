import AIC11LiteralZeroExtension
import ANR8WeakDistribution

noncomputable section
open MeasureTheory Classical
open scoped ContDiff

namespace Grad.InteriorLocalization
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.CircularHighWeak Grad.CircularHighRegularity Grad.WeightedJets

/-- Full-plane weak Laplacian, with all auxiliary cells and arbitrary compact tests. -/
def HasGlobalWeakLaplacian (field laplacian : FieldL2 1 Set.univ) : Prop :=
  ∀ (cell : ℤ) (vector : PhysicalValue 1) (test : Spatial → ℝ),
    ContDiff ℝ ∞ test → HasCompactSupport test →
      (∫ point in (Set.univ : Set Spatial), test point • inner ℂ vector (laplacian point cell)) =
        ∫ point in (Set.univ : Set Spatial), testLaplacian test point • inner ℂ vector (field point cell)

/-- The actual L2 cutoff Laplacian of the constructed AN18 weak inverse. -/
def actualInteriorLaplacian (parameter : ℝ) (source : highDiskL2) : FieldL2 1 Set.univ :=
  diskZeroExtension (localizedDiskLaplacian (highRobinWeakInverse parameter source).val
    (weakLaplacianValue parameter source))

/-- No distributional equation or second-derivative premise is assumed:
the equation is obtained from the actual constructed Robin inverse. -/
theorem actualInteriorLaplacian_weak (parameter : ℝ) (source : highDiskL2) :
    HasGlobalWeakLaplacian
      (base 1 1 Set.univ (fun _ => 0) (localizedWeakInverse parameter source))
      (actualInteriorLaplacian parameter source) := by
  intro cell vector test smooth compact
  have localEquation := localizedDiskLaplacian_weak
    (highRobinWeakInverse parameter source).val (weakLaplacianValue parameter source)
    (weakInverse_distribution parameter source) vector test smooth compact
  have globalSource := diskZeroExtension_integral
    (localizedDiskLaplacian (highRobinWeakInverse parameter source).val
      (weakLaplacianValue parameter source)) cell vector test
  have globalField := diskZeroExtension_integral
    (diskScalar interiorCutoff.toFun interiorCutoff.smooth
      (highDiskBulk (highRobinWeakInverse parameter source))) cell vector (testLaplacian test)
  have sameBase := congrArg (fun field : FieldL2 1 Set.univ =>
    ∫ point in (Set.univ : Set Spatial), testLaplacian test point • inner ℂ vector (field point cell))
    (localizedWeakInverse_base_zeroExtension parameter source)
  exact globalSource.trans ((congrArg (fun value : ℂ => if cell = 0 then value else 0) localEquation).trans
    (globalField.symm.trans sameBase.symm))

end Grad.InteriorLocalization

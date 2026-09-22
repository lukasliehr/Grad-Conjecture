import AIC13InteriorBounds

noncomputable section
open MeasureTheory

namespace Grad.InteriorLocalization
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.CircularHighWeak Grad.WeightedJets

/-- Immediate actual inverse consumer: a genuine global H1 cutoff field,
its proved L2 distributional Laplacian and k-polynomial bound, and equality
to the original weak solution on the fixed inner disk. This is the input to
interior Fourier regularity; no H2 conclusion is folded into the premise. -/
theorem actualInteriorPDE_consumer (parameter : ℝ) (source : highDiskL2) :
    ‖localizedWeakInverse parameter source‖ ≤ (2 * diskInteriorConstant) * ‖source‖ ∧
    HasGlobalWeakLaplacian
      (base 1 1 Set.univ (fun _ => 0) (localizedWeakInverse parameter source))
      (actualInteriorLaplacian parameter source) ∧
    ‖actualInteriorLaplacian parameter source‖ ≤ interiorLaplacianConstant * (1 + parameter ^ 2) * ‖source‖ ∧
    (∀ᵐ point ∂volume.restrict (Metric.ball (0 : Spatial) (1 / 2)),
      base 1 1 Set.univ (fun _ => 0) (localizedWeakInverse parameter source) point 0 =
        highDiskBulk (highRobinWeakInverse parameter source) point) :=
  ⟨localizedWeakInverse_bound parameter source, actualInteriorLaplacian_weak parameter source,
    actualInteriorLaplacian_bound parameter source, localizedWeakInverse_inner_disk parameter source⟩

end Grad.InteriorLocalization

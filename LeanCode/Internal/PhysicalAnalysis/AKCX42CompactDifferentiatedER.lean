import AKCX41SameLocalizedEquationGraphs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.WeightedJets.ZeroExtension Grad.WeightedJets.Ordered

/-- Internal carrier for an actual compact native equation at one completed spatial grade. -/
structure StartupCompactSpatialEquation (order : ℕ) (support : Set Spatial) where
  field : GraphGrade 3 order 0 openUnitDisk
  zeroth : GraphGrade 3 order 0 openUnitDisk
  tensor : Fin 2 → Fin 2 → GraphGrade 3 order 0 openUnitDisk
  flux : Fin 2 → GraphGrade 3 order 0 openUnitDisk
  fieldSupported : SupportedField (CellValues 3) openUnitDisk support (base 3 order openUnitDisk (fun _ => 0) field)
  zeroSupported : SupportedField (CellValues 3) openUnitDisk support (base 3 order openUnitDisk (fun _ => 0) zeroth)
  tensorSupported : ∀ outer inner, SupportedField (CellValues 3) openUnitDisk support
    (base 3 order openUnitDisk (fun _ => 0) (tensor outer inner))
  fluxSupported : ∀ direction, SupportedField (CellValues 3) openUnitDisk support
    (base 3 order openUnitDisk (fun _ => 0) (flux direction))
  equation : StartupWeakDivDivEquation (base 3 order openUnitDisk (fun _ => 0) field)
    (base 3 order openUnitDisk (fun _ => 0) zeroth)
    (fun outer inner => base 3 order openUnitDisk (fun _ => 0) (tensor outer inner))
    (fun direction => base 3 order openUnitDisk (fun _ => 0) (flux direction))

namespace StartupCompactSpatialEquation
variable {order rank : ℕ} {support : Set Spatial} (data : StartupCompactSpatialEquation order support)

theorem differentiated_weak (bound : rank ≤ order) (word : Fin rank → Fin 2) :
    StartupWeakDivDivEquation
      (orderedDerivative 3 order rank openUnitDisk (fun _ => 0) bound data.field word)
      (orderedDerivative 3 order rank openUnitDisk (fun _ => 0) bound data.zeroth word)
      (fun outer inner => orderedDerivative 3 order rank openUnitDisk (fun _ => 0) bound (data.tensor outer inner) word)
      (fun direction => orderedDerivative 3 order rank openUnitDisk (fun _ => 0) bound (data.flux direction) word) :=
  startupSame_ordered_weakDivDiv data.field data.zeroth data.tensor data.flux data.equation bound word

/-- The SAME differentiated compact equation, with its actual tensor and phase/cutoff remainders. -/
theorem differentiated_distribution (closed : IsClosed support) (localizer : TestLocalizer openUnitDisk support)
    (bound : rank ≤ order) (word : Fin rank → Fin 2) :
    Laplacian.laplacian (distributionEmbedding (startupPlaneExtension
      (orderedDerivative 3 order rank openUnitDisk (fun _ => 0) bound data.field word))) =
      (∑ outer : Fin 2, ∑ inner : Fin 2, distributionDerivative outer (distributionDerivative inner
        (distributionEmbedding (startupPlaneExtension
          (orderedDerivative 3 order rank openUnitDisk (fun _ => 0) bound (data.tensor outer inner) word)))))+
      distributionEmbedding (startupPlaneExtension
        (orderedDerivative 3 order rank openUnitDisk (fun _ => 0) bound data.zeroth word))-
      ∑ direction : Fin 2, distributionDerivative direction (distributionEmbedding (startupPlaneExtension
        (orderedDerivative 3 order rank openUnitDisk (fun _ => 0) bound (data.flux direction) word))) :=
  startupCompact_divDiv_distribution localizer _ _ _ _
    (startupOrderedDerivative_supported closed data.field data.fieldSupported bound word)
    (startupOrderedDerivative_supported closed data.zeroth data.zeroSupported bound word)
    (fun outer inner => startupOrderedDerivative_supported closed (data.tensor outer inner) (data.tensorSupported outer inner) bound word)
    (fun direction => startupOrderedDerivative_supported closed (data.flux direction) (data.fluxSupported direction) bound word)
    (data.differentiated_weak bound word)

end StartupCompactSpatialEquation
end Grad.CartesianStartup

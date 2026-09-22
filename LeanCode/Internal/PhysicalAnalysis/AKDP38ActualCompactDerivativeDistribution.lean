import AKDP37ActualBesselDerivativeGains
import AKCX42CompactDifferentiatedER

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.WeightedJets.ZeroExtension Grad.WeightedJets.Ordered
open Grad.RepresentedKernel.SpatialProduct

/-- A stored ordered derivative has the actual next weak derivative,
with the same graph and the same word prefix. -/
theorem startupOrderedDerivative_snoc_pairing {order rank weight : ℕ}
    (field : GraphGrade 3 order weight openUnitDisk) (bound : rank+1≤order)
    (word : Fin rank → Fin 2) (direction : Fin 2)
    (cell : ℤ) (vector : PhysicalValue 3) (test : TestFunction openUnitDisk) :
    startupTestPairing cell vector test
      (orderedDerivative 3 order (rank+1) openUnitDisk (fun _ => weight) bound field (Fin.snoc word direction)) =
      -startupTestPairing cell vector (startupDerivativeTest direction test)
        (orderedDerivative 3 order rank openUnitDisk (fun _ => weight) (by omega) field word) := by
  rw [startupOrderedDerivative_pairing,startupOrderedDerivative_pairing]
  have testSame : startupListDerivativeTest (List.ofFn (Fin.snoc word direction)) test =
      startupListDerivativeTest (List.ofFn word) (startupDerivativeTest direction test) := by
    rw [List.ofFn_succ']
    simp [startupListDerivativeTest,List.foldr_append]
  rw [testSame,pow_succ]
  ring

/-- Compact support permits the exact first derivative identity against
all Schwartz tests, without imposing a boundary derivative hypothesis. -/
theorem startupCompact_first_distribution {support : Set Spatial}
    (localizer : TestLocalizer openUnitDisk support) (field derivative : StartupL2 3)
    (fieldSupported : SupportedField (CellValues 3) openUnitDisk support field)
    (derivativeSupported : SupportedField (CellValues 3) openUnitDisk support derivative)
    (direction : Fin 2)
    (weak : ∀ cell vector test,startupTestPairing cell vector test derivative =
      -startupTestPairing cell vector (startupDerivativeTest direction test) field) :
    distributionEmbedding (startupPlaneExtension derivative) =
      distributionDerivative direction (distributionEmbedding (startupPlaneExtension field)) := by
  apply startupTempered_eq_of_real
  intro test
  apply lp.ext
  funext cell
  apply ext_inner_left ℂ
  intro vector
  rw [startupPlaneExtension_realSchwartz,startupPlaneExtension_first_realSchwartz]
  have identity := weak cell vector (startupLocalizeSmoothTest localizer test test.smooth')
  rw [startupSupportedPairing_localize localizer test test.smooth' derivative derivativeSupported,
    startupSupportedPairing_localize_first localizer test test.smooth' field fieldSupported] at identity
  exact identity

/-- Actual ordered compact derivatives commute with the same zero
extension used by the elliptic equation and the Bessel remainder. -/
theorem startupOrderedExtension_snoc_distribution {order rank weight : ℕ} {support : Set Spatial}
    (closed : IsClosed support) (localizer : TestLocalizer openUnitDisk support)
    (field : GraphGrade 3 order weight openUnitDisk)
    (supported : SupportedField (CellValues 3) openUnitDisk support
      (base 3 order openUnitDisk (fun _ => weight) field))
    (bound : rank+1≤order) (word : Fin rank → Fin 2) (direction : Fin 2) :
    distributionEmbedding (startupPlaneExtension
      (orderedDerivative 3 order (rank+1) openUnitDisk (fun _ => weight) bound field (Fin.snoc word direction))) =
      distributionDerivative direction (distributionEmbedding (startupPlaneExtension
        (orderedDerivative 3 order rank openUnitDisk (fun _ => weight) (by omega) field word))) :=
  startupCompact_first_distribution localizer _ _
    (startupOrderedDerivative_supported closed field supported (by omega) word)
    (startupOrderedDerivative_supported closed field supported bound (Fin.snoc word direction)) direction
    (startupOrderedDerivative_snoc_pairing field bound word direction)

end Grad.CartesianStartup

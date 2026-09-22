import AKDP38ActualCompactDerivativeDistribution

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets Grad.TensorBootstrap
open Grad.WeightedJets.ZeroExtension Grad.WeightedJets.Ordered

/-- Two actual stored spatial derivatives pass into the bounded second
Bessel operator after the genuine compact extension. -/
theorem startupOrderedExtension_two_distribution {order rank weight : ℕ} {support : Set Spatial}
    (closed : IsClosed support) (localizer : TestLocalizer openUnitDisk support)
    (field : GraphGrade 3 order weight openUnitDisk)
    (supported : SupportedField (CellValues 3) openUnitDisk support
      (base 3 order openUnitDisk (fun _ => weight) field))
    (bound : rank+2≤order) (word : Fin rank → Fin 2) (first second : Fin 2) :
    distributionEmbedding (startupPlaneExtension
      (orderedDerivative 3 order (rank+2) openUnitDisk (fun _ => weight) bound field
        (Fin.snoc (Fin.snoc word first) second))) =
      distributionDerivative second (distributionDerivative first (distributionEmbedding (startupPlaneExtension
        (orderedDerivative 3 order rank openUnitDisk (fun _ => weight) (by omega) field word)))) := by
  rw [startupOrderedExtension_snoc_distribution closed localizer field supported bound,
    startupOrderedExtension_snoc_distribution closed localizer field supported (by omega)]

/-- The literal compact-equation Bessel remainder at rank r+2 is paid
by rank r of the value/zeroth and rank r+1 of the flux. The flux sign is
the one in the actual compact weak equation. -/
theorem startupCompactBessel_lowerOrders {order rank : ℕ} {support : Set Spatial}
    (data : StartupCompactSpatialEquation order support)
    (closed : IsClosed support) (localizer : TestLocalizer openUnitDisk support)
    (bound : rank+2≤order) (word : Fin rank → Fin 2) (first second : Fin 2) :
    ‖valueInclusion (startupDivDivRemainder
      (startupPlaneExtension (orderedDerivative 3 order (rank+2) openUnitDisk (fun _ => 0) bound data.field
        (Fin.snoc (Fin.snoc word first) second)))
      (startupPlaneExtension (orderedDerivative 3 order (rank+2) openUnitDisk (fun _ => 0) bound data.zeroth
        (Fin.snoc (Fin.snoc word first) second)))
      (fun direction => -startupPlaneExtension (orderedDerivative 3 order (rank+2) openUnitDisk (fun _ => 0) bound
        (data.flux direction) (Fin.snoc (Fin.snoc word first) second))))‖ ≤
      ‖orderedDerivative 3 order rank openUnitDisk (fun _ => 0) (by omega) data.field word‖+
      ‖orderedDerivative 3 order rank openUnitDisk (fun _ => 0) (by omega) data.zeroth word‖+
      ∑ direction : Fin 2,‖orderedDerivative 3 order (rank+1) openUnitDisk (fun _ => 0) (by omega)
        (data.flux direction) (Fin.snoc word first)‖ := by
  rw [startupDivDivRemainder_value]
  rw [startupResolvent_actualSecond (second,first) _ _
    (startupOrderedExtension_two_distribution closed localizer data.field data.fieldSupported bound word first second)]
  rw [startupResolvent_actualSecond (second,first) _ _
    (startupOrderedExtension_two_distribution closed localizer data.zeroth data.zeroSupported bound word first second)]
  simp_rw [map_neg]
  have fluxSame (direction : Fin 2) :
      l2ResolventDerivative direction
        (startupPlaneExtension (orderedDerivative 3 order (rank+2) openUnitDisk (fun _ => 0) bound
          (data.flux direction) (Fin.snoc (Fin.snoc word first) second))) =
        startupSecondL2 (direction,second)
          (startupPlaneExtension (orderedDerivative 3 order (rank+1) openUnitDisk (fun _ => 0) (by omega)
            (data.flux direction) (Fin.snoc word first))) :=
    startupFluxResolvent_actualFirst direction second _ _
      (startupOrderedExtension_snoc_distribution closed localizer (data.flux direction)
        (data.fluxSupported direction) bound (Fin.snoc word first) second)
  simp_rw [fluxSame]
  apply (norm_sub_le _ _).trans
  apply (add_le_add (norm_sub_le _ _) (norm_sum_le _ _)).trans
  apply add_le_add
  · apply add_le_add
    · simpa only [startupPlaneExtension_norm] using startupSecondL2_norm (second,first)
        (startupPlaneExtension (orderedDerivative 3 order rank openUnitDisk (fun _ => 0) (by omega) data.field word))
    · simpa only [startupPlaneExtension_norm] using startupSecondL2_norm (second,first)
        (startupPlaneExtension (orderedDerivative 3 order rank openUnitDisk (fun _ => 0) (by omega) data.zeroth word))
  · apply Finset.sum_le_sum
    intro direction _
    simpa only [norm_neg,startupPlaneExtension_norm] using startupSecondL2_norm (direction,second)
      (startupPlaneExtension (orderedDerivative 3 order (rank+1) openUnitDisk (fun _ => 0) (by omega)
        (data.flux direction) (Fin.snoc word first)))

end Grad.CartesianStartup

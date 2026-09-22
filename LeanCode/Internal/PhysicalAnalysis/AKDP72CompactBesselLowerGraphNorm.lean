import AKDP39ActualCompactBesselLowerOrders
import AKDP67FiniteAdjustableGraphFormula

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets Grad.TensorBootstrap
open Grad.WeightedJets.Ordered Grad.WeightedJets.ZeroExtension

theorem startupSameOrdered_lowerGraph_norm {dimension order lowerOrder rank weight : ℕ}
    (graph : GraphGrade dimension order weight openUnitDisk) (lower : GraphGrade dimension lowerOrder 0 openUnitDisk)
    (same : base dimension order openUnitDisk (fun _ => weight) graph=base dimension lowerOrder openUnitDisk (fun _ => 0) lower)
    (bound : rank≤order) (lowerBound : rank≤lowerOrder) (word : Fin rank → Fin 2) :
    ‖orderedDerivative dimension order rank openUnitDisk (fun _ => weight) bound graph word‖≤
      Real.sqrt (rank.factorial : ℝ)*‖lower‖ := by
  rw [startupOrderedDerivative_sameBase graph bound lower lowerBound same]
  exact (PiLp.norm_apply_le _ word).trans (orderedDerivative_norm_le dimension lowerOrder rank openUnitDisk (fun _ => 0) lowerBound lower)

def startupCompactBesselRemainder {order : ℕ} {support : Set Spatial}
    (data : StartupCompactSpatialEquation order support) : StartupOrderedL2 order :=
  startupOrderedValue order (WithLp.toLp 2 (fun word => startupDivDivRemainder
    (startupPlaneExtension (orderedDerivative 3 order order openUnitDisk (fun _ => 0) le_rfl data.field word))
    (startupPlaneExtension (orderedDerivative 3 order order openUnitDisk (fun _ => 0) le_rfl data.zeroth word))
    (fun direction => -startupPlaneExtension (orderedDerivative 3 order order openUnitDisk (fun _ => 0) le_rfl (data.flux direction) word))))

/-- Every coordinate of the actual Bessel remainder uses only rank r of
value/zeroth graphs and rank r+1 of flux graphs. -/
theorem startupCompactBesselRemainder_word_bound {rank : ℕ} {support : Set Spatial}
    (data : StartupCompactSpatialEquation (rank+2) support) (closed : IsClosed support)
    (localizer : TestLocalizer openUnitDisk support)
    (field zeroth : GraphGrade 3 rank 0 openUnitDisk) (flux : Fin 2 → GraphGrade 3 (rank+1) 0 openUnitDisk)
    (fieldSame : base 3 (rank+2) openUnitDisk (fun _ => 0) data.field=base 3 rank openUnitDisk (fun _ => 0) field)
    (zeroSame : base 3 (rank+2) openUnitDisk (fun _ => 0) data.zeroth=base 3 rank openUnitDisk (fun _ => 0) zeroth)
    (fluxSame : ∀ direction,base 3 (rank+2) openUnitDisk (fun _ => 0) (data.flux direction)=
      base 3 (rank+1) openUnitDisk (fun _ => 0) (flux direction)) (word : Fin (rank+2) → Fin 2) :
    ‖startupCompactBesselRemainder data word‖≤
      Real.sqrt (rank.factorial : ℝ)*(‖field‖+‖zeroth‖)+
      Real.sqrt ((rank+1).factorial : ℝ)*(∑ direction,‖flux direction‖) := by
  let wordPrefix : Fin rank → Fin 2 := Fin.init (Fin.init word)
  let first := Fin.init word (Fin.last rank)
  let second := word (Fin.last (rank+1))
  have wordSame : Fin.snoc (Fin.snoc wordPrefix first) second=word := by
    dsimp only [wordPrefix,first,second]
    rw [Fin.snoc_init_self,Fin.snoc_init_self]
  have bounded := startupCompactBessel_lowerOrders data closed localizer le_rfl wordPrefix first second
  rw [wordSame] at bounded
  change ‖startupCompactBesselRemainder data word‖≤_ at bounded
  have fieldBound := startupSameOrdered_lowerGraph_norm data.field field fieldSame (by omega : rank≤rank+2) le_rfl wordPrefix
  have zeroBound := startupSameOrdered_lowerGraph_norm data.zeroth zeroth zeroSame (by omega : rank≤rank+2) le_rfl wordPrefix
  have fluxBound := Finset.sum_le_sum (fun direction (_ : direction∈Finset.univ) =>
    startupSameOrdered_lowerGraph_norm (data.flux direction) (flux direction) (fluxSame direction)
      (by omega : rank+1≤rank+2) le_rfl (Fin.snoc wordPrefix first))
  apply (bounded.trans (add_le_add (add_le_add fieldBound zeroBound) fluxBound)).trans_eq
  rw [←Finset.mul_sum]
  ring

theorem startupCompactBesselRemainder_lowerGraph_bound {rank : ℕ} {support : Set Spatial}
    (data : StartupCompactSpatialEquation (rank+2) support) (closed : IsClosed support)
    (localizer : TestLocalizer openUnitDisk support)
    (field zeroth : GraphGrade 3 rank 0 openUnitDisk) (flux : Fin 2 → GraphGrade 3 (rank+1) 0 openUnitDisk)
    (fieldSame : base 3 (rank+2) openUnitDisk (fun _ => 0) data.field=base 3 rank openUnitDisk (fun _ => 0) field)
    (zeroSame : base 3 (rank+2) openUnitDisk (fun _ => 0) data.zeroth=base 3 rank openUnitDisk (fun _ => 0) zeroth)
    (fluxSame : ∀ direction,base 3 (rank+2) openUnitDisk (fun _ => 0) (data.flux direction)=
      base 3 (rank+1) openUnitDisk (fun _ => 0) (flux direction)) :
    ‖startupCompactBesselRemainder data‖≤(Fintype.card (Fin (rank+2) → Fin 2) : ℝ)*
      (Real.sqrt (rank.factorial : ℝ)*(‖field‖+‖zeroth‖)+
        Real.sqrt ((rank+1).factorial : ℝ)*(∑ direction,‖flux direction‖)) := by
  have finite := startupFiniteHilbert_norm_le_sum (fun word => startupCompactBesselRemainder data word)
  change ‖startupCompactBesselRemainder data‖≤_ at finite
  exact (finite.trans (Finset.sum_le_sum (fun word _ =>
    startupCompactBesselRemainder_word_bound data closed localizer field zeroth flux fieldSame zeroSame fluxSame word))).trans_eq
    (by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul])

end Grad.CartesianStartup

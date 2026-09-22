import AKDP72CompactBesselLowerGraphNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets Grad.WeightedJets.ZeroExtension

/-- Uniform lower graph estimates bound the SAME compact Bessel
remainder before either principal or endpoint absorption. -/
theorem startupCompactBesselRemainder_adjustable {State : Type*} (rank : ℕ) {support : Set Spatial}
    (closed : IsClosed support) (localizer : TestLocalizer openUnitDisk support)
    (data : State → StartupCompactSpatialEquation (rank+2) support)
    (high low : State → ℝ) (highNonnegative : ∀ state,0≤high state)
    (fieldEstimate : StartupAdjustableSpatialGraph rank
      (fun state => base 3 (rank+2) openUnitDisk (fun _ => 0) (data state).field) high low)
    (zeroEstimate : StartupAdjustableSpatialGraph rank
      (fun state => base 3 (rank+2) openUnitDisk (fun _ => 0) (data state).zeroth) high low)
    (fluxEstimate : ∀ direction,StartupAdjustableSpatialGraph (rank+1)
      (fun state => base 3 (rank+2) openUnitDisk (fun _ => 0) ((data state).flux direction)) high low)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ constant : ℝ,0≤constant ∧ ∀ state,‖startupCompactBesselRemainder (data state)‖≤epsilon*high state+constant*low state := by
  let count : ℝ := Fintype.card (Fin (rank+2) → Fin 2)
  let first : ℝ := Real.sqrt (rank.factorial : ℝ)
  let second : ℝ := Real.sqrt ((rank+1).factorial : ℝ)
  have countNonnegative : 0≤count := Nat.cast_nonneg _
  have firstNonnegative : 0≤first := Real.sqrt_nonneg _
  have secondNonnegative : 0≤second := Real.sqrt_nonneg _
  let delta := epsilon/(count*(2*first+2*second)+1)
  have deltaPositive : 0<delta := div_pos positive (by positivity)
  obtain ⟨fieldConstant,fieldNonnegative,fieldBound⟩ := fieldEstimate delta deltaPositive
  obtain ⟨zeroConstant,zeroNonnegative,zeroBound⟩ := zeroEstimate delta deltaPositive
  choose fluxConstant fluxNonnegative fluxBound using fun direction => fluxEstimate direction delta deltaPositive
  refine ⟨count*(first*(fieldConstant+zeroConstant)+second*(∑ direction,fluxConstant direction)),
    mul_nonneg countNonnegative (add_nonneg (mul_nonneg firstNonnegative (add_nonneg fieldNonnegative zeroNonnegative))
      (mul_nonneg secondNonnegative (Finset.sum_nonneg (fun direction _ => fluxNonnegative direction)))),?_⟩
  intro state
  obtain ⟨field,fieldSame,fieldPaid⟩ := fieldBound state
  obtain ⟨zeroth,zeroSame,zeroPaid⟩ := zeroBound state
  choose flux fluxSame fluxPaid using fun direction => fluxBound direction state
  have original := startupCompactBesselRemainder_lowerGraph_bound (data state) closed localizer field zeroth flux
    fieldSame.symm zeroSame.symm (fun direction => (fluxSame direction).symm)
  have fluxSum := Finset.sum_le_sum (fun direction (_ : direction∈Finset.univ) => fluxPaid direction)
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Finset.sum_mul] at fluxSum
  norm_num only [Fintype.card_fin,Nat.cast_ofNat] at fluxSum
  have parts := add_le_add (mul_le_mul_of_nonneg_left (add_le_add fieldPaid zeroPaid) firstNonnegative)
    (mul_le_mul_of_nonneg_left fluxSum secondNonnegative)
  have paid := original.trans (mul_le_mul_of_nonneg_left parts countNonnegative)
  have allocated : count*(2*first+2*second)*delta≤epsilon := by
    have exactDelta : delta*(count*(2*first+2*second)+1)=epsilon := div_mul_cancel₀ epsilon (by positivity)
    nlinarith [deltaPositive]
  have main := mul_le_mul_of_nonneg_right allocated (highNonnegative state)
  nlinarith only [paid,main]

end Grad.CartesianStartup

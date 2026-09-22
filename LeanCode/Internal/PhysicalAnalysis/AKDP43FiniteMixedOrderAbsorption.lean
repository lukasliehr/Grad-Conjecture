import AKDP40ActualMixedOrderInputNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap
open Grad.OriginalCartesianTameEstimate Grad.GaugeCoefficients.Physical.RadialLedger

theorem startupOriginalMixedOrder_zero {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (core : ACore parameters dimension) :
    originalMixedOrderNorm parameters grade 0 core=originalCellNorm parameters grade core := by
  have rowSame (cell : ℤ) : apMassRow 1 0 (phaseWeightedJet parameters cell (core.val cell))=
      apMassRow (cellFrequency cell) 0 (phaseWeightedJet parameters cell (core.val cell)) := by
    apply PiLp.ext
    intro index
    change (1 : ℂ)^(0-_) • _=(cellFrequency cell : ℂ)^(0-_) • _
    simp only [Nat.zero_sub,pow_zero,one_smul]
  simp only [originalMixedOrderNorm,originalCellNorm,Nat.sub_zero,rowSame]

/-- A finite collection of actual strict mixed orders is adjustable in
the pure planar endpoint, with one fixed pure-cell remainder. -/
theorem startupFiniteMixedOrders_adjustable {Index : Type*} [Fintype Index]
    (grade : ℕ) (order : Index → ℕ) (strict : ∀ index,order index<grade)
    (weight : Index → ℝ) (nonnegative : ∀ index,0≤weight index)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ constant : ℝ,0≤constant ∧ ∀ (dimension : ℕ) (parameters : PhaseParameters) (core : ACore parameters dimension),
      (∑ index,weight index*originalMixedOrderNorm parameters grade (order index) core)≤
        epsilon*originalPlanarNorm parameters grade core+constant*originalCellNorm parameters grade core := by
  classical
  let total : ℝ := ∑ index,weight index
  have totalNonnegative : 0≤total := Finset.sum_nonneg (fun index _ => nonnegative index)
  let delta := epsilon/(total+1)
  have deltaPositive : 0<delta := div_pos positive (by positivity)
  have individual (index : Index) : ∃ constant : ℝ,0≤constant ∧
      ∀ (dimension : ℕ) (parameters : PhaseParameters) (core : ACore parameters dimension),
        originalMixedOrderNorm parameters grade (order index) core≤
          delta*originalPlanarNorm parameters grade core+constant*originalCellNorm parameters grade core := by
    by_cases zero : order index=0
    · refine ⟨1,zero_le_one,?_⟩
      intro dimension parameters core
      rw [zero,startupOriginalMixedOrder_zero,one_mul]
      exact le_add_of_nonneg_left (mul_nonneg deltaPositive.le (Real.sqrt_nonneg _))
    · exact originalMixedOrder_adjustable grade (order index) (Nat.pos_of_ne_zero zero) (strict index) delta deltaPositive
  choose remainder remainderNonnegative remainderBound using individual
  refine ⟨∑ index,weight index*remainder index,
    Finset.sum_nonneg (fun index _ => mul_nonneg (nonnegative index) (remainderNonnegative index)),?_⟩
  intro dimension parameters core
  have allocated : total*delta≤epsilon := by
    have exactTotal : delta*(total+1)=epsilon := div_mul_cancel₀ epsilon (by positivity : total+1≠0)
    nlinarith [deltaPositive]
  calc
    _ ≤ ∑ index,weight index*(delta*originalPlanarNorm parameters grade core+
        remainder index*originalCellNorm parameters grade core) :=
      Finset.sum_le_sum (fun index _ => mul_le_mul_of_nonneg_left
        (remainderBound index dimension parameters core) (nonnegative index))
    _ = (total*delta)*originalPlanarNorm parameters grade core+
        (∑ index,weight index*remainder index)*originalCellNorm parameters grade core := by
      simp only [mul_add,Finset.sum_add_distrib,← mul_assoc,← Finset.sum_mul,total]
    _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_right allocated (Real.sqrt_nonneg _)) _

end Grad.CartesianStartup

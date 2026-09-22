import AKDP66OriginalLowerGraphAbsorption

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets

/-- Uniform adjustable bounds for a finite formula of actual lower
spatial graphs. The graph always represents the stated L2 field. -/
def StartupAdjustableSpatialGraph {State : Type*} (order : ℕ) (field : State → StartupL2 3)
    (high low : State → ℝ) : Prop :=
  ∀ epsilon : ℝ,0<epsilon → ∃ constant : ℝ,0≤constant ∧ ∀ state : State,
    ∃ graph : GraphGrade 3 order 0 openUnitDisk,
      base 3 order openUnitDisk (fun _ => 0) graph=field state ∧
      ‖graph‖≤epsilon*high state+constant*low state

namespace StartupAdjustableSpatialGraph
variable {State : Type*} {order : ℕ} {field other : State → StartupL2 3} {high low : State → ℝ}

theorem sameGraph (estimate : StartupAdjustableSpatialGraph order field high low)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ constant : ℝ,0≤constant ∧ ∀ state (graph : GraphGrade 3 order 0 openUnitDisk),
      base 3 order openUnitDisk (fun _ => 0) graph=field state →
      ‖graph‖≤epsilon*high state+constant*low state := by
  obtain ⟨constant,nonnegative,bounded⟩ := estimate epsilon positive
  refine ⟨constant,nonnegative,?_⟩
  intro state graph same
  obtain ⟨actual,actualSame,actualBound⟩ := bounded state
  have identical : graph=actual := base_injective 3 order openUnitDisk openUnitDisk_isOpen (fun _ => 0)
    (same.trans actualSame.symm)
  simpa only [identical] using actualBound

theorem congr (estimate : StartupAdjustableSpatialGraph order field high low)
    (same : ∀ state,field state=other state) : StartupAdjustableSpatialGraph order other high low := by
  intro epsilon positive
  obtain ⟨constant,nonnegative,bounded⟩ := estimate epsilon positive
  exact ⟨constant,nonnegative,fun state => by simpa only [←same state] using bounded state⟩

theorem add (first : StartupAdjustableSpatialGraph order field high low)
    (second : StartupAdjustableSpatialGraph order other high low) :
    StartupAdjustableSpatialGraph order (fun state => field state+other state) high low := by
  intro epsilon positive
  obtain ⟨one,oneNonnegative,oneBound⟩ := first (epsilon/2) (by positivity)
  obtain ⟨two,twoNonnegative,twoBound⟩ := second (epsilon/2) (by positivity)
  refine ⟨one+two,add_nonneg oneNonnegative twoNonnegative,?_⟩
  intro state
  obtain ⟨firstGraph,firstSame,firstBound⟩ := oneBound state
  obtain ⟨secondGraph,secondSame,secondBound⟩ := twoBound state
  refine ⟨firstGraph+secondGraph,by rw [map_add,firstSame,secondSame],?_⟩
  exact ((norm_add_le _ _).trans (add_le_add firstBound secondBound)).trans_eq (by ring)

theorem neg (estimate : StartupAdjustableSpatialGraph order field high low) :
    StartupAdjustableSpatialGraph order (fun state => -field state) high low := by
  intro epsilon positive
  obtain ⟨constant,nonnegative,bounded⟩ := estimate epsilon positive
  refine ⟨constant,nonnegative,?_⟩
  intro state
  obtain ⟨graph,same,bound⟩ := bounded state
  exact ⟨-graph,by rw [map_neg,same],by simpa only [norm_neg] using bound⟩

theorem sub (first : StartupAdjustableSpatialGraph order field high low)
    (second : StartupAdjustableSpatialGraph order other high low) :
    StartupAdjustableSpatialGraph order (fun state => field state-other state) high low :=
  (first.add second.neg).congr (fun _ => (sub_eq_add_neg _ _).symm)

theorem sum {Index : Type*} [Fintype Index]
    (fields : Index → State → StartupL2 3) (estimates : ∀ index,StartupAdjustableSpatialGraph order (fields index) high low)
    (highNonnegative : ∀ state,0≤high state) :
    StartupAdjustableSpatialGraph order (fun state => ∑ index,fields index state) high low := by
  classical
  intro epsilon positive
  let delta := epsilon/((Fintype.card Index : ℝ)+1)
  have deltaPositive : 0<delta := div_pos positive (by positivity)
  choose constants nonnegative bounded using fun index => estimates index delta deltaPositive
  refine ⟨∑ index,constants index,Finset.sum_nonneg (fun index _ => nonnegative index),?_⟩
  intro state
  choose graphs same graphBound using fun index => bounded index state
  refine ⟨∑ index,graphs index,by simp only [map_sum,same],?_⟩
  have paid := (norm_sum_le Finset.univ graphs).trans (Finset.sum_le_sum (fun index _ => graphBound index))
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Finset.sum_mul] at paid
  have allocated : (Fintype.card Index : ℝ)*delta≤epsilon := by
    have exactDelta : delta*((Fintype.card Index : ℝ)+1)=epsilon := div_mul_cancel₀ epsilon (by positivity)
    nlinarith [deltaPositive]
  have main := mul_le_mul_of_nonneg_right allocated (highNonnegative state)
  nlinarith only [paid,main]

theorem map (estimate : StartupAdjustableSpatialGraph order field high low)
    (operator : GraphGrade 3 order 0 openUnitDisk →L[ℂ] GraphGrade 3 order 0 openUnitDisk)
    (coarse : StartupL2 3 →L[ℂ] StartupL2 3)
    (same : ∀ graph,base 3 order openUnitDisk (fun _ => 0) (operator graph)=
      coarse (base 3 order openUnitDisk (fun _ => 0) graph))
    (highNonnegative : ∀ state,0≤high state) :
    StartupAdjustableSpatialGraph order (fun state => coarse (field state)) high low := by
  intro epsilon positive
  let delta := epsilon/(‖operator‖+1)
  have deltaPositive : 0<delta := div_pos positive (by positivity)
  obtain ⟨constant,nonnegative,bounded⟩ := estimate delta deltaPositive
  refine ⟨‖operator‖*constant,mul_nonneg (norm_nonneg operator) nonnegative,?_⟩
  intro state
  obtain ⟨graph,graphSame,graphBound⟩ := bounded state
  refine ⟨operator graph,by rw [same,graphSame],?_⟩
  have paid := (operator.le_opNorm graph).trans (mul_le_mul_of_nonneg_left graphBound (norm_nonneg operator))
  have allocated : ‖operator‖*delta≤epsilon := by
    have exactDelta : delta*(‖operator‖+1)=epsilon := div_mul_cancel₀ epsilon (by positivity)
    nlinarith [deltaPositive]
  have main := mul_le_mul_of_nonneg_right allocated (highNonnegative state)
  nlinarith only [paid,main]

theorem smul (estimate : StartupAdjustableSpatialGraph order field high low)
    (scalar : ℂ) (highNonnegative : ∀ state,0≤high state) :
    StartupAdjustableSpatialGraph order (fun state => scalar • field state) high low := by
  exact estimate.map (scalar • ContinuousLinearMap.id ℂ _) (scalar • ContinuousLinearMap.id ℂ _)
    (fun graph => by simp only [smul_apply,ContinuousLinearMap.id_apply,map_smul]) highNonnegative

end StartupAdjustableSpatialGraph
end Grad.CartesianStartup

import QYP14PhysicalCoreTower
import TameFixedSliceProof

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 600000

open Filter
open scoped BigOperators Topology

namespace Grad.PhysicalCoordinates

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds

variable {parameters : PhaseParameters}

def physicalFixedReferenceTransfer (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) :
    ChartState parameters →ₗ[ℂ] ChartState parameters :=
  (physicalChartState parameters).comp (referenceTransfer parameters reference insideR seed insideS)

variable (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
  (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)

theorem physicalFixedReferenceTransfer_axis (state : ChartState parameters) :
    ChartAxisCondition (physicalFixedReferenceTransfer parameters reference insideR seed insideS state) ↔
      ChartAxisCondition state := Iff.rfl

theorem chartStateNorm_physicalFixedReferenceTransfer_le (grade : ℕ) (state : ChartState parameters) :
    chartStateNorm grade (physicalFixedReferenceTransfer parameters reference insideR seed insideS state) ≤
      transferGradeFactor parameters reference seed grade * chartStateNorm grade state := by
  change chartStateNorm grade (physicalChartState parameters
    (referenceTransfer parameters reference insideR seed insideS state)) ≤ _
  rw [physicalChartState_norm]
  exact chartStateNorm_referenceTransfer_le reference insideR seed insideS grade state

theorem prod_chartStateNorm_physicalFixedReferenceTransfer_le (grade : ℕ) {order : ℕ}
    (directions : Fin order → JointState parameters) (subset : Finset (Fin order)) :
    ∏ position ∈ subset, chartStateNorm grade
        (physicalFixedReferenceTransfer parameters reference insideR seed insideS (directions position).2) ≤
      transferGradeFactor parameters reference seed grade ^ order *
        ∏ position ∈ subset, jointNorm grade (directions position) := by
  simp only [physicalFixedReferenceTransfer, LinearMap.comp_apply, physicalChartState_norm]
  exact prod_chartStateNorm_referenceTransfer_le reference insideR seed insideS grade directions subset

def physicalFixedReferenceFamily (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (order : ℕ) (state : JointState parameters) (directions : Fin order → JointState parameters) :
    QuotientState parameters :=
  (referenceScalar order state directions,
    chartDerivativeFamily parameters seed insideS order
      (physicalFixedReferenceTransfer parameters reference insideR seed insideS state.2)
      (fun position => physicalFixedReferenceTransfer parameters reference insideR seed insideS (directions position).2))

theorem physicalFixedReferenceFamily_zero (state : JointState parameters) (directions : Fin 0 → JointState parameters) :
    physicalFixedReferenceFamily parameters reference insideR seed insideS 0 state directions =
      physicalReferenceState parameters reference insideR seed insideS state := by
  unfold physicalFixedReferenceFamily physicalReferenceState
  refine Prod.ext rfl ?_
  convert chartDerivativeFamily_zeroth parameters seed insideS
    (physicalFixedReferenceTransfer parameters reference insideR seed insideS state.2) using 2
  rfl

theorem physicalFixedReferenceTransfer_line (base direction : JointState parameters) (t : ℝ) :
    physicalFixedReferenceTransfer parameters reference insideR seed insideS (base + (t : ℂ) • direction).2 =
      physicalFixedReferenceTransfer parameters reference insideR seed insideS base.2 +
        (t : ℂ) • physicalFixedReferenceTransfer parameters reference insideR seed insideS direction.2 := by
  rw [Prod.snd_add, Prod.smul_snd, map_add, map_smul]

theorem physicalFixedReferenceFamily_genuine (order : ℕ) (base : JointState parameters)
    (directions : Fin (order + 1) → JointState parameters)
    (axis : ChartAxisCondition base.2) :
    IsJointStateDirectionalDerivative
      (fun state => physicalFixedReferenceFamily parameters reference insideR seed insideS order state
        (fun position => directions position.castSucc))
      base (directions (Fin.last order))
      (physicalFixedReferenceFamily parameters reference insideR seed insideS (order + 1) base directions) := by
  intro grade
  have chart := chartDerivativeFamily_genuine parameters seed insideS order
    (physicalFixedReferenceTransfer parameters reference insideR seed insideS base.2)
    (fun position => physicalFixedReferenceTransfer parameters reference insideR seed insideS
      (directions position).2)
    ((physicalFixedReferenceTransfer_axis reference insideR seed insideS base.2).mpr axis) grade
  have scalar_zero : ∀ t : ℝ, t ≠ 0 →
      ((t : ℂ))⁻¹ * (referenceScalar order (base + (t : ℂ) • directions (Fin.last order))
          (fun position => directions position.castSucc) -
        referenceScalar order base (fun position => directions position.castSucc)) -
        referenceScalar (order + 1) base directions = 0 := by
    intro t nonzero
    have tC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nonzero
    rcases order with _ | _ | order
    · show ((t : ℂ))⁻¹ * ((base + (t : ℂ) • directions (Fin.last 0)).1 - base.1) -
        (directions 0).1 = 0
      rw [Prod.fst_add, Prod.smul_fst, smul_eq_mul, add_sub_cancel_left, ← mul_assoc,
        inv_mul_cancel₀ tC, one_mul]
      have : directions (Fin.last 0) = directions 0 := rfl
      rw [this, sub_self]
    · show ((t : ℂ))⁻¹ * ((directions (Fin.castSucc 0)).1 - (directions (Fin.castSucc 0)).1) -
        0 = 0
      rw [sub_self, mul_zero, sub_zero]
    · show ((t : ℂ))⁻¹ * ((0 : ℂ) - 0) - 0 = 0
      rw [sub_self, mul_zero, sub_zero]
  have expression : ∀ t : ℝ, t ≠ 0 →
      stateNorm grade ((((t : ℂ))⁻¹ • (physicalFixedReferenceFamily parameters reference insideR seed insideS
          order (base + (t : ℂ) • directions (Fin.last order))
          (fun position => directions position.castSucc) -
        physicalFixedReferenceFamily parameters reference insideR seed insideS order base
          (fun position => directions position.castSucc))) -
        physicalFixedReferenceFamily parameters reference insideR seed insideS (order + 1) base directions) =
      chartOutputNorm grade ((((t : ℂ))⁻¹ • (chartDerivativeFamily parameters seed insideS order
          (physicalFixedReferenceTransfer parameters reference insideR seed insideS base.2 +
            (t : ℂ) • physicalFixedReferenceTransfer parameters reference insideR seed insideS
              (directions (Fin.last order)).2)
          (fun position => physicalFixedReferenceTransfer parameters reference insideR seed insideS
            (directions position.castSucc).2) -
        chartDerivativeFamily parameters seed insideS order
          (physicalFixedReferenceTransfer parameters reference insideR seed insideS base.2)
          (fun position => physicalFixedReferenceTransfer parameters reference insideR seed insideS
            (directions position.castSucc).2))) -
        chartDerivativeFamily parameters seed insideS (order + 1)
          (physicalFixedReferenceTransfer parameters reference insideR seed insideS base.2)
          (fun position => physicalFixedReferenceTransfer parameters reference insideR seed insideS
            (directions position).2)) := by
    intro t nonzero
    have scalar := scalar_zero t nonzero
    unfold physicalFixedReferenceFamily
    rw [physicalFixedReferenceTransfer_line]
    change stateNorm grade
      ((((t : ℂ))⁻¹ * (referenceScalar order (base + (t : ℂ) • directions (Fin.last order))
          (fun position => directions position.castSucc) -
        referenceScalar order base (fun position => directions position.castSucc)) -
        referenceScalar (order + 1) base directions,
       ((t : ℂ))⁻¹ • (chartDerivativeFamily parameters seed insideS order
          (physicalFixedReferenceTransfer parameters reference insideR seed insideS base.2 +
            (t : ℂ) • physicalFixedReferenceTransfer parameters reference insideR seed insideS
              (directions (Fin.last order)).2)
          (fun position => physicalFixedReferenceTransfer parameters reference insideR seed insideS
            (directions position.castSucc).2) -
        chartDerivativeFamily parameters seed insideS order
          (physicalFixedReferenceTransfer parameters reference insideR seed insideS base.2)
          (fun position => physicalFixedReferenceTransfer parameters reference insideR seed insideS
            (directions position.castSucc).2)) -
        chartDerivativeFamily parameters seed insideS (order + 1)
          (physicalFixedReferenceTransfer parameters reference insideR seed insideS base.2)
          (fun position => physicalFixedReferenceTransfer parameters reference insideR seed insideS
            (directions position).2)) : QuotientState parameters) = _
    rw [stateNorm_pair, scalar, norm_zero, zero_add]
  refine chart.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t nonzero
  exact (expression t nonzero).symm


theorem physicalFixedReferenceFamily_bound (grade order : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : JointState parameters) (directions : Fin order → JointState parameters),
        ChartAxisCondition base.2 →
        stateNorm grade (physicalFixedReferenceFamily parameters reference insideR seed insideS order
            base directions) ≤
          constant * jointOneHigh grade 4 base directions := by
  obtain ⟨chartC, chartC_nonneg, chartBound⟩ :=
    chartDerivativeFamily_bound parameters seed insideS grade order
  set K := transferGradeFactor parameters reference seed grade with K_def
  set K4 := transferGradeFactor parameters reference seed 4 with K4_def
  have K_one : 1 ≤ K := one_le_transferGradeFactor reference seed grade
  have K4_pow_nonneg : 0 ≤ K4 ^ order := pow_nonneg (transferGradeFactor_nonneg reference seed 4) _
  refine ⟨1 + chartC * (K * K4 ^ order), by positivity, ?_⟩
  intro base directions axis
  have expr_nonneg := jointOneHigh_nonneg grade 4 base directions
  have scalarPart := norm_referenceScalar_le grade 4 order base directions
  have chartPart : chartOutputNorm grade (chartDerivativeFamily parameters seed insideS order
      (physicalFixedReferenceTransfer parameters reference insideR seed insideS base.2) (fun position => physicalFixedReferenceTransfer parameters reference insideR seed insideS (directions position).2)) ≤
      chartC * (K * K4 ^ order) * jointOneHigh grade 4 base directions := by
    have applied := chartBound (physicalFixedReferenceTransfer parameters reference insideR seed insideS base.2) (fun position => physicalFixedReferenceTransfer parameters reference insideR seed insideS (directions position).2)
      ((physicalFixedReferenceTransfer_axis reference insideR seed insideS base.2).mpr axis)
    refine applied.trans ?_
    rw [mul_assoc chartC]
    apply mul_le_mul_of_nonneg_left _ chartC_nonneg
    unfold jointOneHigh
    have baseFactor : 1 + chartStateNorm grade (physicalFixedReferenceTransfer parameters reference insideR seed insideS base.2) ≤ K * (1 + jointNorm grade base) := by
      have := (chartStateNorm_physicalFixedReferenceTransfer_le reference insideR seed insideS grade
        base.2).trans (mul_le_mul_of_nonneg_left (chartStateNorm_snd_le_jointNorm grade base)
          (transferGradeFactor_nonneg reference seed grade))
      have jn := jointNorm_nonneg grade base
      nlinarith
    have lowProduct := prod_chartStateNorm_physicalFixedReferenceTransfer_le reference insideR seed insideS 4
      directions Finset.univ
    have firstTerm : (1 + chartStateNorm grade (physicalFixedReferenceTransfer parameters reference insideR seed insideS base.2)) *
        ∏ position, chartStateNorm 4 (physicalFixedReferenceTransfer parameters reference insideR seed insideS (directions position).2) ≤
        K * K4 ^ order * ((1 + jointNorm grade base) *
          ∏ position, jointNorm 4 (directions position)) := by
      have a_nonneg : 0 ≤ 1 + chartStateNorm grade (physicalFixedReferenceTransfer parameters reference insideR seed insideS base.2) := by
        linarith [chartStateNorm_nonneg grade (physicalFixedReferenceTransfer parameters reference insideR seed insideS base.2)]
      have b_nonneg : 0 ≤ K * (1 + jointNorm grade base) :=
        mul_nonneg (transferGradeFactor_nonneg reference seed grade)
          (by linarith [jointNorm_nonneg grade base])
      calc (1 + chartStateNorm grade (physicalFixedReferenceTransfer parameters reference insideR seed insideS base.2)) *
            ∏ position, chartStateNorm 4 (physicalFixedReferenceTransfer parameters reference insideR seed insideS (directions position).2)
          ≤ (K * (1 + jointNorm grade base)) *
              (K4 ^ order * ∏ position, jointNorm 4 (directions position)) :=
            mul_le_mul baseFactor lowProduct
              (Finset.prod_nonneg fun _ _ => chartStateNorm_nonneg _ _) b_nonneg
        _ = K * K4 ^ order * ((1 + jointNorm grade base) *
              ∏ position, jointNorm 4 (directions position)) := by ring
    have secondTerm : ∑ position, chartStateNorm grade (physicalFixedReferenceTransfer parameters reference insideR seed insideS (directions position).2) *
        ∏ other ∈ Finset.univ.erase position, chartStateNorm 4 (physicalFixedReferenceTransfer parameters reference insideR seed insideS (directions other).2) ≤
        K * K4 ^ order * ∑ position, jointNorm grade (directions position) *
          ∏ other ∈ Finset.univ.erase position, jointNorm 4 (directions other) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro position _
      have highFactor : chartStateNorm grade (physicalFixedReferenceTransfer parameters reference insideR seed insideS (directions position).2) ≤
          K * jointNorm grade (directions position) :=
        (chartStateNorm_physicalFixedReferenceTransfer_le reference insideR seed insideS grade _).trans
          (mul_le_mul_of_nonneg_left (chartStateNorm_snd_le_jointNorm grade _)
            (transferGradeFactor_nonneg reference seed grade))
      have lowFactor := prod_chartStateNorm_physicalFixedReferenceTransfer_le reference insideR seed insideS 4
        directions (Finset.univ.erase position)
      calc chartStateNorm grade (physicalFixedReferenceTransfer parameters reference insideR seed insideS (directions position).2) *
            ∏ other ∈ Finset.univ.erase position, chartStateNorm 4 (physicalFixedReferenceTransfer parameters reference insideR seed insideS (directions other).2)
          ≤ (K * jointNorm grade (directions position)) *
              (K4 ^ order * ∏ other ∈ Finset.univ.erase position, jointNorm 4 (directions other)) :=
            mul_le_mul highFactor lowFactor
              (Finset.prod_nonneg fun _ _ => chartStateNorm_nonneg _ _)
              (mul_nonneg (transferGradeFactor_nonneg reference seed grade) (jointNorm_nonneg _ _))
        _ = K * K4 ^ order * (jointNorm grade (directions position) *
              ∏ other ∈ Finset.univ.erase position, jointNorm 4 (directions other)) := by ring
    calc (1 + chartStateNorm grade (physicalFixedReferenceTransfer parameters reference insideR seed insideS base.2)) *
          ∏ position, chartStateNorm 4 (physicalFixedReferenceTransfer parameters reference insideR seed insideS (directions position).2) +
        ∑ position, chartStateNorm grade (physicalFixedReferenceTransfer parameters reference insideR seed insideS (directions position).2) *
          ∏ other ∈ Finset.univ.erase position, chartStateNorm 4 (physicalFixedReferenceTransfer parameters reference insideR seed insideS (directions other).2)
        ≤ K * K4 ^ order * ((1 + jointNorm grade base) *
            ∏ position, jointNorm 4 (directions position)) +
          K * K4 ^ order * ∑ position, jointNorm grade (directions position) *
            ∏ other ∈ Finset.univ.erase position, jointNorm 4 (directions other) :=
          add_le_add firstTerm secondTerm
      _ = K * K4 ^ order * ((1 + jointNorm grade base) *
            ∏ position, jointNorm 4 (directions position) +
          ∑ position, jointNorm grade (directions position) *
            ∏ other ∈ Finset.univ.erase position, jointNorm 4 (directions other)) := by ring
  have split : (1 + chartC * (K * K4 ^ order)) * jointOneHigh grade 4 base directions =
      jointOneHigh grade 4 base directions +
        chartC * (K * K4 ^ order) * jointOneHigh grade 4 base directions := by ring
  unfold physicalFixedReferenceFamily
  rw [stateNorm_pair, split]
  linarith


end Grad.PhysicalCoordinates

import AIY9OriginalStrongHilbertCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option synthInstance.maxHeartbeats 400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularStrongData
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularCurrentEnergy
open Grad.AnnularCurrentSource Grad.AnnularHighTilt Grad.AnnularLowEnergy Grad.AnnularCrossMaps
open Grad.ActualBoundaryPrimitives

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (angular cell : ℕ)

theorem StrongDataCarrier.component_bounds
    (data : StrongDataCarrier parameters lower positive bounded angular cell) :
    (∀ slot : Fin 4, ‖data.val.ofLp.1.ofLp.1.ofLp.1 slot‖ ≤ ‖data‖) ∧
    (∀ slot : Fin 3, ‖data.val.ofLp.1.ofLp.1.ofLp.2 slot‖ ≤ ‖data‖) ∧
    ‖data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.1‖ ≤ ‖data‖ ∧
    ‖data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.2‖ ≤ ‖data‖ ∧
    ‖data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.1‖ ≤ ‖data‖ ∧
    ‖data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.2‖ ≤ ‖data‖ ∧
    ‖data.val.ofLp.2‖ ≤ ‖data‖ := by
  have shared := hilbert_first_bound data.val
  have bulk := (hilbert_first_bound data.val.ofLp.1).trans shared
  have graphBoundary := (hilbert_second_bound data.val.ofLp.1).trans shared
  have graphs := (hilbert_first_bound data.val.ofLp.1.ofLp.2).trans graphBoundary
  have boundary := (hilbert_second_bound data.val.ofLp.1.ofLp.2).trans graphBoundary
  refine ⟨?_, ?_, (hilbert_first_bound _).trans graphs,
    (hilbert_second_bound _).trans graphs, (hilbert_first_bound _).trans boundary,
    (hilbert_second_bound _).trans boundary, hilbert_second_bound data.val⟩
  · intro slot
    exact (finite_hilbert_coordinate_bound _ slot).trans ((hilbert_first_bound _).trans bulk)
  · intro slot
    exact (finite_hilbert_coordinate_bound _ slot).trans ((hilbert_second_bound _).trans bulk)

private theorem norm_four_sum {E : Type*} [NormedAddCommGroup E]
    (data : PiLp 2 (fun _ : Fin 4 => E)) :
    ‖data‖ ≤ ‖data 0‖ + ‖data 1‖ + ‖data 2‖ + ‖data 3‖ := by
  have square := PiLp.norm_sq_eq_of_L2 _ data
  rw [Fin.sum_univ_four] at square
  nlinarith [norm_nonneg data, norm_nonneg (data 0), norm_nonneg (data 1),
    norm_nonneg (data 2), norm_nonneg (data 3),
    mul_nonneg (norm_nonneg (data 0)) (norm_nonneg (data 1)),
    mul_nonneg (norm_nonneg (data 0)) (norm_nonneg (data 2)),
    mul_nonneg (norm_nonneg (data 0)) (norm_nonneg (data 3)),
    mul_nonneg (norm_nonneg (data 1)) (norm_nonneg (data 2)),
    mul_nonneg (norm_nonneg (data 1)) (norm_nonneg (data 3)),
    mul_nonneg (norm_nonneg (data 2)) (norm_nonneg (data 3))]

private theorem norm_three_sum {E : Type*} [NormedAddCommGroup E]
    (data : PiLp 2 (fun _ : Fin 3 => E)) :
    ‖data‖ ≤ ‖data 0‖ + ‖data 1‖ + ‖data 2‖ := by
  have square := PiLp.norm_sq_eq_of_L2 _ data
  rw [Fin.sum_univ_three] at square
  nlinarith [norm_nonneg data, norm_nonneg (data 0), norm_nonneg (data 1), norm_nonneg (data 2),
    mul_nonneg (norm_nonneg (data 0)) (norm_nonneg (data 1)),
    mul_nonneg (norm_nonneg (data 0)) (norm_nonneg (data 2)),
    mul_nonneg (norm_nonneg (data 1)) (norm_nonneg (data 2))]

theorem StrongDataCarrier.norm_le_sum
    (data : StrongDataCarrier parameters lower positive bounded angular cell) :
    ‖data‖ ≤
      ‖data.val.ofLp.1.ofLp.1.ofLp.1 0‖ + ‖data.val.ofLp.1.ofLp.1.ofLp.1 1‖ +
      ‖data.val.ofLp.1.ofLp.1.ofLp.1 2‖ + ‖data.val.ofLp.1.ofLp.1.ofLp.1 3‖ +
      ‖data.val.ofLp.1.ofLp.1.ofLp.2 0‖ + ‖data.val.ofLp.1.ofLp.1.ofLp.2 1‖ +
      ‖data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.1‖ + ‖data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.2‖ +
      ‖data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.1‖ + ‖data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.2‖ +
      ‖data.val.ofLp.2‖ := by
  have main := hilbert_norm_le_add data.val
  have shared := hilbert_norm_le_add data.val.ofLp.1
  have bulk := hilbert_norm_le_add data.val.ofLp.1.ofLp.1
  have known := norm_four_sum data.val.ofLp.1.ofLp.1.ofLp.1
  have auxiliary := norm_three_sum data.val.ofLp.1.ofLp.1.ofLp.2
  have graphBoundary := hilbert_norm_le_add data.val.ofLp.1.ofLp.2
  have graphs := hilbert_norm_le_add data.val.ofLp.1.ofLp.2.ofLp.1
  have boundary := hilbert_norm_le_add data.val.ofLp.1.ofLp.2.ofLp.2
  have zero := StrongDataCarrier.spare_zero parameters lower positive bounded angular cell data
  change data.val.ofLp.1.ofLp.1.ofLp.2 2 = 0 at zero
  rw [zero, norm_zero] at auxiliary
  change ‖data.val‖ ≤ _
  linarith only [main,shared,bulk,known,auxiliary,graphBoundary,graphs,boundary]

variable (length : ℝ) (lengthPositive : 0 < length)

private theorem sevenDataTransformBound
    {K A G0 G2 H I J F G : Type*}
    [NormedAddCommGroup K] [NormedAddCommGroup A] [NormedAddCommGroup G0]
    [NormedAddCommGroup G2] [NormedAddCommGroup H] [NormedAddCommGroup I]
    [NormedAddCommGroup J] [NormedAddCommGroup F] [NormedAddCommGroup G]
    (f : K → F) (g : A → G) (high : I → I) (low : J → J) (C : ℝ) (Cnonnegative : 0 ≤ C)
    (fBound : ∀ x, ‖f x‖ ≤ ‖x‖) (gBound : ∀ x, ‖g x‖ ≤ 2 * ‖x‖)
    (highBound : ∀ x, ‖high x‖ ≤ ‖x‖) (lowBound : ∀ x, ‖low x‖ ≤ C * ‖x‖)
    (data : WithLp 2 (WithLp 2 (WithLp 2 (K × A) ×
      WithLp 2 (WithLp 2 (G0 × G2) × WithLp 2 (H × I))) × J)) :
    ‖WithLp.toLp 2
      (WithLp.toLp 2 (data.ofLp.1.ofLp.2.ofLp.1,
        WithLp.toLp 2 (f data.ofLp.1.ofLp.1.ofLp.1,g data.ofLp.1.ofLp.1.ofLp.2)),
      WithLp.toLp 2 (data.ofLp.1.ofLp.2.ofLp.2.ofLp.1,
        WithLp.toLp 2 (high data.ofLp.1.ofLp.2.ofLp.2.ofLp.2,low data.ofLp.2)))‖ ≤
      (7 + C) * ‖data‖ := by
  let result := WithLp.toLp 2
      (WithLp.toLp 2 (data.ofLp.1.ofLp.2.ofLp.1,
        WithLp.toLp 2 (f data.ofLp.1.ofLp.1.ofLp.1,g data.ofLp.1.ofLp.1.ofLp.2)),
      WithLp.toLp 2 (data.ofLp.1.ofLp.2.ofLp.2.ofLp.1,
        WithLp.toLp 2 (high data.ofLp.1.ofLp.2.ofLp.2.ofLp.2,low data.ofLp.2)))
  have shared := hilbert_first_bound data
  have bulk := (hilbert_first_bound data.ofLp.1).trans shared
  have gb := (hilbert_second_bound data.ofLp.1).trans shared
  have graphs := (hilbert_first_bound data.ofLp.1.ofLp.2).trans gb
  have boundary := (hilbert_second_bound data.ofLp.1.ofLp.2).trans gb
  have first := (hilbert_first_bound data.ofLp.1.ofLp.2.ofLp.1).trans graphs
  have second := (hilbert_second_bound data.ofLp.1.ofLp.2.ofLp.1).trans graphs
  have ff := (fBound _).trans ((hilbert_first_bound data.ofLp.1.ofLp.1).trans bulk)
  have gg := (gBound _).trans (mul_le_mul_of_nonneg_left
    ((hilbert_second_bound data.ofLp.1.ofLp.1).trans bulk) (by norm_num : (0 : ℝ) ≤ 2))
  have hh := (hilbert_first_bound data.ofLp.1.ofLp.2.ofLp.2).trans boundary
  have ii := (highBound _).trans ((hilbert_second_bound data.ofLp.1.ofLp.2.ofLp.2).trans boundary)
  have jj := (lowBound _).trans (mul_le_mul_of_nonneg_left (hilbert_second_bound data) Cnonnegative)
  have main := hilbert_norm_le_add result
  have left := hilbert_norm_le_add result.ofLp.1
  have graphSum := hilbert_norm_le_add result.ofLp.1.ofLp.1
  have fg := hilbert_norm_le_add result.ofLp.1.ofLp.2
  have right := hilbert_norm_le_add result.ofLp.2
  have incoming := hilbert_norm_le_add result.ofLp.2.ofLp.2
  change ‖result‖ ≤ _
  dsimp only [result,WithLp.ofLp_toLp] at main left graphSum fg right incoming
  linarith only [main,left,graphSum,fg,right,incoming,first,second,ff,gg,hh,ii,jj]

/-- Reverse BF5 comparison for all seven original datum coordinates. -/
theorem strongOriginalCoordinateMap_bound
    (data : StrongDataCarrier parameters lower positive bounded angular cell) :
    ‖strongOriginalCoordinateMap parameters lower length positive bounded lengthPositive angular cell data‖ ≤
      (7 + 2 * lowOuterFrequencyConstant length) * ‖data‖ := by
  have constant : 0 ≤ 2 * lowOuterFrequencyConstant length := by
    have := lowOuterFrequencyConstant_two_le length lengthPositive
    positivity
  exact sevenDataTransformBound
    (fun known : HighKnownSourceBulk lower => divisionHighUnweight lower positive bounded (known 3))
    (fun auxiliary : HighAuxiliarySourceBulk lower => strengthenedG lower
      (divisionHighUnweight lower positive bounded (auxiliary 0))
      (divisionHighUnweight lower positive bounded (auxiliary 1)))
    (fun incoming : AnnularBoundary => lower ^ (9 / 4 : ℝ) • incoming)
    (originalLowIncomingUnweightMap parameters lower length positive bounded lengthPositive)
    (2 * lowOuterFrequencyConstant length) constant
    (fun known => (divisionHighUnweight_bound lower positive bounded (known 3)).trans
      (finite_hilbert_coordinate_bound known 3))
    (fun auxiliary => (strengthenedG_bound lower _ _).trans
      ((add_le_add
        ((divisionHighUnweight_bound lower positive bounded (auxiliary 0)).trans
          (finite_hilbert_coordinate_bound auxiliary 0))
        ((divisionHighUnweight_bound lower positive bounded (auxiliary 1)).trans
          (finite_hilbert_coordinate_bound auxiliary 1))).trans_eq (two_mul ‖auxiliary‖).symm))
    (fun incoming => by
      rw [norm_smul, Real.norm_of_nonneg (Real.rpow_pos_of_pos positive _).le]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (Real.rpow_le_one positive.le bounded (by norm_num : (0 : ℝ) ≤ 9 / 4)) (norm_nonneg incoming))
    (originalLowIncomingUnweightMap_bound parameters lower length positive bounded lengthPositive)
    data.val

end Grad.AnnularStrongData

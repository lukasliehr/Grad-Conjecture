import AIY3ExactHighDataRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularStrongData
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceCollarFullSource Grad.AnnularSourceGraph Grad.AnnularVariational
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentGreen Grad.AnnularCurrentSource
open Grad.AnnularKnownLow Grad.AnnularLowEnergy

private theorem pair_norm_mono {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] (a c : E) (b d : F)
    (first : ‖a‖ ≤ ‖c‖) (second : ‖b‖ ≤ ‖d‖) :
    ‖WithLp.toLp 2 (a,b)‖ ≤ ‖WithLp.toLp 2 (c,d)‖ := by
  have left := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (a,b))
  have right := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (c,d))
  change ‖WithLp.toLp 2 (a,b)‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 at left
  change ‖WithLp.toLp 2 (c,d)‖ ^ 2 = ‖c‖ ^ 2 + ‖d‖ ^ 2 at right
  have bound := add_le_add (sq_le_sq₀ (norm_nonneg a) (norm_nonneg c) |>.mpr first)
    (sq_le_sq₀ (norm_nonneg b) (norm_nonneg d) |>.mpr second)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith)

theorem strongHighWeightedMap_bound (lower : ℝ) (data : HighKnownSourceBulk lower) :
    ‖strongHighWeightedMap lower data‖ ≤ ‖data‖ := by
  have first := highKnownSourceBulk_norm_sq lower data
  have second := highKnownSourceBulk_norm_sq lower (strongHighWeightedMap lower data)
  change ‖strongHighWeightedMap lower data‖ ^ 2 =
    ‖data 0‖ ^ 2 + ‖data 1‖ ^ 2 + ‖data 2‖ ^ 2 + ‖highRowProjection lower (data 3)‖ ^ 2 at second
  have bound := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (strongHighRow_bound lower (data 3))
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith)

theorem strongHighAuxiliaryMap_bound (lower : ℝ) (data : HighAuxiliarySourceBulk lower) :
    ‖strongHighAuxiliaryMap lower data‖ ≤ ‖data‖ := by
  have first := PiLp.norm_sq_eq_of_L2 _ data
  have second := PiLp.norm_sq_eq_of_L2 _ (strongHighAuxiliaryMap lower data)
  rw [Fin.sum_univ_three] at first second
  change ‖strongHighAuxiliaryMap lower data‖ ^ 2 =
    ‖highRowProjection lower (data 0)‖ ^ 2 + ‖(0 : DivisionRow 1 lower)‖ ^ 2 +
      ‖(0 : DivisionRow 1 lower)‖ ^ 2 at second
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at second
  have bound := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (strongHighRow_bound lower (data 0))
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by
    nlinarith [sq_nonneg ‖data 1‖, sq_nonneg ‖data 2‖])

theorem strongHighBulkMap_bound (lower : ℝ) (data : HighKnownBulkHilbert lower) :
    ‖strongHighBulkMap lower data‖ ≤ ‖data‖ :=
  pair_norm_mono _ _ _ _ (strongHighWeightedMap_bound lower data.ofLp.1)
    (strongHighAuxiliaryMap_bound lower data.ofLp.2)

theorem strongHighAmbientMap_bound (parameters : PhaseParameters) (lower : ℝ)
    (angular cell : ℕ) (data : ActualHighKnownAmbient parameters lower angular cell) :
    ‖strongHighAmbientMap parameters lower angular cell data‖ ≤ ‖data‖ :=
  pair_norm_mono _ _ _ _ (strongHighBulkMap_bound lower data.ofLp.1) le_rfl

/-- The AIR input takes the same four complete source rows, the full `g`
(not its radial derivative or independent `Rg` coordinate), and the exact
low incoming datum.  AIR itself forms the genuine low angular `+Rg`. -/
def strongLowAmbientMap (parameters : PhaseParameters) (lower : ℝ)
    (angular cell : ℕ) : StrongDataAmbient parameters lower angular cell →L[ℝ]
      KnownLowData lower :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    (((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
      (((highKnownWeightedProjection parameters lower angular cell).comp
        (strongSharedProjection parameters lower angular cell)).prod
       ((highKnownWeightedG parameters lower angular cell).comp
        (strongSharedProjection parameters lower angular cell)))).prod
      (strongLowIncomingProjection parameters lower angular cell))

variable (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell : ℕ)

def strongToLow : StrongDataCarrier parameters lower positive bounded angular cell →L[ℝ]
    KnownLowData lower :=
  (strongLowAmbientMap parameters lower angular cell).comp
    (StrongDataCarrier parameters lower positive bounded angular cell).subtypeL

theorem strongToLow_exact
    (data : StrongDataCarrier parameters lower positive bounded angular cell) :
    (strongToLow parameters lower positive bounded angular cell data).ofLp.1.ofLp.1 =
      data.val.ofLp.1.ofLp.1.ofLp.1 ∧
    (strongToLow parameters lower positive bounded angular cell data).ofLp.1.ofLp.2 =
      data.val.ofLp.1.ofLp.1.ofLp.2 0 ∧
    (strongToLow parameters lower positive bounded angular cell data).ofLp.2 = data.val.ofLp.2 :=
  ⟨rfl,rfl,rfl⟩

/-- Literal BF4 Hilbert norm: six weighted bulk rows, the two original
source graphs and the genuine outer/high-incoming/low-incoming coordinates.
Each original source graph occurs exactly once. -/
theorem StrongDataCarrier.norm_sq
    (data : StrongDataCarrier parameters lower positive bounded angular cell) :
    ‖data‖ ^ 2 =
      ‖data.val.ofLp.1.ofLp.1.ofLp.1‖ ^ 2 +
      ‖data.val.ofLp.1.ofLp.1.ofLp.2 0‖ ^ 2 +
      ‖data.val.ofLp.1.ofLp.1.ofLp.2 1‖ ^ 2 +
      ‖data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.1‖ ^ 2 +
      ‖data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.2‖ ^ 2 +
      ‖data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.1‖ ^ 2 +
      ‖data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.2‖ ^ 2 + ‖data.val.ofLp.2‖ ^ 2 := by
  have shared := actualHighKnownAmbient_norm_sq parameters lower angular cell data.val.ofLp.1
  have outer := WithLp.prod_norm_sq_eq_of_L2 data.val
  have auxiliary := PiLp.norm_sq_eq_of_L2 _ data.val.ofLp.1.ofLp.1.ofLp.2
  rw [Fin.sum_univ_three] at auxiliary
  have zero := StrongDataCarrier.spare_zero parameters lower positive bounded angular cell data
  change data.val.ofLp.1.ofLp.1.ofLp.2 2 = 0 at zero
  rw [zero, norm_zero] at auxiliary
  simp only [highKnownWeightedProjection_apply, highKnownAuxiliaryProjection_apply,
    highKnownF0GraphProjection_apply, highKnownF2GraphProjection_apply,
    highKnownDatumProjection_apply, highKnownIncomingProjection_apply] at shared
  change ‖data.val‖ ^ 2 = ‖data.val.ofLp.1‖ ^ 2 + ‖data.val.ofLp.2‖ ^ 2 at outer
  change ‖data.val‖ ^ 2 = _
  linarith

theorem strongToHigh_bound
    (data : StrongDataCarrier parameters lower positive bounded angular cell) :
    ‖strongToHigh parameters lower positive bounded angular cell data‖ ≤ ‖data‖ := by
  have outer := WithLp.prod_norm_sq_eq_of_L2 data.val
  change ‖data.val‖ ^ 2 = ‖data.val.ofLp.1‖ ^ 2 + ‖data.val.ofLp.2‖ ^ 2 at outer
  have bound : ‖data.val.ofLp.1‖ ≤ ‖data.val‖ := by
    nlinarith [norm_nonneg data.val, norm_nonneg data.val.ofLp.1,
      sq_nonneg ‖data.val.ofLp.2‖]
  exact (strongHighAmbientMap_bound parameters lower angular cell data.val.ofLp.1).trans bound

theorem strongToLow_bound
    (data : StrongDataCarrier parameters lower positive bounded angular cell) :
    ‖strongToLow parameters lower positive bounded angular cell data‖ ≤ ‖data‖ := by
  have normSq := StrongDataCarrier.norm_sq parameters lower positive bounded angular cell data
  have outer := WithLp.prod_norm_sq_eq_of_L2
    (strongToLow parameters lower positive bounded angular cell data)
  have bulk := WithLp.prod_norm_sq_eq_of_L2
    (strongToLow parameters lower positive bounded angular cell data).ofLp.1
  change ‖strongToLow parameters lower positive bounded angular cell data‖ ^ 2 =
    ‖(strongToLow parameters lower positive bounded angular cell data).ofLp.1‖ ^ 2 +
      ‖data.val.ofLp.2‖ ^ 2 at outer
  change ‖(strongToLow parameters lower positive bounded angular cell data).ofLp.1‖ ^ 2 =
    ‖data.val.ofLp.1.ofLp.1.ofLp.1‖ ^ 2 + ‖data.val.ofLp.1.ofLp.1.ofLp.2 0‖ ^ 2 at bulk
  exact (sq_le_sq₀ (norm_nonneg (strongToLow parameters lower positive bounded angular cell data))
    (norm_nonneg data)).mp (by
    linarith only [normSq, outer, bulk, sq_nonneg ‖data.val.ofLp.1.ofLp.1.ofLp.2 1‖,
      sq_nonneg ‖data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.1‖,
      sq_nonneg ‖data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.2‖,
      sq_nonneg ‖data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.1‖,
      sq_nonneg ‖data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.2‖])

end Grad.AnnularStrongData

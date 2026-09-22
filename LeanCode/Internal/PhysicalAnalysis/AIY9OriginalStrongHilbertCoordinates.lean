import AIY8OriginalLowIncomingEquivalence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularStrongData
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularCurrentEnergy
open Grad.AnnularCurrentSource Grad.AnnularHighTilt Grad.AnnularLowEnergy Grad.AnnularCrossMaps
open Grad.ActualBoundaryPrimitives

theorem hilbert_first_bound {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (data : WithLp 2 (E × F)) : ‖data.ofLp.1‖ ≤ ‖data‖ := by
  have square := WithLp.prod_norm_sq_eq_of_L2 data
  change ‖data‖ ^ 2 = ‖data.ofLp.1‖ ^ 2 + ‖data.ofLp.2‖ ^ 2 at square
  nlinarith [norm_nonneg data, norm_nonneg data.ofLp.1, sq_nonneg ‖data.ofLp.2‖]

theorem hilbert_second_bound {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (data : WithLp 2 (E × F)) : ‖data.ofLp.2‖ ≤ ‖data‖ := by
  have square := WithLp.prod_norm_sq_eq_of_L2 data
  change ‖data‖ ^ 2 = ‖data.ofLp.1‖ ^ 2 + ‖data.ofLp.2‖ ^ 2 at square
  nlinarith [norm_nonneg data, norm_nonneg data.ofLp.2, sq_nonneg ‖data.ofLp.1‖]

theorem hilbert_norm_le_add {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (data : WithLp 2 (E × F)) : ‖data‖ ≤ ‖data.ofLp.1‖ + ‖data.ofLp.2‖ := by
  have square := WithLp.prod_norm_sq_eq_of_L2 data
  change ‖data‖ ^ 2 = ‖data.ofLp.1‖ ^ 2 + ‖data.ofLp.2‖ ^ 2 at square
  nlinarith [norm_nonneg data, norm_nonneg data.ofLp.1, norm_nonneg data.ofLp.2,
    mul_nonneg (norm_nonneg data.ofLp.1) (norm_nonneg data.ofLp.2)]

theorem finite_hilbert_coordinate_bound {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (data : PiLp 2 (fun _ : Fin n => E)) (slot : Fin n) : ‖data slot‖ ≤ ‖data‖ := by
  have square : ‖data slot‖ ^ 2 ≤ ∑ index : Fin n, ‖data index‖ ^ 2 :=
    Finset.single_le_sum (fun index _ => sq_nonneg ‖data index‖) (Finset.mem_univ slot)
  rw [← PiLp.norm_sq_eq_of_L2] at square
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp square

/-- Exact seven strengthened AK20 datum coordinates: two original AH source
graphs, original f and strengthened angular g, physical outer h, full scalar
incoming d split high/low, and low angular incoming Rk. -/
abbrev OriginalStrongAmbient (parameters : PhaseParameters) (lower : ℝ)
    (angular cell : ℕ) :=
  WithLp 2
    (WithLp 2 (HighKnownGraphHilbert parameters lower ×
      WithLp 2 (DivisionRow 1 lower × DivisionRow 1 lower)) ×
      WithLp 2 (HighBoundaryPrimitive parameters angular cell ×
        WithLp 2 (AnnularBoundary × LowEnergyBoundary)))

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length) (angular cell : ℕ)

private def originalFMap :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower :=
  ((divisionHighUnweight lower positive bounded).restrictScalars ℝ).comp
    (highKnownWeightedF parameters lower angular cell)

private def originalGMap :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower :=
  ((divisionHighUnweight lower positive bounded).restrictScalars ℝ).comp
    (highKnownWeightedG parameters lower angular cell) +
  ((angularRecoveryMap lower).restrictScalars ℝ).comp
    (((divisionHighUnweight lower positive bounded).restrictScalars ℝ).comp
      (highKnownWeightedQc parameters lower angular cell))

/-- Forget redundant weighted F0/RF0/F2 norm coordinates using their genuine
shared radial graphs, undo the bulk tilt, and restore the exact original
angular and incoming norms. The original phase is unchanged. -/
def strongOriginalCoordinateMap :
    StrongDataCarrier parameters lower positive bounded angular cell →L[ℝ]
      OriginalStrongAmbient parameters lower angular cell :=
  let shared := (strongSharedProjection parameters lower angular cell).comp
    (StrongDataCarrier parameters lower positive bounded angular cell).subtypeL
  let graphPair := (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    (((highKnownF0GraphProjection parameters lower angular cell).comp shared).prod
      ((highKnownF2GraphProjection parameters lower angular cell).comp shared))
  let fgPair := (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    (((originalFMap parameters lower positive bounded angular cell).comp shared).prod
      ((originalGMap parameters lower positive bounded angular cell).comp shared))
  let innerPair := (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    (((lower ^ (9 / 4 : ℝ)) •
      ((highKnownIncomingProjection parameters lower angular cell).comp shared)).prod
      (((originalLowIncomingUnweightMap parameters lower length positive bounded lengthPositive).restrictScalars ℝ).comp
        ((strongLowIncomingProjection parameters lower angular cell).comp
          (StrongDataCarrier parameters lower positive bounded angular cell).subtypeL)))
  let left := (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    (graphPair.prod fgPair)
  let right := (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    (((highKnownDatumProjection parameters lower angular cell).comp shared).prod innerPair)
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp (left.prod right)

theorem strongOriginalCoordinateMap_exact
    (data : StrongDataCarrier parameters lower positive bounded angular cell) :
    let original := strongOriginalCoordinateMap parameters lower length positive bounded lengthPositive angular cell data
    original.ofLp.1.ofLp.1 = data.val.ofLp.1.ofLp.2.ofLp.1 ∧
    original.ofLp.1.ofLp.2.ofLp.1 = divisionHighUnweight lower positive bounded
      (data.val.ofLp.1.ofLp.1.ofLp.1 3) ∧
    original.ofLp.1.ofLp.2.ofLp.2 = strengthenedG lower
      (divisionHighUnweight lower positive bounded (data.val.ofLp.1.ofLp.1.ofLp.2 0))
      (divisionHighUnweight lower positive bounded (data.val.ofLp.1.ofLp.1.ofLp.2 1)) ∧
    original.ofLp.2.ofLp.1 = data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.1 ∧
    original.ofLp.2.ofLp.2.ofLp.1 = lower ^ (9 / 4 : ℝ) • data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.2 ∧
    original.ofLp.2.ofLp.2.ofLp.2 =
      originalLowIncomingUnweightMap parameters lower length positive bounded lengthPositive data.val.ofLp.2 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Norm of the actual original seven datum coordinates, without separately
charging F0/RF0/F2 outside their source graphs. -/
theorem originalStrongAmbient_norm_sq (data : OriginalStrongAmbient parameters lower angular cell) :
    ‖data‖ ^ 2 =
      ‖data.ofLp.1.ofLp.1.ofLp.1‖ ^ 2 + ‖data.ofLp.1.ofLp.1.ofLp.2‖ ^ 2 +
      ‖data.ofLp.1.ofLp.2.ofLp.1‖ ^ 2 + ‖data.ofLp.1.ofLp.2.ofLp.2‖ ^ 2 +
      ‖data.ofLp.2.ofLp.1‖ ^ 2 + ‖data.ofLp.2.ofLp.2.ofLp.1‖ ^ 2 +
      ‖data.ofLp.2.ofLp.2.ofLp.2‖ ^ 2 := by
  have main := WithLp.prod_norm_sq_eq_of_L2 data
  have left := WithLp.prod_norm_sq_eq_of_L2 data.ofLp.1
  have graphs := WithLp.prod_norm_sq_eq_of_L2 data.ofLp.1.ofLp.1
  have fg := WithLp.prod_norm_sq_eq_of_L2 data.ofLp.1.ofLp.2
  have right := WithLp.prod_norm_sq_eq_of_L2 data.ofLp.2
  have incoming := WithLp.prod_norm_sq_eq_of_L2 data.ofLp.2.ofLp.2
  change ‖data‖ ^ 2 = ‖data.ofLp.1‖ ^ 2 + ‖data.ofLp.2‖ ^ 2 at main
  change ‖data.ofLp.1‖ ^ 2 = ‖data.ofLp.1.ofLp.1‖ ^ 2 + ‖data.ofLp.1.ofLp.2‖ ^ 2 at left
  change ‖data.ofLp.1.ofLp.1‖ ^ 2 = ‖data.ofLp.1.ofLp.1.ofLp.1‖ ^ 2 + ‖data.ofLp.1.ofLp.1.ofLp.2‖ ^ 2 at graphs
  change ‖data.ofLp.1.ofLp.2‖ ^ 2 = ‖data.ofLp.1.ofLp.2.ofLp.1‖ ^ 2 + ‖data.ofLp.1.ofLp.2.ofLp.2‖ ^ 2 at fg
  change ‖data.ofLp.2‖ ^ 2 = ‖data.ofLp.2.ofLp.1‖ ^ 2 + ‖data.ofLp.2.ofLp.2‖ ^ 2 at right
  change ‖data.ofLp.2.ofLp.2‖ ^ 2 = ‖data.ofLp.2.ofLp.2.ofLp.1‖ ^ 2 + ‖data.ofLp.2.ofLp.2.ofLp.2‖ ^ 2 at incoming
  linarith only [main,left,graphs,fg,right,incoming]

theorem originalStrongAmbient_norm_le_sum (data : OriginalStrongAmbient parameters lower angular cell) :
    ‖data‖ ≤
      ‖data.ofLp.1.ofLp.1.ofLp.1‖ + ‖data.ofLp.1.ofLp.1.ofLp.2‖ +
      ‖data.ofLp.1.ofLp.2.ofLp.1‖ + ‖data.ofLp.1.ofLp.2.ofLp.2‖ +
      ‖data.ofLp.2.ofLp.1‖ + ‖data.ofLp.2.ofLp.2.ofLp.1‖ +
      ‖data.ofLp.2.ofLp.2.ofLp.2‖ := by
  have main := hilbert_norm_le_add data
  have left := hilbert_norm_le_add data.ofLp.1
  have graphs := hilbert_norm_le_add data.ofLp.1.ofLp.1
  have fg := hilbert_norm_le_add data.ofLp.1.ofLp.2
  have right := hilbert_norm_le_add data.ofLp.2
  have incoming := hilbert_norm_le_add data.ofLp.2.ofLp.2
  linarith only [main,left,graphs,fg,right,incoming]

theorem originalStrongAmbient_component_bounds (data : OriginalStrongAmbient parameters lower angular cell) :
    ‖data.ofLp.1.ofLp.1.ofLp.1‖ ≤ ‖data‖ ∧ ‖data.ofLp.1.ofLp.1.ofLp.2‖ ≤ ‖data‖ ∧
    ‖data.ofLp.1.ofLp.2.ofLp.1‖ ≤ ‖data‖ ∧ ‖data.ofLp.1.ofLp.2.ofLp.2‖ ≤ ‖data‖ ∧
    ‖data.ofLp.2.ofLp.1‖ ≤ ‖data‖ ∧ ‖data.ofLp.2.ofLp.2.ofLp.1‖ ≤ ‖data‖ ∧
    ‖data.ofLp.2.ofLp.2.ofLp.2‖ ≤ ‖data‖ := by
  have left := hilbert_first_bound data
  have right := hilbert_second_bound data
  have graphs := (hilbert_first_bound data.ofLp.1).trans left
  have fg := (hilbert_second_bound data.ofLp.1).trans left
  have incoming := (hilbert_second_bound data.ofLp.2).trans right
  exact ⟨(hilbert_first_bound _).trans graphs, (hilbert_second_bound _).trans graphs,
    (hilbert_first_bound _).trans fg, (hilbert_second_bound _).trans fg,
    (hilbert_first_bound _).trans right, (hilbert_first_bound _).trans incoming,
    (hilbert_second_bound _).trans incoming⟩

end Grad.AnnularStrongData

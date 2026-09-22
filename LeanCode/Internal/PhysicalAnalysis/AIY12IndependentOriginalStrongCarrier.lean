import AIY11OriginalStrongForwardComparison

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option synthInstance.maxHeartbeats 400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularStrongData
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarFullSource
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularCurrentEnergy
open Grad.AnnularCurrentSource Grad.AnnularHighTilt Grad.AnnularLowEnergy Grad.AnnularCrossMaps
open Grad.ActualBoundaryPrimitives

private def pairFirst {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : WithLp 2 (E × F) →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ _ _).comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toContinuousLinearMap

private def pairSecond {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : WithLp 2 (E × F) →L[ℝ] F :=
  (ContinuousLinearMap.snd ℝ _ _).comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toContinuousLinearMap

variable (parameters : PhaseParameters) (lower : ℝ) (angular cell : ℕ)

def originalF2Projection : OriginalStrongAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower :=
  (unweightedSourceF2Bulk parameters lower).comp
    ((pairSecond (E := HighF0SourceGraph parameters lower) (F := HighF2SourceGraph parameters lower)).comp
      ((pairFirst (E := HighKnownGraphHilbert parameters lower) (F := WithLp 2 (DivisionRow 1 lower × DivisionRow 1 lower))).comp (pairFirst (E := WithLp 2 (HighKnownGraphHilbert parameters lower × WithLp 2 (DivisionRow 1 lower × DivisionRow 1 lower))) (F := WithLp 2 (HighBoundaryPrimitive parameters angular cell × WithLp 2 (AnnularBoundary × LowEnergyBoundary))))))

def originalFProjection : OriginalStrongAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower :=
  (pairFirst (E := DivisionRow 1 lower) (F := DivisionRow 1 lower)).comp
    ((pairSecond (E := HighKnownGraphHilbert parameters lower) (F := WithLp 2 (DivisionRow 1 lower × DivisionRow 1 lower))).comp (pairFirst (E := WithLp 2 (HighKnownGraphHilbert parameters lower × WithLp 2 (DivisionRow 1 lower × DivisionRow 1 lower))) (F := WithLp 2 (HighBoundaryPrimitive parameters angular cell × WithLp 2 (AnnularBoundary × LowEnergyBoundary)))))

def originalGProjection : OriginalStrongAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower :=
  (pairSecond (E := DivisionRow 1 lower) (F := DivisionRow 1 lower)).comp
    ((pairSecond (E := HighKnownGraphHilbert parameters lower) (F := WithLp 2 (DivisionRow 1 lower × DivisionRow 1 lower))).comp (pairFirst (E := WithLp 2 (HighKnownGraphHilbert parameters lower × WithLp 2 (DivisionRow 1 lower × DivisionRow 1 lower))) (F := WithLp 2 (HighBoundaryPrimitive parameters angular cell × WithLp 2 (AnnularBoundary × LowEnergyBoundary)))))

def originalMeanResidual
    (row : OriginalStrongAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower) :
    OriginalStrongAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower :=
  ((meanFreeRow lower).restrictScalars ℝ - ContinuousLinearMap.id ℝ _).comp row

/-- Independent original strengthened AK20 carrier.  The two genuine AH
source graphs and all boundary coordinates are independent; only the three
original mean-free supports F2,f,g are imposed.  No weighted solution or
range-membership assumption occurs in this definition. -/
def OriginalStrongCarrier : Submodule ℝ (OriginalStrongAmbient parameters lower angular cell) :=
  (originalMeanResidual parameters lower angular cell (originalF2Projection parameters lower angular cell)).ker ⊓
    (originalMeanResidual parameters lower angular cell (originalFProjection parameters lower angular cell)).ker ⊓
    (originalMeanResidual parameters lower angular cell (originalGProjection parameters lower angular cell)).ker

theorem OriginalStrongCarrier_closed :
    IsClosed (OriginalStrongCarrier parameters lower angular cell :
      Set (OriginalStrongAmbient parameters lower angular cell)) :=
  ((originalMeanResidual parameters lower angular cell (originalF2Projection parameters lower angular cell)).isClosed_ker.inter
    (originalMeanResidual parameters lower angular cell (originalFProjection parameters lower angular cell)).isClosed_ker).inter
    (originalMeanResidual parameters lower angular cell (originalGProjection parameters lower angular cell)).isClosed_ker

instance originalStrongCarrierComplete : CompleteSpace (OriginalStrongCarrier parameters lower angular cell) :=
  (OriginalStrongCarrier_closed parameters lower angular cell).completeSpace_coe

theorem OriginalStrongCarrier.mean_free (data : OriginalStrongCarrier parameters lower angular cell) :
    (∀ mode : ℤ × ℤ, mode.1 = 0 →
      unweightedSourceF2Bulk parameters lower data.val.ofLp.1.ofLp.1.ofLp.2 mode = 0) ∧
    (∀ mode : ℤ × ℤ, mode.1 = 0 → data.val.ofLp.1.ofLp.2.ofLp.1 mode = 0) ∧
    (∀ mode : ℤ × ℤ, mode.1 = 0 → data.val.ofLp.1.ofLp.2.ofLp.2 mode = 0) := by
  have f2 := data.property.1.1
  have f := data.property.1.2
  have g := data.property.2
  change meanFreeRow lower (unweightedSourceF2Bulk parameters lower data.val.ofLp.1.ofLp.1.ofLp.2) -
    unweightedSourceF2Bulk parameters lower data.val.ofLp.1.ofLp.1.ofLp.2 = 0 at f2
  change meanFreeRow lower data.val.ofLp.1.ofLp.2.ofLp.1 - data.val.ofLp.1.ofLp.2.ofLp.1 = 0 at f
  change meanFreeRow lower data.val.ofLp.1.ofLp.2.ofLp.2 - data.val.ofLp.1.ofLp.2.ofLp.2 = 0 at g
  exact ⟨(meanFreeRow_fixed_iff lower _).mp (sub_eq_zero.mp f2),
    (meanFreeRow_fixed_iff lower _).mp (sub_eq_zero.mp f),
    (meanFreeRow_fixed_iff lower _).mp (sub_eq_zero.mp g)⟩

theorem divisionHighWeight_zero_mode (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : DivisionRow 1 lower) (mode : ℤ × ℤ) (zero : field mode = 0) :
    divisionHighWeight lower positive bounded field mode = 0 := by
  rw [divisionHighWeight_mode, zero, map_zero]

theorem divisionHighUnweight_zero_mode (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : DivisionRow 1 lower) (mode : ℤ × ℤ) (zero : field mode = 0) :
    divisionHighUnweight lower positive bounded field mode = 0 := by
  change scalarRadialMap lower (highPowerCurve lower highTiltExponent positive) 1
    (highPositivePower_bound lower positive bounded) (field mode) = 0
  rw [zero, map_zero]

theorem originalAngularDecode_relation (field : DivisionRow 1 lower) (mode : ℤ × ℤ) :
    sourceAngularBulk lower field mode = (Complex.I * (mode.1 : ℂ)) • originalAngularDecode lower field mode := by
  change ((Complex.I * (mode.1 : ℂ)) / ((1 + |(mode.1 : ℝ)| : ℝ) : ℂ)) • field mode =
    (Complex.I * (mode.1 : ℂ)) • ((((1 + |(mode.1 : ℝ)|)⁻¹ : ℝ) : ℂ) • field mode)
  rw [smul_smul, Complex.ofReal_inv, div_eq_mul_inv]

theorem strengthenedG_originalAngularDecode (field : DivisionRow 1 lower) :
    strengthenedG lower (originalAngularDecode lower field) (sourceAngularBulk lower field) = field := by
  apply lp.ext
  funext mode
  rw [strengthenedG_mode lower _ _ (originalAngularDecode_relation lower field)]
  change ((1 + |(mode.1 : ℝ)| : ℝ) : ℂ) •
    ((((1 + |(mode.1 : ℝ)|)⁻¹ : ℝ) : ℂ) • field mode) = field mode
  rw [smul_smul, Complex.ofReal_inv, mul_inv_cancel₀, one_smul]
  exact_mod_cast (ne_of_gt (show 0 < 1 + |(mode.1 : ℝ)| by positivity))

variable (length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < length)

theorem strongOriginalCoordinateMap_mem
    (data : StrongDataCarrier parameters lower positive bounded angular cell) :
    strongOriginalCoordinateMap parameters lower length positive bounded lengthPositive angular cell data ∈
      OriginalStrongCarrier parameters lower angular cell := by
  let original := strongOriginalCoordinateMap parameters lower length positive bounded lengthPositive angular cell data
  have mean := StrongDataCarrier.mean_free parameters lower positive bounded angular cell data
  have source := (weightedGraphCompatibility_iff_rows parameters lower positive bounded angular cell
    data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.1 data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.2
    data.val.ofLp.1.ofLp.1.ofLp.1).mp
      (StrongDataCarrier.compatibility parameters lower positive bounded angular cell data)
  have f2identity : divisionHighUnweight lower positive bounded (data.val.ofLp.1.ofLp.1.ofLp.1 2) =
      unweightedSourceF2Bulk parameters lower data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.2 := by
    rw [source.2.2, divisionHighUnweight_weight]
  have f2Mean : meanFreeRow lower (originalF2Projection parameters lower angular cell original) =
      originalF2Projection parameters lower angular cell original := by
    apply (meanFreeRow_fixed_iff lower _).mpr
    intro mode zero
    change unweightedSourceF2Bulk parameters lower data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.2 mode = 0
    rw [← f2identity]
    exact divisionHighUnweight_zero_mode lower positive bounded _ mode ((meanFreeRow_fixed_iff lower _).mp mean.1 mode zero)
  have fMean : meanFreeRow lower (originalFProjection parameters lower angular cell original) =
      originalFProjection parameters lower angular cell original := by
    apply (meanFreeRow_fixed_iff lower _).mpr
    intro mode zero
    exact divisionHighUnweight_zero_mode lower positive bounded _ mode ((meanFreeRow_fixed_iff lower _).mp mean.2.1 mode zero)
  have gMean : meanFreeRow lower (originalGProjection parameters lower angular cell original) =
      originalGProjection parameters lower angular cell original := by
    apply (meanFreeRow_fixed_iff lower _).mpr
    intro mode zero
    have gZero := (meanFreeRow_fixed_iff lower _).mp mean.2.2 mode zero
    change data.val.ofLp.1.ofLp.1.ofLp.2 0 mode = 0 at gZero
    have rgZero : data.val.ofLp.1.ofLp.1.ofLp.2 1 mode = 0 := by
      have relation := StrongDataCarrier.angular_relation parameters lower positive bounded angular cell data mode
      change data.val.ofLp.1.ofLp.1.ofLp.2 1 mode =
        (Complex.I * (mode.1 : ℂ)) • (data.val.ofLp.1.ofLp.1.ofLp.2 0 mode) at relation
      simpa only [zero, Int.cast_zero, mul_zero, zero_smul] using relation
    change divisionHighUnweight lower positive bounded (data.val.ofLp.1.ofLp.1.ofLp.2 0) mode +
      angularRecoverySymbol mode • divisionHighUnweight lower positive bounded (data.val.ofLp.1.ofLp.1.ofLp.2 1) mode = 0
    rw [divisionHighUnweight_zero_mode lower positive bounded _ mode gZero,
      divisionHighUnweight_zero_mode lower positive bounded _ mode rgZero, smul_zero, add_zero]
  exact ⟨⟨sub_eq_zero.mpr f2Mean,sub_eq_zero.mpr fMean⟩,sub_eq_zero.mpr gMean⟩

def strongToOriginal : StrongDataCarrier parameters lower positive bounded angular cell →L[ℝ]
    OriginalStrongCarrier parameters lower angular cell :=
  (strongOriginalCoordinateMap parameters lower length positive bounded lengthPositive angular cell).codRestrict
    (OriginalStrongCarrier parameters lower angular cell)
    (strongOriginalCoordinateMap_mem parameters lower angular cell length positive bounded lengthPositive)

end Grad.AnnularStrongData

import AIY1FullStrongDataAmbient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularStrongData
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceCollarFullSource Grad.AnnularSourceGraph Grad.AnnularVariational
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource Grad.AnnularKnownLow Grad.AnnularLowEnergy

variable (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell : ℕ)

def strongMeanResidual
    (row : ActualHighKnownAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower) :
    StrongDataAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower :=
  (((meanFreeRow lower).restrictScalars ℝ - ContinuousLinearMap.id ℝ _).comp row).comp
    (strongSharedProjection parameters lower angular cell)

def strongZeroResidual :
    StrongDataAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower :=
  (highKnownWeightedRqv parameters lower angular cell).comp
    (strongSharedProjection parameters lower angular cell)

/-- Complete original BF4 strong datum.  Its source pair is shared exactly
once, `F2,f,g` are mean free, `Rg` is the actual angular graph coordinate,
and both incoming coordinates and the physical high outer datum are retained.
The spare bulk coordinate is zero and has no physical meaning. -/
def StrongDataCarrier : Submodule ℝ (StrongDataAmbient parameters lower angular cell) :=
  (highKnownCompatibilityCarrier parameters lower positive bounded angular cell).comap
      (strongSharedProjection parameters lower angular cell).toLinearMap ⊓
    (strongAngularCarrier parameters lower angular cell) ⊓
    (strongMeanResidual parameters lower angular cell
      (highKnownWeightedF2 parameters lower angular cell)).ker ⊓
    (strongMeanResidual parameters lower angular cell
      (highKnownWeightedF parameters lower angular cell)).ker ⊓
    (strongMeanResidual parameters lower angular cell
      (highKnownWeightedG parameters lower angular cell)).ker ⊓
    (strongZeroResidual parameters lower angular cell).ker

theorem StrongDataCarrier_closed :
    IsClosed (StrongDataCarrier parameters lower positive bounded angular cell :
      Set (StrongDataAmbient parameters lower angular cell)) := by
  exact (((((highKnownCompatibilityCarrier_closed parameters lower positive bounded angular cell).preimage
      (strongSharedProjection parameters lower angular cell).continuous).inter
      (strongAngularCarrier_closed parameters lower angular cell)).inter
      (strongMeanResidual parameters lower angular cell
        (highKnownWeightedF2 parameters lower angular cell)).isClosed_ker).inter
      (strongMeanResidual parameters lower angular cell
        (highKnownWeightedF parameters lower angular cell)).isClosed_ker).inter
      (strongMeanResidual parameters lower angular cell
        (highKnownWeightedG parameters lower angular cell)).isClosed_ker |>.inter
      (strongZeroResidual parameters lower angular cell).isClosed_ker

instance strongDataCarrierComplete :
    CompleteSpace (StrongDataCarrier parameters lower positive bounded angular cell) :=
  (StrongDataCarrier_closed parameters lower positive bounded angular cell).completeSpace_coe

theorem StrongDataCarrier.compatibility
    (data : StrongDataCarrier parameters lower positive bounded angular cell) :
    WeightedGraphCompatibility parameters lower (angular + cell)
      (highKnownF0GraphProjection parameters lower angular cell data.val.ofLp.1,
        highKnownF2GraphProjection parameters lower angular cell data.val.ofLp.1)
      (highKnownWeightedProjection parameters lower angular cell data.val.ofLp.1) :=
  (highKnownCompatibilityCarrier_mem_iff parameters lower positive bounded angular cell
    data.val.ofLp.1).mp data.property.1.1.1.1.1

theorem StrongDataCarrier.angular_relation
    (data : StrongDataCarrier parameters lower positive bounded angular cell) :
    ∀ mode : ℤ × ℤ,
      highKnownWeightedQc parameters lower angular cell data.val.ofLp.1 mode =
        (Complex.I * (mode.1 : ℂ)) •
          highKnownWeightedG parameters lower angular cell data.val.ofLp.1 mode :=
  (strongAngularCarrier_mem_iff parameters lower angular cell data.val).mp
    data.property.1.1.1.1.2

theorem StrongDataCarrier.mean_free
    (data : StrongDataCarrier parameters lower positive bounded angular cell) :
    meanFreeRow lower (highKnownWeightedF2 parameters lower angular cell data.val.ofLp.1) =
      highKnownWeightedF2 parameters lower angular cell data.val.ofLp.1 ∧
    meanFreeRow lower (highKnownWeightedF parameters lower angular cell data.val.ofLp.1) =
      highKnownWeightedF parameters lower angular cell data.val.ofLp.1 ∧
    meanFreeRow lower (highKnownWeightedG parameters lower angular cell data.val.ofLp.1) =
      highKnownWeightedG parameters lower angular cell data.val.ofLp.1 := by
  have first := data.property.1.1.1.2
  have second := data.property.1.1.2
  have third := data.property.1.2
  change meanFreeRow lower (highKnownWeightedF2 parameters lower angular cell data.val.ofLp.1) -
    highKnownWeightedF2 parameters lower angular cell data.val.ofLp.1 = 0 at first
  change meanFreeRow lower (highKnownWeightedF parameters lower angular cell data.val.ofLp.1) -
    highKnownWeightedF parameters lower angular cell data.val.ofLp.1 = 0 at second
  change meanFreeRow lower (highKnownWeightedG parameters lower angular cell data.val.ofLp.1) -
    highKnownWeightedG parameters lower angular cell data.val.ofLp.1 = 0 at third
  exact ⟨sub_eq_zero.mp first, sub_eq_zero.mp second, sub_eq_zero.mp third⟩

theorem StrongDataCarrier.spare_zero
    (data : StrongDataCarrier parameters lower positive bounded angular cell) :
    highKnownWeightedRqv parameters lower angular cell data.val.ofLp.1 = 0 :=
  data.property.2

/-- Genuine angular relation in radial L2 representatives of the same
weighted physical datum.  Its generator is `R`, not a radial derivative. -/
theorem StrongDataCarrier.angular_ae
    (data : StrongDataCarrier parameters lower positive bounded angular cell) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      highKnownWeightedQc parameters lower angular cell data.val.ofLp.1 mode radius =
        (Complex.I * (mode.1 : ℂ)) •
          highKnownWeightedG parameters lower angular cell data.val.ofLp.1 mode radius := by
  rw [ae_all_iff]
  intro mode
  rw [StrongDataCarrier.angular_relation parameters lower positive bounded angular cell data mode]
  exact Lp.coeFn_smul _ _

end Grad.AnnularStrongData

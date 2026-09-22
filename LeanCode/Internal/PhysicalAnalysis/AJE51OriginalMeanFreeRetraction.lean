import AJE50GenuineSmoothRadialDensity
import AJE43CompleteStrongFiniteApproximation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open Set Filter
open scoped Topology BigOperators
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarFullSource Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularLowEnergy

local instance originalAmbientRealNormed (parameters : PhaseParameters) (lower : ℝ) :
    NormedSpace ℝ (OriginalStrongAmbient parameters lower 0 0) := by
  letI : NormedSpace ℝ (HighKnownGraphHilbert parameters lower) := inferInstance
  letI : NormedSpace ℝ (WithLp 2 (DivisionRow 1 lower × DivisionRow 1 lower)) := inferInstance
  letI : NormedSpace ℝ (WithLp 2 (HighKnownGraphHilbert parameters lower × WithLp 2 (DivisionRow 1 lower × DivisionRow 1 lower))) := inferInstance
  letI : NormedSpace ℝ (WithLp 2 (AnnularBoundary × LowEnergyBoundary)) := inferInstance
  letI : NormedSpace ℝ (WithLp 2 (HighBoundaryPrimitive parameters 0 0 × WithLp 2 (AnnularBoundary × LowEnergyBoundary))) := inferInstance
  exact inferInstance

section Mask
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sourceMeanFreeLp : lp (fun _ : ℤ × ℤ => E) 2 →L[ℝ] lp (fun _ : ℤ × ℤ => E) 2 :=
  lpTwoMap (fun mode => if mode.1 = 0 then 0 else ContinuousLinearMap.id ℝ E) 1 zero_le_one
    (fun mode field => by split_ifs <;> simp)

theorem sourceMeanFreeLp_apply (field : lp (fun _ : ℤ × ℤ => E) 2) (mode : ℤ × ℤ) :
    sourceMeanFreeLp field mode = if mode.1 = 0 then 0 else field mode := by
  change (if mode.1 = 0 then (0 : E →L[ℝ] E) else ContinuousLinearMap.id ℝ E) (field mode) = _
  split_ifs <;> rfl

theorem sourceMeanFreeLp_bound (field : lp (fun _ : ℤ × ℤ => E) 2) : ‖sourceMeanFreeLp field‖ ≤ ‖field‖ := by
  apply lp.norm_mono (by norm_num)
  intro mode
  rw [sourceMeanFreeLp_apply]
  split_ifs <;> simp

theorem sourceMeanFreeLp_fixed (field : lp (fun _ : ℤ × ℤ => E) 2)
    (mean : ∀ mode : ℤ × ℤ, mode.1 = 0 → field mode = 0) : sourceMeanFreeLp field = field := by
  apply lp.ext
  funext mode
  rw [sourceMeanFreeLp_apply]
  split_ifs with zero
  · exact (mean mode zero).symm
  · rfl

def meanFreeSourceContraction : SourceContraction (lp (fun _ : ℤ × ℤ => E) 2) :=
  ⟨sourceMeanFreeLp,sourceMeanFreeLp_bound⟩
end Mask

def identitySourceContraction (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : SourceContraction E :=
  ⟨ContinuousLinearMap.id ℝ E,fun _ => le_rfl⟩

theorem sourceHilbertPairMap_fixed {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (first : E →L[ℝ] E) (second : F →L[ℝ] F)
    (data : WithLp 2 (E × F)) (firstFixed : first data.ofLp.1 = data.ofLp.1)
    (secondFixed : second data.ofLp.2 = data.ofLp.2) : sourceHilbertPairMap first second data = data := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ E F).injective
  exact Prod.ext firstFixed secondFixed

variable (parameters : PhaseParameters) (lower : ℝ)

def originalMeanFreeContraction : SourceContraction (OriginalStrongAmbient parameters lower 0 0) :=
  (((identitySourceContraction (HighF0SourceGraph parameters lower)).pair meanFreeSourceContraction).pair
    (meanFreeSourceContraction.pair meanFreeSourceContraction)).pair
      (identitySourceContraction (WithLp 2 (HighBoundaryPrimitive parameters 0 0 × WithLp 2 (AnnularBoundary × LowEnergyBoundary))))

def originalMeanFreeAmbient : OriginalStrongAmbient parameters lower 0 0 →L[ℝ] OriginalStrongAmbient parameters lower 0 0 :=
  (originalMeanFreeContraction parameters lower).mapping

theorem originalMeanFreeAmbient_mem (data : OriginalStrongAmbient parameters lower 0 0) :
    originalMeanFreeAmbient parameters lower data ∈ OriginalStrongCarrier parameters lower 0 0 := by
  have f2Mean : meanFreeRow lower (originalF2Projection parameters lower 0 0 (originalMeanFreeAmbient parameters lower data)) =
      originalF2Projection parameters lower 0 0 (originalMeanFreeAmbient parameters lower data) := by
    apply (meanFreeRow_fixed_iff lower _).mpr
    intro mode zero
    change weightedRadialCoordinate 1 lower 0 (sourceMeanFreeLp data.ofLp.1.ofLp.1.ofLp.2 mode) = 0
    rw [sourceMeanFreeLp_apply,if_pos zero,map_zero]
  have fMean : meanFreeRow lower (originalFProjection parameters lower 0 0 (originalMeanFreeAmbient parameters lower data)) =
      originalFProjection parameters lower 0 0 (originalMeanFreeAmbient parameters lower data) := by
    apply (meanFreeRow_fixed_iff lower _).mpr
    intro mode zero
    change sourceMeanFreeLp data.ofLp.1.ofLp.2.ofLp.1 mode = 0
    rw [sourceMeanFreeLp_apply,if_pos zero]
  have gMean : meanFreeRow lower (originalGProjection parameters lower 0 0 (originalMeanFreeAmbient parameters lower data)) =
      originalGProjection parameters lower 0 0 (originalMeanFreeAmbient parameters lower data) := by
    apply (meanFreeRow_fixed_iff lower _).mpr
    intro mode zero
    change sourceMeanFreeLp data.ofLp.1.ofLp.2.ofLp.2 mode = 0
    rw [sourceMeanFreeLp_apply,if_pos zero]
  exact ⟨⟨sub_eq_zero.mpr f2Mean,sub_eq_zero.mpr fMean⟩,sub_eq_zero.mpr gMean⟩

def originalMeanFreeRetraction : OriginalStrongAmbient parameters lower 0 0 →L[ℝ] OriginalStrongCarrier parameters lower 0 0 :=
  (originalMeanFreeAmbient parameters lower).codRestrict (OriginalStrongCarrier parameters lower 0 0)
    (originalMeanFreeAmbient_mem parameters lower)

/-- Vanishing F2 bulk really forces the SAME full radial source graph to
vanish, including its derivative and both traces. -/
theorem originalStrongF2Graph_meanFree (positive : 0 < lower) (bounded : lower ≤ 1)
    (data : OriginalStrongCarrier parameters lower 0 0) (mode : ℤ × ℤ) (zero : mode.1 = 0) :
    data.val.ofLp.1.ofLp.1.ofLp.2 mode = 0 := by
  apply weightedRadial_value_injective 1 lower positive bounded
  rw [map_zero]
  exact (OriginalStrongCarrier.mean_free parameters lower 0 0 data).1 mode zero

theorem originalMeanFreeRetraction_fixed (positive : 0 < lower) (bounded : lower ≤ 1)
    (data : OriginalStrongCarrier parameters lower 0 0) : originalMeanFreeRetraction parameters lower data.val = data := by
  apply Subtype.ext
  apply sourceHilbertPairMap_fixed
  · apply sourceHilbertPairMap_fixed
    · apply sourceHilbertPairMap_fixed
      · rfl
      · exact sourceMeanFreeLp_fixed _ (originalStrongF2Graph_meanFree parameters lower positive bounded data)
    · apply sourceHilbertPairMap_fixed
      · exact sourceMeanFreeLp_fixed _ (OriginalStrongCarrier.mean_free parameters lower 0 0 data).2.1
      · exact sourceMeanFreeLp_fixed _ (OriginalStrongCarrier.mean_free parameters lower 0 0 data).2.2
  · rfl

theorem originalMeanFreeRetraction_surjective (positive : 0 < lower) (bounded : lower ≤ 1) :
    Function.Surjective (originalMeanFreeRetraction parameters lower) :=
  fun data => ⟨data.val,originalMeanFreeRetraction_fixed parameters lower positive bounded data⟩

end Grad.AnnularStrongOrbit

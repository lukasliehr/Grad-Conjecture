import JCInterface

noncomputable section

open MeasureTheory Filter Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue FieldL2)
open scoped Topology BigOperators

namespace Grad.WeightedJets.CellCutoff

theorem fieldCutoff_coordinate (dimension : ℕ) (domain : Set Spatial) (cells : Finset ℤ)
    (field : FieldL2 dimension domain) :
    ∀ᵐ point ∂volume.restrict domain, ∀ cell : ℤ,
      fieldCutoff dimension domain cells field point cell = if cell ∈ cells then field point cell else 0 :=
  Grad.CellProjections.Generic.field_projection_coordinate (PhysicalValue dimension) (volume.restrict domain) cells field

theorem fieldCutoff_inverse (dimension : ℕ) (domain : Set Spatial) (cells : Finset ℤ)
    (weight : ℕ) (field : FieldL2 dimension domain) :
    Grad.CellWeights.inverseFieldCLM dimension domain weight (fieldCutoff dimension domain cells field) =
      fieldCutoff dimension domain cells (Grad.CellWeights.inverseFieldCLM dimension domain weight field) := by
  apply Lp.ext
  filter_upwards [Grad.CellWeights.inverseFieldCLM_coordinate dimension domain weight
      (fieldCutoff dimension domain cells field),
    fieldCutoff_coordinate dimension domain cells (Grad.CellWeights.inverseFieldCLM dimension domain weight field),
    fieldCutoff_coordinate dimension domain cells field,
    Grad.CellWeights.inverseFieldCLM_coordinate dimension domain weight field] with point inverse projected original weighted
  apply lp.ext
  funext cell
  rw [inverse cell, projected cell, original cell, weighted cell]
  split_ifs <;> simp

theorem pairing_cutoff (dimension : ℕ) (domain : Set Spatial) (cells : Finset ℤ) (cell : ℤ)
    (vector : PhysicalValue dimension) (test : Spatial → ℝ)
    (membership : MemLp test 2 (volume.restrict domain)) (field : FieldL2 dimension domain) :
    Grad.WeakTesting.pairingOfMemLp dimension domain cell vector test membership
        (fieldCutoff dimension domain cells field) =
      if cell ∈ cells then Grad.WeakTesting.pairingOfMemLp dimension domain cell vector test membership field else 0 := by
  rw [Grad.WeakTesting.pairingOfMemLp_apply, Grad.WeakTesting.pairingOfMemLp_apply]
  by_cases inside : cell ∈ cells
  · rw [if_pos inside]
    apply integral_congr_ae
    filter_upwards [fieldCutoff_coordinate dimension domain cells field] with point coordinates
    rw [coordinates cell, if_pos inside]
  · rw [if_neg inside]
    calc
      _ = ∫ _point in domain, (0 : ℂ) := by
        apply integral_congr_ae
        filter_upwards [fieldCutoff_coordinate dimension domain cells field] with point coordinates
        rw [coordinates cell, if_neg inside, inner_zero_right, smul_zero]
      _ = 0 := integral_zero _ _

theorem testPairing_cutoff (dimension : ℕ) (domain : Set Spatial) (cells : Finset ℤ) (cell : ℤ)
    (vector : PhysicalValue dimension) (test : TestFunction domain) (field : FieldL2 dimension domain) :
    testPairing dimension domain cell vector test (fieldCutoff dimension domain cells field) =
      if cell ∈ cells then testPairing dimension domain cell vector test field else 0 :=
  pairing_cutoff dimension domain cells cell vector test.toFun _ field

theorem derivativeTestPairing_cutoff (dimension order : ℕ) (domain : Set Spatial) (cells : Finset ℤ)
    (index : JetIndex order) (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction domain)
    (field : FieldL2 dimension domain) :
    derivativeTestPairing dimension order domain index cell vector test (fieldCutoff dimension domain cells field) =
      if cell ∈ cells then derivativeTestPairing dimension order domain index cell vector test field else 0 :=
  pairing_cutoff dimension domain cells cell vector _ _ field

theorem cutoffTuple_base (dimension order : ℕ) (domain : Set Spatial) (cells : Finset ℤ)
    (exponent : JetIndex order → ℕ) (tuple : JetTuple dimension order domain) :
    ambientBase dimension order domain exponent (cutoffTuple dimension order domain cells tuple) =
      fieldCutoff dimension domain cells (ambientBase dimension order domain exponent tuple) :=
  fieldCutoff_inverse dimension domain cells (exponent (zeroIndex order)) (tuple (zeroIndex order))

theorem cutoffTuple_mem (dimension order : ℕ) (domain : Set Spatial) (cells : Finset ℤ)
    (exponent : JetIndex order → ℕ) (tuple : JetTuple dimension order domain)
    (membership : tuple ∈ jetGraph dimension order domain exponent) :
    cutoffTuple dimension order domain cells tuple ∈ jetGraph dimension order domain exponent := by
  apply (jetGraph_mem dimension order domain exponent _).mpr
  intro index cell vector test
  change testPairing dimension domain cell vector test (fieldCutoff dimension domain cells (tuple index)) = _
  rw [testPairing_cutoff, cutoffTuple_base, derivativeTestPairing_cutoff]
  by_cases inside : cell ∈ cells
  · simpa only [if_pos inside] using (jetGraph_mem dimension order domain exponent tuple).mp membership index cell vector test
  · simp only [if_neg inside, mul_zero]

theorem cutoffTuple_norm_le (dimension order : ℕ) (domain : Set Spatial) (cells : Finset ℤ)
    (tuple : JetTuple dimension order domain) : ‖cutoffTuple dimension order domain cells tuple‖ ≤ ‖tuple‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [tuple_norm_sq, tuple_norm_sq]
  apply Finset.sum_le_sum
  intro index _membership
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (Grad.CellProjections.Generic.field_projection_norm_apply (PhysicalValue dimension) (volume.restrict domain) cells (tuple index))

def cutoffLinear (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (cells : Finset ℤ) : WJet dimension order domain exponent →ₗ[ℂ] WJet dimension order domain exponent where
  toFun jet := ⟨cutoffTuple dimension order domain cells jet.val,
    cutoffTuple_mem dimension order domain cells exponent jet.val jet.property⟩
  map_add' first second := by
    apply jet_eq
    intro index
    exact map_add (fieldCutoff dimension domain cells) (first.val index) (second.val index)
  map_smul' scalar jet := by
    apply jet_eq
    intro index
    exact map_smul (fieldCutoff dimension domain cells) scalar (jet.val index)

def cutoff (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (cells : Finset ℤ) : WJet dimension order domain exponent →L[ℂ] WJet dimension order domain exponent :=
  (cutoffLinear dimension order domain exponent cells).mkContinuous 1 (fun jet => by
    change ‖cutoffTuple dimension order domain cells jet.val‖ ≤ 1 * ‖jet.val‖
    simpa only [one_mul] using cutoffTuple_norm_le dimension order domain cells jet.val)

theorem cutoff_apply (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (cells : Finset ℤ) (jet : WJet dimension order domain exponent) :
    (cutoff dimension order domain exponent cells jet).val = cutoffTuple dimension order domain cells jet.val := rfl

theorem cutoff_base (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (cells : Finset ℤ) (jet : WJet dimension order domain exponent) :
    base dimension order domain exponent (cutoff dimension order domain exponent cells jet) =
      fieldCutoff dimension domain cells (base dimension order domain exponent jet) :=
  cutoffTuple_base dimension order domain cells exponent jet.val

theorem cutoff_norm_le (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (cells : Finset ℤ) (jet : WJet dimension order domain exponent) :
    ‖cutoff dimension order domain exponent cells jet‖ ≤ ‖jet‖ :=
  cutoffTuple_norm_le dimension order domain cells jet.val

theorem cutoff_opNorm_le (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (cells : Finset ℤ) : ‖cutoff dimension order domain exponent cells‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro jet
  simpa only [one_mul] using cutoff_norm_le dimension order domain exponent cells jet

theorem cutoff_idempotent (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (cells : Finset ℤ) (jet : WJet dimension order domain exponent) :
    cutoff dimension order domain exponent cells (cutoff dimension order domain exponent cells jet) =
      cutoff dimension order domain exponent cells jet := by
  apply jet_eq
  intro index
  exact Grad.CellProjections.Generic.field_projection_idempotent (PhysicalValue dimension) (volume.restrict domain) cells (jet.val index)

theorem cutoff_finite (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (cells : Finset ℤ) (jet : WJet dimension order domain exponent) :
    FiniteCellJet dimension order domain exponent (cutoff dimension order domain exponent cells jet) := by
  refine ⟨cells, fun index => ?_⟩
  filter_upwards [fieldCutoff_coordinate dimension domain cells (jet.val index)] with point coordinates cell outside
  exact (coordinates cell).trans (if_neg outside)

theorem cutoffTuple_strong (dimension order : ℕ) (domain : Set Spatial) (tuple : JetTuple dimension order domain) :
    Tendsto (fun cells : Finset ℤ => cutoffTuple dimension order domain cells tuple) atTop (𝓝 tuple) := by
  apply (PiLp.continuous_toLp 2 (fun _ : JetIndex order => FieldL2 dimension domain)).continuousAt.tendsto.comp
  exact tendsto_pi_nhds.mpr (fun index =>
    Grad.CellProjections.Generic.field_strong (volume.restrict domain) (PhysicalValue dimension) (tuple index))

theorem cutoff_strong (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (jet : WJet dimension order domain exponent) :
    Tendsto (fun cells : Finset ℤ => cutoff dimension order domain exponent cells jet) atTop (𝓝 jet) := by
  apply tendsto_subtype_rng.mpr
  exact cutoffTuple_strong dimension order domain jet.val

theorem finiteCellJet_dense (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ) :
    Dense {jet : WJet dimension order domain exponent | FiniteCellJet dimension order domain exponent jet} := by
  intro jet
  apply isClosed_closure.mem_of_tendsto (cutoff_strong dimension order domain exponent jet)
  exact Eventually.of_forall (fun cells => subset_closure (cutoff_finite dimension order domain exponent cells jet))

theorem constructor_consumer : ConstructorGoal := by
  intro dimension order domain exponent
  refine ⟨cutoff dimension order domain exponent, ?_, cutoff_opNorm_le dimension order domain exponent,
    cutoff_strong dimension order domain exponent⟩
  intro cells jet
  exact ⟨cutoff_apply dimension order domain exponent cells jet, cutoff_base dimension order domain exponent cells jet,
    cutoff_norm_le dimension order domain exponent cells jet, cutoff_idempotent dimension order domain exponent cells jet,
    cutoff_finite dimension order domain exponent cells jet⟩

theorem block_consumer : BlockGoal := ⟨constructor_consumer, finiteCellJet_dense⟩

end Grad.WeightedJets.CellCutoff

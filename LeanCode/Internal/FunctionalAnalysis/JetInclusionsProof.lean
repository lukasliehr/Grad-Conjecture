import JetInclusionsInterface

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue FieldL2)
open scoped BigOperators ContDiff

namespace Grad.WeightedJets.Inclusions

theorem indexInclusion_injective {lower higher : ℕ} (bound : lower ≤ higher) :
    Function.Injective (indexInclusion bound) := by
  intro first second equality
  apply Subtype.ext
  exact congrArg (fun index : JetIndex higher => index.val) equality

theorem indexInclusion_zero {lower higher : ℕ} (bound : lower ≤ higher) :
    indexInclusion bound (zeroIndex lower) = zeroIndex higher := rfl

theorem inverse_norm_le (dimension : ℕ) (domain : Set Spatial) (gap : ℕ) (field : FieldL2 dimension domain) :
    ‖Grad.CellWeights.inverseFieldCLM dimension domain gap field‖ ≤ ‖field‖ := by
  calc
    _ ≤ ‖Grad.CellWeights.inverseFieldCLM dimension domain gap‖ * ‖field‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖field‖ := mul_le_mul_of_nonneg_right
      (Grad.CellWeights.inverseFieldCLM_norm_le dimension domain gap) (norm_nonneg field)
    _ = ‖field‖ := one_mul _

theorem selected_sum_le (dimension lower higher : ℕ) (domain : Set Spatial) (bound : lower ≤ higher)
    (tuple : JetTuple dimension higher domain) :
    (∑ index : JetIndex lower, ‖tuple (indexInclusion bound index)‖ ^ 2) ≤ ∑ index : JetIndex higher, ‖tuple index‖ ^ 2 := by
  classical
  calc
    _ = ∑ index ∈ Finset.univ.image (indexInclusion bound), ‖tuple index‖ ^ 2 := by
      rw [Finset.sum_image]
      intro first _first second _second equality
      exact indexInclusion_injective bound equality
    _ ≤ ∑ index : JetIndex higher, ‖tuple index‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun index _inside _outside => sq_nonneg ‖tuple index‖)

theorem shiftedTuple_norm_le (dimension lower higher : ℕ) (domain : Set Spatial) (gap : ℕ) (bound : lower ≤ higher)
    (tuple : JetTuple dimension higher domain) : ‖shiftedTuple dimension lower higher domain gap bound tuple‖ ≤ ‖tuple‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [tuple_norm_sq, tuple_norm_sq]
  calc
    _ ≤ ∑ index : JetIndex lower, ‖tuple (indexInclusion bound index)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro index _inside
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
        (inverse_norm_le dimension domain gap (tuple (indexInclusion bound index)))
    _ ≤ _ := selected_sum_le dimension lower higher domain bound tuple

theorem pairing_inverse (dimension : ℕ) (domain : Set Spatial) (gap : ℕ) (cell : ℤ)
    (vector : PhysicalValue dimension) (test : Spatial → ℝ) (membership : MemLp test 2 (volume.restrict domain))
    (field : FieldL2 dimension domain) :
    Grad.WeakTesting.pairingOfMemLp dimension domain cell vector test membership
        (Grad.CellWeights.inverseFieldCLM dimension domain gap field) =
      Grad.CellWeights.inverseFactor gap cell * Grad.WeakTesting.pairingOfMemLp dimension domain cell vector test membership field := by
  rw [Grad.WeakTesting.pairingOfMemLp_apply, Grad.WeakTesting.pairingOfMemLp_apply]
  calc
    _ = ∫ point in domain, Grad.CellWeights.inverseFactor gap cell • (test point • inner ℂ vector (field point cell)) := by
      apply integral_congr_ae
      filter_upwards [Grad.CellWeights.inverseFieldCLM_coordinate dimension domain gap field] with point coordinates
      rw [coordinates cell, inner_smul_right]
      exact smul_comm (test point) (Grad.CellWeights.inverseFactor gap cell) (inner ℂ vector (field point cell))
    _ = _ := integral_smul _ _

theorem testPairing_inverse (dimension : ℕ) (domain : Set Spatial) (gap : ℕ) (cell : ℤ)
    (vector : PhysicalValue dimension) (test : TestFunction domain) (field : FieldL2 dimension domain) :
    testPairing dimension domain cell vector test (Grad.CellWeights.inverseFieldCLM dimension domain gap field) =
      Grad.CellWeights.inverseFactor gap cell * testPairing dimension domain cell vector test field :=
  pairing_inverse dimension domain gap cell vector test.toFun _ field

theorem inverseFactor_positiveFactor (lower gap : ℕ) (cell : ℤ) :
    Grad.CellWeights.inverseFactor gap cell * Grad.CellWeights.positiveFactor (lower + gap) cell =
      Grad.CellWeights.positiveFactor lower cell := by
  unfold Grad.CellWeights.inverseFactor Grad.CellWeights.positiveFactor
  rw [pow_add]
  have nonzero : (Grad.CellWeights.cellWeight cell : ℂ) ^ gap ≠ 0 :=
    pow_ne_zero gap (Complex.ofReal_ne_zero.mpr (Grad.CellWeights.cellWeight_pos cell).ne')
  calc
    _ = (Grad.CellWeights.cellWeight cell : ℂ) ^ lower *
        (((Grad.CellWeights.cellWeight cell : ℂ) ^ gap)⁻¹ * (Grad.CellWeights.cellWeight cell : ℂ) ^ gap) := by ring
    _ = _ := by rw [inv_mul_cancel₀ nonzero, mul_one]

theorem shiftedTuple_base (dimension lower higher : ℕ) (domain : Set Spatial) (gap : ℕ) (bound : lower ≤ higher)
    (source : JetIndex higher → ℕ) (target : JetIndex lower → ℕ) (compatible : Compatible bound gap source target)
    (tuple : JetTuple dimension higher domain) :
    ambientBase dimension lower domain target (shiftedTuple dimension lower higher domain gap bound tuple) =
      ambientBase dimension higher domain source tuple := by
  have composition := congrArg (fun mapping : FieldL2 dimension domain →L[ℂ] FieldL2 dimension domain =>
    mapping (tuple (zeroIndex higher)))
    (Grad.CellWeights.inverseFieldCLM_comp dimension domain (target (zeroIndex lower)) gap)
  have zeroCompatibility := compatible (zeroIndex lower)
  rw [indexInclusion_zero] at zeroCompatibility
  change Grad.CellWeights.inverseFieldCLM dimension domain (target (zeroIndex lower))
    (Grad.CellWeights.inverseFieldCLM dimension domain gap (tuple (zeroIndex higher))) =
      Grad.CellWeights.inverseFieldCLM dimension domain (source (zeroIndex higher)) (tuple (zeroIndex higher))
  simpa only [ContinuousLinearMap.comp_apply, zeroCompatibility] using composition

theorem shiftedTuple_mem (dimension lower higher : ℕ) (domain : Set Spatial) (gap : ℕ) (bound : lower ≤ higher)
    (source : JetIndex higher → ℕ) (target : JetIndex lower → ℕ) (compatible : Compatible bound gap source target)
    (tuple : JetTuple dimension higher domain) (membership : tuple ∈ jetGraph dimension higher domain source) :
    shiftedTuple dimension lower higher domain gap bound tuple ∈ jetGraph dimension lower domain target := by
  apply (jetGraph_mem dimension lower domain target _).mpr
  intro index cell vector test
  change testPairing dimension domain cell vector test
    (Grad.CellWeights.inverseFieldCLM dimension domain gap (tuple (indexInclusion bound index))) = _
  rw [testPairing_inverse,
    (jetGraph_mem dimension higher domain source tuple).mp membership (indexInclusion bound index) cell vector test,
    shiftedTuple_base dimension lower higher domain gap bound source target compatible tuple, ← compatible index]
  change Grad.CellWeights.inverseFactor gap cell *
      (((-1 : ℂ) ^ degree index * Grad.CellWeights.positiveFactor (target index + gap) cell) *
        derivativeTestPairing dimension lower domain index cell vector test (ambientBase dimension higher domain source tuple)) = _
  calc
    _ = ((-1 : ℂ) ^ degree index *
        (Grad.CellWeights.inverseFactor gap cell * Grad.CellWeights.positiveFactor (target index + gap) cell)) *
      derivativeTestPairing dimension lower domain index cell vector test (ambientBase dimension higher domain source tuple) := by ring
    _ = _ := by rw [inverseFactor_positiveFactor]

def inclusionLinear (dimension lower higher : ℕ) (domain : Set Spatial) (gap : ℕ) (bound : lower ≤ higher)
    (source : JetIndex higher → ℕ) (target : JetIndex lower → ℕ) (compatible : Compatible bound gap source target) :
    WJet dimension higher domain source →ₗ[ℂ] WJet dimension lower domain target where
  toFun jet := ⟨shiftedTuple dimension lower higher domain gap bound jet.val,
    shiftedTuple_mem dimension lower higher domain gap bound source target compatible jet.val jet.property⟩
  map_add' first second := by
    apply Subtype.ext
    apply PiLp.ext
    intro index
    exact (Grad.CellWeights.inverseFieldCLM dimension domain gap).map_add _ _
  map_smul' scalar jet := by
    apply Subtype.ext
    apply PiLp.ext
    intro index
    exact (Grad.CellWeights.inverseFieldCLM dimension domain gap).map_smul scalar _

def inclusion (dimension lower higher : ℕ) (domain : Set Spatial) (gap : ℕ) (bound : lower ≤ higher)
    (source : JetIndex higher → ℕ) (target : JetIndex lower → ℕ) (compatible : Compatible bound gap source target) :
    WJet dimension higher domain source →L[ℂ] WJet dimension lower domain target :=
  (inclusionLinear dimension lower higher domain gap bound source target compatible).mkContinuous 1 (fun jet => by
    change ‖shiftedTuple dimension lower higher domain gap bound jet.val‖ ≤ 1 * ‖jet.val‖
    simpa only [one_mul] using shiftedTuple_norm_le dimension lower higher domain gap bound jet.val)

theorem inclusion_coordinates (dimension lower higher : ℕ) (domain : Set Spatial) (gap : ℕ) (bound : lower ≤ higher)
    (source : JetIndex higher → ℕ) (target : JetIndex lower → ℕ) (compatible : Compatible bound gap source target)
    (jet : WJet dimension higher domain source) :
    (inclusion dimension lower higher domain gap bound source target compatible jet).val =
      shiftedTuple dimension lower higher domain gap bound jet.val := rfl

theorem inclusion_base (dimension lower higher : ℕ) (domain : Set Spatial) (gap : ℕ) (bound : lower ≤ higher)
    (source : JetIndex higher → ℕ) (target : JetIndex lower → ℕ) (compatible : Compatible bound gap source target)
    (jet : WJet dimension higher domain source) :
    base dimension lower domain target (inclusion dimension lower higher domain gap bound source target compatible jet) =
      base dimension higher domain source jet :=
  shiftedTuple_base dimension lower higher domain gap bound source target compatible jet.val

theorem inclusion_opNorm_le (dimension lower higher : ℕ) (domain : Set Spatial) (gap : ℕ) (bound : lower ≤ higher)
    (source : JetIndex higher → ℕ) (target : JetIndex lower → ℕ) (compatible : Compatible bound gap source target) :
    ‖inclusion dimension lower higher domain gap bound source target compatible‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro jet
  change ‖shiftedTuple dimension lower higher domain gap bound jet.val‖ ≤ 1 * ‖jet.val‖
  simpa only [one_mul] using shiftedTuple_norm_le dimension lower higher domain gap bound jet.val

theorem inclusion_injective (dimension lower higher : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (gap : ℕ) (bound : lower ≤ higher) (source : JetIndex higher → ℕ) (target : JetIndex lower → ℕ)
    (compatible : Compatible bound gap source target) :
    Function.Injective (inclusion dimension lower higher domain gap bound source target compatible) := by
  intro first second equality
  apply base_injective dimension higher domain openDomain source
  rw [← inclusion_base dimension lower higher domain gap bound source target compatible first,
    ← inclusion_base dimension lower higher domain gap bound source target compatible second, equality]

theorem inclusion_spec (dimension lower higher : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (gap : ℕ) (bound : lower ≤ higher) (source : JetIndex higher → ℕ) (target : JetIndex lower → ℕ)
    (compatible : Compatible bound gap source target) :
    InclusionSpec dimension lower higher domain gap bound source target
      (inclusion dimension lower higher domain gap bound source target compatible) :=
  ⟨inclusion_opNorm_le dimension lower higher domain gap bound source target compatible,
    inclusion_injective dimension lower higher domain openDomain gap bound source target compatible,
    inclusion_coordinates dimension lower higher domain gap bound source target compatible,
    inclusion_base dimension lower higher domain gap bound source target compatible⟩

theorem general_consumer : GeneralGoal := by
  intro dimension lower higher domain openDomain gap bound source target compatible
  exact ⟨inclusion dimension lower higher domain gap bound source target compatible,
    inclusion_spec dimension lower higher domain openDomain gap bound source target compatible⟩

end Grad.WeightedJets.Inclusions

import SD1Radial

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (CellValues PhysicalValue FieldL2)
open Grad.WeightedJets (JetIndex degree derivativeWord base)
open Grad.Mollifier.Pointwise (orderedDerivative)
open scoped ContDiff Topology BigOperators

namespace Grad.SmoothDensity

set_option maxHeartbeats 800000

theorem orderedDerivative_map {Value Target : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    [NormedAddCommGroup Target] [NormedSpace ℂ Target] (mapping : Value →L[ℂ] Target)
    (rank : ℕ) (word : Fin rank → Fin 2) (function : Spatial → Value)
    (smooth : ContDiff ℝ ∞ function) (point : Spatial) :
    orderedDerivative rank word (fun source => mapping (function source)) point =
      mapping (orderedDerivative rank word function point) := by
  change iteratedFDeriv ℝ rank ((mapping.restrictScalars ℝ) ∘ function) point _ = _
  rw [(mapping.restrictScalars ℝ).iteratedFDeriv_comp_left smooth.contDiffAt
    (by exact_mod_cast (le_top : (rank : ℕ∞) ≤ ⊤))]
  rfl

theorem derivative_zero_cell (dimension : ℕ) (function : Spatial → CellValues dimension)
    (smooth : ContDiff ℝ ∞ function) (cell : ℤ) (zeroCell : ∀ point, function point cell = 0)
    (rank : ℕ) (word : Fin rank → Fin 2) (point : Spatial) :
    orderedDerivative rank word function point cell = 0 := by
  have equality := orderedDerivative_map (lp.evalCLM ℂ (fun _ : ℤ => PhysicalValue dimension) 2 cell)
    rank word function smooth point
  have zeroFunction : (fun source => function source cell) = (fun _ => 0) := funext zeroCell
  change orderedDerivative rank word (fun source => function source cell) point =
    orderedDerivative rank word function point cell at equality
  rw [zeroFunction] at equality
  rw [← equality]
  simp [orderedDerivative]

def finiteWeight (dimension power : ℕ) (cells : Finset ℤ) : CellValues dimension →L[ℂ] CellValues dimension :=
  ∑ cell ∈ cells, Grad.CellWeights.positiveFactor power cell •
    (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => PhysicalValue dimension) 2 cell).comp
      (lp.evalCLM ℂ (fun _ : ℤ => PhysicalValue dimension) 2 cell)

theorem finiteWeight_apply (dimension power : ℕ) (cells : Finset ℤ) (value : CellValues dimension) :
    finiteWeight dimension power cells value =
      ∑ cell ∈ cells, Grad.CellWeights.positiveFactor power cell • lp.single 2 cell (value cell) := by
  simp only [finiteWeight, sum_apply, smul_apply,
    ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply]
  rfl

theorem weightedDerivative_eq (dimension power rank : ℕ) (word : Fin rank → Fin 2)
    (cells : Finset ℤ) (function : Spatial → CellValues dimension) :
    weightedDerivative dimension power rank word cells function =
      fun point => finiteWeight dimension power cells (orderedDerivative rank word function point) := by
  funext point
  exact (finiteWeight_apply dimension power cells _).symm

theorem finiteWeight_coordinate (dimension power : ℕ) (cells : Finset ℤ)
    (value : CellValues dimension) (cell : ℤ) :
    finiteWeight dimension power cells value cell =
      if cell ∈ cells then Grad.CellWeights.positiveFactor power cell • value cell else 0 := by
  classical
  rw [finiteWeight_apply]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, lp.single_apply]
  simp [Pi.single_apply, smul_ite]

theorem higher_finite_goal : HigherFiniteGoal := by
  intro dimension function cells core power rank word
  have smooth := Grad.Mollifier.Pointwise.orderedDerivative_contDiff rank word function core.1
  have compact := Grad.Mollifier.Pointwise.orderedDerivative_compactSupport rank word function core.2.1
  rw [weightedDerivative_eq]
  have smoothWeighted := (finiteWeight dimension power cells).contDiff.restrict_scalars ℝ |>.comp smooth
  have compactWeighted := compact.comp_left (finiteWeight dimension power cells).map_zero
  refine ⟨smoothWeighted, compactWeighted,
    smoothWeighted.continuous.memLp_of_hasCompactSupport compactWeighted, ?_⟩
  intro point cell
  rw [finiteWeight_coordinate]
  by_cases member : cell ∈ cells
  · rw [if_pos member]
  · rw [if_neg member, derivative_zero_cell dimension function core.1 cell
      (fun point => core.2.2 point cell member), smul_zero]

theorem zero_index_unique (index : JetIndex 0) : index = Grad.WeightedJets.zeroIndex 0 := by
  apply Subtype.ext
  have bound := index.property
  apply Prod.ext <;> dsimp [Grad.WeightedJets.zeroIndex] <;> omega

def rawZeroJet (dimension : ℕ) (domain : Set Spatial) (field : FieldL2 dimension domain) :
    Grad.WeightedJets.GraphGrade dimension 0 0 domain :=
  Grad.WeightedJets.ofCoordinates dimension 0 domain (fun _ => 0) (fun _ => field) (by
    intro index cell vector test
    rw [zero_index_unique index]
    simp only [Grad.WeightedJets.degree_zero, pow_zero, Grad.CellWeights.positiveFactor,
      mul_one, Grad.CellWeights.inverseFieldCLM_zero, ContinuousLinearMap.id_apply, one_mul]
    rw [Grad.WeightedJets.testPairing_apply, Grad.WeightedJets.derivativeTestPairing_apply]
    rfl)

theorem rawZeroJet_base (dimension : ℕ) (domain : Set Spatial) (field : FieldL2 dimension domain) :
    base dimension 0 domain (fun _ => 0) (rawZeroJet dimension domain field) = field := by
  rw [Grad.WeightedJets.base_apply, Grad.CellWeights.inverseFieldCLM_zero]
  rfl

theorem rawZeroJet_norm (dimension : ℕ) (domain : Set Spatial) (field : FieldL2 dimension domain) :
    ‖rawZeroJet dimension domain field‖ = ‖field‖ := by
  have sumSingleton : (Finset.univ : Finset (JetIndex 0)) = {Grad.WeightedJets.zeroIndex 0} := by
    ext index
    simp [zero_index_unique index]
  have square := Grad.WeightedJets.jet_norm_sq dimension 0 domain (fun _ => 0) (rawZeroJet dimension domain field)
  rw [sumSingleton, Finset.sum_singleton] at square
  change ‖rawZeroJet dimension domain field‖ ^ 2 = ‖field‖ ^ 2 at square
  nlinarith [norm_nonneg (rawZeroJet dimension domain field), norm_nonneg field]

theorem raw_zero_goal : RawZeroGoal :=
  fun dimension domain field => ⟨rawZeroJet dimension domain field,
    rawZeroJet_base dimension domain field, rawZeroJet_norm dimension domain field⟩

end Grad.SmoothDensity

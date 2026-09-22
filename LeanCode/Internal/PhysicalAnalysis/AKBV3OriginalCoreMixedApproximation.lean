import AKBV2FiniteSmoothOriginalCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Grad.CartesianCoreRecovery
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap
open Grad.WeightedJets Grad.SmoothDensity Grad.SpatialDilation

private theorem mixedSmoothApproximation {dimension grade : ℕ} (jet : Mixed dimension grade openUnitDisk) :
    ∃ functions : ℕ → Spatial → CellValues dimension,
    ∃ _smooth : ∀ number, ContDiff ℝ ∞ (functions number),
    ∃ cells : ℕ → Finset ℤ, ∃ approximants : ℕ → Mixed dimension grade openUnitDisk,
      (∀ number point cell, cell ∉ cells number → functions number point cell = 0) ∧
      Tendsto approximants atTop (𝓝 jet) ∧
      (∀ number, Realizes dimension openUnitDisk (.mixed grade) (functions number) (approximants number)) := by
  have onDisk : ∀ input : Mixed dimension grade (disk 1),
      ∃ functions : ℕ → Spatial → CellValues dimension,
      ∃ _smooth : ∀ number, ContDiff ℝ ∞ (functions number),
      ∃ cells : ℕ → Finset ℤ, ∃ approximants : ℕ → Mixed dimension grade (disk 1),
        (∀ number point cell, cell ∉ cells number → functions number point cell = 0) ∧
        Tendsto approximants atTop (𝓝 input) ∧
        (∀ number, Realizes dimension (disk 1) (.mixed grade) (functions number) (approximants number)) := by
    intro input
    obtain ⟨steps,_scales,_epsilons,_cellBounds,cores,_baseLimit,derivatives⟩ :=
      mixed_consumer dimension 1 1 (by norm_num) (fun _ => grade)
        (base dimension grade (disk 1) (fun index => grade-degree index) input)
        (fun _ => input) (fun _ => rfl)
    refine ⟨fun number => stepFunction dimension 1 (by norm_num) (steps number)
        (base dimension grade (disk 1) (fun index => grade-degree index) input),
      fun number => (cores number).1,
      fun number => Grad.WeightedJets.CellCutoff.centeredCells (steps number).cellRadius,
      fun number => restrictJet dimension 1 (.mixed grade)
        (stepJet dimension 1 (by norm_num) (.mixed grade) (steps number) input),
      fun number => (cores number).2.2,(derivatives 0).2,?_⟩
    intro number
    exact realizes_restriction dimension (Set.subset_univ (disk 1)) MeasurableSet.univ (.mixed grade)
      _ _ ((derivatives 0).1 number)
  have unit : disk 1 = openUnitDisk := openUnitDisk_eq_ball.symm
  rw [unit] at onDisk
  exact onDisk jet

/-- Accepted finite-cell smooth density supplies actual original-core approximations in the exact mixed norm. -/
theorem originalCore_mixedApproximation {dimension grade : ℕ} (parameters : PhaseParameters)
    (jet : Mixed dimension grade openUnitDisk) :
    ∃ cores : ℕ → ACore parameters dimension, ∃ approximants : ℕ → Mixed dimension grade openUnitDisk,
      Tendsto approximants atTop (𝓝 jet) ∧
      (∀ number cell index,
        cartesianGradeCoordinates parameters grade (cores number) cell index =
          fieldCellProjection dimension openUnitDisk cell
            ((approximants number).val (originalJetIndexEquiv grade index))) ∧
      (∀ number cell, Grad.RawSourceFaithfulness.zeroCell parameters cell
        (aGradeEta parameters (GradeCore.ofCoreLinear (cores number))) =
          fieldCellProjection dimension openUnitDisk cell
            (base dimension grade openUnitDisk (fun index => grade-degree index) (approximants number))) := by
  obtain ⟨functions,smooth,cells,approximants,supported,converges,realized⟩ := mixedSmoothApproximation jet
  exact ⟨fun number => finiteWeightedOriginalCore parameters (functions number) (smooth number) (cells number),
    approximants,converges,
    fun number => finiteWeightedOriginalCore_coordinates parameters (functions number) (smooth number)
      (cells number) (supported number) (approximants number) (realized number),
    fun number => finiteWeightedOriginalCore_zeroCell parameters (functions number) (smooth number)
      (cells number) (supported number) (approximants number) (realized number)⟩

end Grad.CartesianCoreRecovery

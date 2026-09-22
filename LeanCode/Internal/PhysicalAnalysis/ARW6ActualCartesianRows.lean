import ARW5ActualFourierRows

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators
namespace Grad.ActualRadialWords
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.ActualOuterCollar Grad.CollarCartesian Grad.BoundaryLift

theorem actualOuterJet_mixedRows_bound (index : CartesianMultiIndex) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (modes : Finset ℤ) (parameter : ℝ) (source : highDiskL2)
      (core : ClosedJet 1) (same : source.val = closedL2Core core),
      ‖closedDerivativeL2 index (actualOuterJet modes parameter source core same)‖ ^ 2 ≤
        constant * ∫ time in (0 : ℝ)..(1 / 2 : ℝ),
          mixedRowsDensity (finiteHighModes modes) (actualWordRows parameter source) (cartesianOrder index) time := by
  obtain ⟨constant, nonnegative, bound⟩ :=
    localRows_cartesian_consumer actualPolarCutoff actualPolarCutoff_smooth index
  refine ⟨constant, nonnegative, ?_⟩
  intro modes parameter source core same
  have estimate := bound 1 (smoothClosedExtension (actualOuterJet modes parameter source core same))
    (smoothClosedExtension_smooth _) (actualOuterExtension_zero modes parameter source core same)
    (actualPolarFinite modes parameter source) (actualPolarFinite_smooth modes parameter source core same)
    (finiteHighModes modes) (actualWordRows parameter source)
    (actualWordRows_continuousOn parameter source core same)
    (actualOuterExtension_polar_germ modes parameter source core same)
    (by
      intro order _ time timeIn angle word
      exact actualPolarFinite_word_expansion modes parameter source core same order word (time, angle)
        ⟨timeIn, mem_univ _⟩)
  rw [smoothClosedExtension_restricts] at estimate
  exact estimate

end Grad.ActualRadialWords

import ASG30CompactWeakGraphConverse

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryKernelAction

/-- Full AH10 characterization with the paper's ORIGINAL compact smooth
interior distributional tests. The norm is literal r dr and the two polynomial
weights; the first coordinate is exp(Phi_n) times the actual physical source. -/
theorem actualAH10_compact_intrinsic_iff (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (value derivative : (ℤ × ℤ) → CollarL2 (ComplexEuclidean dimension) lower) :
    ((∀ mode, CompactWeakDerivative dimension lower (value mode) (derivative mode)) ∧
      Summable (fun mode : ℤ × ℤ => splitTangentialWeight angular cell mode ^ 2 *
        weakRadialEnergy dimension lower (value mode) (derivative mode))) ↔
    ∃! field : AnnularSourceH1 parameters dimension lower angular cell,
      ∀ mode, annularConjugatedCoordinate parameters dimension lower positive bounded.le angular cell field mode 0 = value mode ∧
        annularConjugatedCoordinate parameters dimension lower positive bounded.le angular cell field mode 1 = derivative mode := by
  rw [show (∀ mode, CompactWeakDerivative dimension lower (value mode) (derivative mode)) ↔
      (∀ mode, CollarWeakDerivative lower (value mode) (derivative mode)) from
        forall_congr' (fun mode => compactWeak_iff_collarWeak dimension lower positive bounded (value mode) (derivative mode))]
  exact actualAH10_intrinsic_iff parameters dimension lower positive bounded angular cell value derivative

/-- The intrinsic weak source uses exactly the already constructed two
endpoint extensions; AH11 applies without a second boundary coordinate. -/
theorem actualAH11_compact_source (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (value derivative : (ℤ × ℤ) → CollarL2 (ComplexEuclidean dimension) lower)
    (weak : ∀ mode, CompactWeakDerivative dimension lower (value mode) (derivative mode))
    (finiteEnergy : Summable (fun mode : ℤ × ℤ => splitTangentialWeight angular cell mode ^ 2 *
      weakRadialEnergy dimension lower (value mode) (derivative mode))) :
    ∃ field : AnnularSourceH1 parameters dimension lower angular cell,
      (∀ mode, annularConjugatedCoordinate parameters dimension lower positive bounded.le angular cell field mode 0 = value mode ∧
        annularConjugatedCoordinate parameters dimension lower positive bounded.le angular cell field mode 1 = derivative mode) ∧
      ∀ endpoint : Fin 2,
        ‖annularSourceTrace parameters dimension lower positive bounded angular cell endpoint field‖ ≤
          sourceEndpointConstant lower * ‖field‖ ∧
        ‖annularSourceTrace parameters dimension lower positive bounded angular cell endpoint field‖ ^ 2 =
          physicalEndpointEnergy parameters dimension (radialEndpointRadius lower endpoint) angular cell
            (annularSourceTrace parameters dimension lower positive bounded angular cell endpoint field) := by
  obtain ⟨field, coordinates, _unique⟩ := (actualAH10_compact_intrinsic_iff parameters dimension lower positive bounded angular cell value derivative).1
    ⟨weak, finiteEnergy⟩
  exact ⟨field, coordinates, actualAH11_both_endpoints parameters dimension lower positive bounded angular cell field⟩

end Grad.AnnularSourceGraph

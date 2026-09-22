import AKCO22ActualOriginalSourceAllPowerStartup

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets Grad.CellWeights Grad.CellBinomial

/-- The genuine all-p startup supplies every natural cell weight at the
first spatial grade. This is the outer spatial induction's actual base,
using the unchanged CellBinomial synthesis and SAME signed representatives. -/
theorem StartupSignedFamily.allNaturalGraphs {dimension : ℕ} {L ell : ℝ}
    (family : StartupSignedFamily dimension L ell) (order : ℕ) (lengthNonzero : L ≠ 0) (scaleNonzero : ell ≠ 0)
    (regular : ∀ power : ℕ, ∃ graph : GraphGrade dimension order 0 openUnitDisk,
      base dimension order openUnitDisk (fun _ => 0) graph = family.moment power) :
    ∀ weight : ℕ, ∃ graph : GraphGrade dimension order weight openUnitDisk,
      base dimension order openUnitDisk (fun _ => weight) graph = family.field := by
  apply (allCellConsumer dimension order openUnitDisk openUnitDisk_isOpen family.field).mpr
  intro power
  obtain ⟨graph,same⟩ := regular power
  let derivative := operatorJetOfGraph dimension order openUnitDisk (derivativeFactor power) family.field
    (((((ell/L : ℝ) : ℂ)⁻¹)^power) • graph) (by
      rw [map_smul,same]
      exact (fieldGraph_mem dimension openUnitDisk _ _ _).mpr
        (family.unscaledProjection lengthNonzero scaleNonzero power))
  exact ⟨derivative.inDomain,derivative.jet,derivative.base_eq⟩

theorem StartupSignedFamily.allNaturalFirst {dimension : ℕ} {L ell : ℝ}
    (family : StartupSignedFamily dimension L ell) (lengthNonzero : L ≠ 0) (scaleNonzero : ell ≠ 0)
    (regular : ∀ power : ℕ, ∃ graph : StartupFirst dimension,
      base dimension 1 openUnitDisk (fun _ => 0) graph = family.moment power) :
    ∀ weight : ℕ, ∃ graph : GraphGrade dimension 1 weight openUnitDisk,
      base dimension 1 openUnitDisk (fun _ => weight) graph = family.field :=
  family.allNaturalGraphs 1 lengthNonzero scaleNonzero regular

end Grad.CartesianStartup

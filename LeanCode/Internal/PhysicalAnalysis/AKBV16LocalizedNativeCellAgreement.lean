import AKBV15ActualNativeOuterGluing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace Grad.CartesianCoreRecovery
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.CartesianStartup

/-- Literal scaled-localized weak representatives determine every punctured weighted native cell pointwise, including the original phase at the unscaled point. -/
theorem localizedWeightedCells_pointwise {dimension : ℕ} (parameters : PhaseParameters)
    (scale upper : ℝ) (scalePositive : 0 < scale) (upperScale : upper ≤ scale) (upperOne : upper ≤ 1)
    (field : StartupL2 dimension) (weighted : DiskCellClosedJet dimension)
    (sameWeighted : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      field point cell = closedDiskLift (diskCellFourierCoefficientJet weighted cell).value point)
    (raw : ℤ → SpatialPlane → ComplexEuclidean dimension)
    (continuousRaw : ∀ cell, ContinuousOn (raw cell) {point | 0 < ‖point‖ ∧ ‖point‖ < 1})
    (cutoff : SpatialPlane → ℝ) (cutoffOne : ∀ point, scale * ‖point‖ < upper → cutoff point = 1)
    (sameRaw : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      field point cell = cutoff point • (cartesianWeight parameters cell (scale • point) • raw cell (scale • point)))
    (point : SpatialPlane) (inside : ‖point‖ ∈ Ioo 0 upper) (cell : ℤ) :
    (diskCellFourierCoefficientJet weighted cell).value
      (inverseScaledDiskPoint scale scalePositive point (inside.2.le.trans upperScale)) =
      cartesianWeight parameters cell point • raw cell point := by
  let domain : Set SpatialPlane := {source | 0 < ‖source‖ ∧ scale * ‖source‖ < upper}
  have openDomain : IsOpen domain :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt (continuous_const.mul continuous_norm) continuous_const)
  have included : domain ⊆ openUnitDisk := by
    intro source member
    change ‖source‖ < 1
    have bound : scale * ‖source‖ < scale := member.2.trans_le upperScale
    nlinarith
  have normScale (source : SpatialPlane) : ‖scale • source‖ = scale * ‖source‖ := by
    rw [norm_smul,Real.norm_of_nonneg scalePositive.le]
  have maps : MapsTo (fun source : SpatialPlane => scale • source) domain {source | 0 < ‖source‖ ∧ ‖source‖ < 1} := by
    intro source member
    rw [Set.mem_ofPred_eq,normScale]
    exact ⟨mul_pos scalePositive member.1,member.2.trans_le upperOne⟩
  have continuousCells (query : ℤ) : ContinuousOn
      (fun source : SpatialPlane => cartesianWeight parameters query (scale • source) • raw query (scale • source)) domain :=
    (((cartesianWeight_contDiff parameters query).continuous.comp (continuous_const_smul scale)).continuousOn).smul
      ((continuousRaw query).comp (continuous_const_smul scale).continuousOn maps)
  have literal : ∀ᵐ source ∂volume.restrict domain, ∀ query : ℤ,
      field source query = cartesianWeight parameters query (scale • source) • raw query (scale • source) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset included sameRaw,
      ae_restrict_mem openDomain.measurableSet] with source actual member
    intro query
    rw [actual query,cutoffOne source member.2,one_smul]
  have equality := sameWeightedClosedJet_pointwise field weighted sameWeighted domain openDomain included
    (fun query source => cartesianWeight parameters query (scale • source) • raw query (scale • source))
    continuousCells literal cell
  let source := inverseScaledDiskPoint scale scalePositive point (inside.2.le.trans upperScale)
  have scaled : scale • source.val = point := by
    change scale • (scale⁻¹ • point) = point
    exact smul_inv_smul₀ scalePositive.ne' point
  have sourceMember : source.val ∈ domain := by
    have normSame : scale * ‖source.val‖ = ‖point‖ := (normScale source.val).symm.trans (congrArg norm scaled)
    refine ⟨?_,?_⟩
    · exact (mul_pos_iff_of_pos_left scalePositive).mp (normSame ▸ inside.1)
    · exact normSame ▸ inside.2
  have result := equality sourceMember
  rw [closedDiskLift,dif_pos source.property] at result
  change (diskCellFourierCoefficientJet weighted cell).value source =
    cartesianWeight parameters cell (scale • source.val) • raw cell (scale • source.val) at result
  rw [scaled] at result
  exact result

end Grad.CartesianCoreRecovery

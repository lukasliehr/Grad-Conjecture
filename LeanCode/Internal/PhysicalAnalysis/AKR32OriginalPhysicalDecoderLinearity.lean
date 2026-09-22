import AKR31ActualResidualCoefficientLinearMaps

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularOriginalSmoothCore Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.PhaseAlgebra
open Grad.AnnularOriginalHigh Grad.AnnularOriginalLow Grad.AnnularLowEnergy Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.WeightedTrace

open Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger

open Grad.AnnularCurrentLow Grad.AnnularCurrentSource Grad.AnnularHighTilt

open Grad.AnnularFullGraph

open Grad.AnnularHighRadial Grad.AnnularTiltedReference Grad.AnnularOmegaGraph Grad.CircularHighRegularity

open Grad.AnnularCurrentLow
open Grad.AnnularCurrentSource Grad.AnnularStrongData
variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)

theorem originalF1Coefficient_add_ae (first second : DivisionRow 1 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      originalF1Coefficient parameters lower positive bounded (first+second) radius mode =
        originalF1Coefficient parameters lower positive bounded first radius mode +
          originalF1Coefficient parameters lower positive bounded second radius mode := by
  unfold originalF1Coefficient
  rw [map_add]
  exact lowRhoPhysicalCoefficient_add_ae parameters lower positive _ _

theorem lowRhoPhysicalCoefficient_real_smul_ae (scalar : ℝ) (field : DivisionRow 1 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      lowRhoPhysicalCoefficient parameters lower positive (scalar • field) radius mode =
        scalar • lowRhoPhysicalCoefficient parameters lower positive field radius mode := by
  rw [ae_all_iff]
  intro mode
  filter_upwards [Lp.coeFn_smul scalar (field mode)] with radius same
  change (lowRhoPhysicalWeight parameters lower positive radius mode : ℂ)⁻¹ • (scalar • field mode) radius = _
  rw [same]
  change (lowRhoPhysicalWeight parameters lower positive radius mode : ℂ)⁻¹ • (scalar • field mode radius) =
    scalar • ((lowRhoPhysicalWeight parameters lower positive radius mode : ℂ)⁻¹ • field mode radius)
  exact smul_comm _ _ _

theorem originalF1Coefficient_real_smul_ae (scalar : ℝ) (field : DivisionRow 1 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      originalF1Coefficient parameters lower positive bounded (scalar • field) radius mode =
        scalar • originalF1Coefficient parameters lower positive bounded field radius mode := by
  unfold originalF1Coefficient
  rw [(divisionHighWeight lower positive bounded).map_smul_of_tower scalar field]
  exact lowRhoPhysicalCoefficient_real_smul_ae parameters lower positive scalar _

theorem originalG3Coefficient_add_ae (first second : DivisionRow 1 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      originalG3Coefficient parameters lower positive bounded (first+second) radius mode =
        originalG3Coefficient parameters lower positive bounded first radius mode +
          originalG3Coefficient parameters lower positive bounded second radius mode := by
  unfold originalG3Coefficient
  rw [map_add]
  exact originalF1Coefficient_add_ae parameters lower positive bounded _ _

theorem originalG3Coefficient_real_smul_ae (scalar : ℝ) (field : DivisionRow 1 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      originalG3Coefficient parameters lower positive bounded (scalar • field) radius mode =
        scalar • originalG3Coefficient parameters lower positive bounded field radius mode := by
  unfold originalG3Coefficient
  rw [(originalAngularDecode lower).map_smul_of_tower scalar field]
  exact originalF1Coefficient_real_smul_ae parameters lower positive bounded scalar _

end Grad.AnnularOriginalCoreRealization

import ANR9PolarEnergy
import RSC5PolarLinearity
import ASG1WeightedRadialCompletion

noncomputable section
set_option maxHeartbeats 1000000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.BoundaryTrace
open Grad.AnnularSourceGraph Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The actual radial Fourier coefficient and its actual derivative form
one genuine smooth graph, before any completion. -/
def diskRadialSmoothCore (mode : ℤ) (field : ClosedJet 1) : SmoothRadialCore 1 :=
  ⟨⟨(⟨radialCoefficientJet (originalPolarValue field) mode 0,
        (radialCoefficientJet_smooth _ (originalPolarValue_smooth field) mode 0).continuous⟩,
      ⟨radialCoefficientJet (originalPolarValue field) mode 1,
        (radialCoefficientJet_smooth _ (originalPolarValue_smooth field) mode 1).continuous⟩),
      radialCoefficientJet_hasDerivAt _ (originalPolarValue_smooth field) mode 0⟩,
    radialCoefficientJet_smooth _ (originalPolarValue_smooth field) mode 0⟩

def diskRadialCoefficientL2 (lower : ℝ) (positive : 0 < lower) (mode : ℤ) (order : ℕ) :
    ClosedJet 1 →ₗ[ℂ] RadialL2 1 lower where
  toFun field := radialToLp lower (radialCoefficientJet (originalPolarValue field) mode order)
    (radialCoefficientJet_smooth _ (originalPolarValue_smooth field) mode order).continuous
  map_add' first second :=
    radialToLp_add_of_interior lower positive _ _ _ _ _ _ (polarCoefficient_add first second mode order)
  map_smul' scalar field :=
    radialToLp_smul_of_interior lower positive scalar _ _ _ _ (polarCoefficient_smul scalar field mode order)

def diskRadialCore (lower : ℝ) (positive : 0 < lower) (mode : ℤ) :
    ClosedJet 1 →ₗ[ℝ] WeightedRadialH1 1 lower where
  toFun field := weightedRadialCoreInto 1 lower (diskRadialSmoothCore mode field)
  map_add' first second := by
    apply Subtype.ext
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate
    · exact (diskRadialCoefficientL2 lower positive mode 0).map_add first second
    · exact (diskRadialCoefficientL2 lower positive mode 1).map_add first second
  map_smul' scalar field := by
    apply Subtype.ext
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate
    · exact ((diskRadialCoefficientL2 lower positive mode 0).restrictScalars ℝ).map_smul scalar field
    · exact ((diskRadialCoefficientL2 lower positive mode 1).restrictScalars ℝ).map_smul scalar field

theorem diskRadialCore_coordinate (lower : ℝ) (positive : 0 < lower) (mode : ℤ)
    (field : ClosedJet 1) (coordinate : Fin 2) :
    weightedRadialCoordinate 1 lower coordinate (diskRadialCore lower positive mode field) =
      diskRadialCoefficientL2 lower positive mode coordinate.val field := by
  fin_cases coordinate <;> rfl

theorem diskRadialCore_norm_sq (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (field : ClosedJet 1) :
    ‖diskRadialCore lower positive mode field‖ ^ 2 =
      annularCoefficientEnergy lower (radialIter 0 (originalPolarValue field)) mode +
      annularCoefficientEnergy lower (radialIter 1 (originalPolarValue field)) mode := by
  rw [weightedRadialH1_norm_sq, diskRadialCore_coordinate, diskRadialCore_coordinate]
  change ‖radialToLp lower (radialCoefficientJet (originalPolarValue field) mode 0)
      (radialCoefficientJet_smooth _ (originalPolarValue_smooth field) mode 0).continuous‖ ^ 2 +
    ‖radialToLp lower (radialCoefficientJet (originalPolarValue field) mode 1)
      (radialCoefficientJet_smooth _ (originalPolarValue_smooth field) mode 1).continuous‖ ^ 2 = _
  rw [radialToLp_norm_sq lower positive.le bounded, radialToLp_norm_sq lower positive.le bounded]
  rfl

def diskRadialBound : ℝ := Real.sqrt ((2 * Real.pi)⁻¹ * (polarOrderConstant 0 + polarOrderConstant 1))

theorem diskRadialBound_nonnegative : 0 ≤ diskRadialBound := Real.sqrt_nonneg _

theorem diskRadialCore_bound (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (field : ClosedJet 1) :
    ‖diskRadialCore lower positive mode field‖ ≤ diskRadialBound * ‖diskCoreInto field‖ := by
  have value := diskPolar_coefficient_energy field mode 0 (by omega) lower positive.le bounded
  have slope := diskPolar_coefficient_energy field mode 1 le_rfl lower positive.le bounded
  have boundSq : ‖diskRadialCore lower positive mode field‖ ^ 2 ≤
      ((2 * Real.pi)⁻¹ * (polarOrderConstant 0 + polarOrderConstant 1)) * ‖diskCoreInto field‖ ^ 2 := by
    rw [diskRadialCore_norm_sq lower positive bounded mode field]
    nlinarith [value, slope]
  have factorNonnegative : 0 ≤ (2 * Real.pi)⁻¹ * (polarOrderConstant 0 + polarOrderConstant 1) :=
    mul_nonneg (by positivity) (add_nonneg (polarOrderConstant_nonnegative 0) (polarOrderConstant_nonnegative 1))
  have square : diskRadialBound ^ 2 = (2 * Real.pi)⁻¹ * (polarOrderConstant 0 + polarOrderConstant 1) :=
    Real.sq_sqrt factorNonnegative
  have targetNonnegative := mul_nonneg diskRadialBound_nonnegative (norm_nonneg (diskCoreInto field))
  nlinarith [sq_nonneg (‖diskRadialCore lower positive mode field‖ - diskRadialBound * ‖diskCoreInto field‖)]

end Grad.CircularHighRegularity

import AKCO2SameSignedSourceCarriers
import AKBT22SameScaledPhaseAndKnownFirst

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers

/-- Only fixed cell-diagonal actions commute with the signed power. -/
theorem StartupCellwise.signedProjection {input output : ℕ}
    {operator : StartupL2 input →L[ℂ] StartupL2 output} (diagonal : StartupCellwise operator)
    (weight : ℤ → ℂ) (field moment : StartupL2 input)
    (same : ∀ cell, fieldCellProjection input openUnitDisk cell moment =
      weight cell • fieldCellProjection input openUnitDisk cell field) (cell : ℤ) :
    fieldCellProjection output openUnitDisk cell (operator moment) =
      weight cell • fieldCellProjection output openUnitDisk cell (operator field) := by
  obtain ⟨mapping,mapped⟩ := diagonal cell
  rw [mapped,mapped,same]
  exact mapping.map_smul (weight cell) _

end Grad.CartesianStartup

namespace Grad.ActualOriginalSourceFirst
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.CartesianStartup
open Grad.ActualScalarWeakEquations Grad.SpatialDilation Grad.WeightedJets
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.Constraints

variable (parameters : PhaseParameters) (source : SmoothQuotient parameters)
  (length : ℝ) (positive : 0 < length)

def actualOriginalKnownForce_signedFirst (power : ℕ) : StartupFirst 2 :=
  startupGenuineQradFirst (originalSignedAxialFirst parameters (cartesianSourceVector source)
    length (originalStartupScale length positive) power)

def actualOriginalKnownThird_signedFirst (power : ℕ) : StartupFirst 1 :=
  (length⁻¹ : ℂ) • originalSignedAxialFirst parameters (source 3)
    length (originalStartupScale length positive) power

theorem actualOriginalKnownForce_signedProjection (power : ℕ) (cell : ℤ) :
    fieldCellProjection 2 openUnitDisk cell
      (base 2 1 openUnitDisk (fun _ => 0)
        (actualOriginalKnownForce_signedFirst parameters source length positive power)) =
      startupAxialFrequency length (min 1 length / 4) cell ^ power •
        fieldCellProjection 2 openUnitDisk cell
          (base 2 1 openUnitDisk (fun _ => 0)
            (startupGenuineQradFirst (actualOriginalF_first parameters source length positive))) := by
  rw [actualOriginalKnownForce_signedFirst,startupGenuineQrad_compatible,startupGenuineQrad_compatible]
  exact ((StartupCellwise.id 2).add ((originalValueKernel_cellwise quarterValueMap).comp
    (originalTangentialKernel_cellwise.comp (originalValueKernel_cellwise quarterValueMap)))).signedProjection
    (fun cell => startupAxialFrequency length (min 1 length / 4) cell ^ power) _ _
    (originalSignedAxialFirst_projection parameters (cartesianSourceVector source)
      length (originalStartupScale length positive) power) cell

theorem actualOriginalKnownThird_signedProjection (power : ℕ) (cell : ℤ) :
    fieldCellProjection 1 openUnitDisk cell
      (base 1 1 openUnitDisk (fun _ => 0)
        (actualOriginalKnownThird_signedFirst parameters source length positive power)) =
      startupAxialFrequency length (min 1 length / 4) cell ^ power •
        fieldCellProjection 1 openUnitDisk cell
          (base 1 1 openUnitDisk (fun _ => 0) (actualOriginalH_first parameters source length positive)) := by
  rw [actualOriginalKnownThird_signedFirst,actualOriginalH_first,map_smul,map_smul,map_smul,map_smul,
    originalSignedAxialFirst_projection]
  exact smul_comm _ _ _

end Grad.ActualOriginalSourceFirst

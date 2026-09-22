import AKBS4SameSourceFirstDilation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 850000
open Set Filter MeasureTheory
namespace Grad.ActualOriginalSourceFirst
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.CartesianStartup
open Grad.ActualScalarWeakEquations Grad.QuotientProjection Grad.SourceCollarFullSource Grad.FlatSourceProjection
open Grad.ActualOriginalSourceMoments Grad.WeightedJets Grad.SpatialDilation

variable (parameters : PhaseParameters) (source : SmoothQuotient parameters)
  (length : ℝ) (positive : 0 < length)

/-- The actual normalized F=f(ell Y), in the original-width weighted first graph. -/
def actualOriginalF_first : StartupFirst 2 :=
  scaledOriginalSourceFirst parameters (cartesianSourceVector source) (originalStartupScale length positive)

/-- The actual normalized H=h(ell Y)/L, in the original-width weighted first graph. -/
def actualOriginalH_first : StartupFirst 1 :=
  (length⁻¹ : ℂ) • scaledOriginalSourceFirst parameters (source 3) (originalStartupScale length positive)

theorem actualOriginalF_first_base :
    base 2 1 openUnitDisk (fun _ => 0) (actualOriginalF_first parameters source length positive) =
      ((originalSourceMoments parameters (cartesianSourceVector source)).dilate
        (originalStartupScale length positive)).field :=
  scaledOriginalSourceFirst_base parameters (cartesianSourceVector source) _

theorem actualOriginalH_first_base :
    base 1 1 openUnitDisk (fun _ => 0) (actualOriginalH_first parameters source length positive) =
      (length⁻¹ : ℂ) • ((originalSourceMoments parameters (source 3)).dilate
        (originalStartupScale length positive)).field := by
  rw [actualOriginalH_first,map_smul,scaledOriginalSourceFirst_base]

theorem actualOriginalF_first_same :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      base 2 1 openUnitDisk (fun _ => 0) (actualOriginalF_first parameters source length positive) point cell =
        Grad.AnalyticWeights.Calculus.physicalWeight parameters.sigma0 parameters.gamma (min 1 length / 4) cell point •
          originalCoreCell parameters (cartesianSourceVector source) cell ((min 1 length / 4) • point) :=
  scaledOriginalSourceFirst_same parameters (cartesianSourceVector source) _

theorem actualOriginalH_first_same :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      base 1 1 openUnitDisk (fun _ => 0) (actualOriginalH_first parameters source length positive) point cell =
        Grad.AnalyticWeights.Calculus.physicalWeight parameters.sigma0 parameters.gamma (min 1 length / 4) cell point •
          ((length⁻¹ : ℂ) • originalCoreCell parameters (source 3) cell ((min 1 length / 4) • point)) := by
  rw [actualOriginalH_first,map_smul]
  filter_upwards [Lp.coeFn_smul (length⁻¹ : ℂ)
      (base 1 1 openUnitDisk (fun _ => 0)
        (scaledOriginalSourceFirst parameters (source 3) (originalStartupScale length positive))),
    scaledOriginalSourceFirst_same parameters (source 3) (originalStartupScale length positive)] with point scaled same
  intro cell
  rw [scaled,Pi.smul_apply,lp.coeFn_smul,Pi.smul_apply,same cell]
  exact smul_comm _ _ _

/-- Public source regularity endpoint for the genuine scaled startup: both SAME original F/H carriers have first weak derivatives. -/
theorem actualOriginalFH_firstCarriers :
    ∃ force : StartupFirst 2, ∃ third : StartupFirst 1,
      base 2 1 openUnitDisk (fun _ => 0) force =
        ((originalSourceMoments parameters (cartesianSourceVector source)).dilate
          (originalStartupScale length positive)).field ∧
      base 1 1 openUnitDisk (fun _ => 0) third =
        (length⁻¹ : ℂ) • ((originalSourceMoments parameters (source 3)).dilate
          (originalStartupScale length positive)).field :=
  ⟨actualOriginalF_first parameters source length positive,actualOriginalH_first parameters source length positive,
    actualOriginalF_first_base parameters source length positive,actualOriginalH_first_base parameters source length positive⟩

end Grad.ActualOriginalSourceFirst

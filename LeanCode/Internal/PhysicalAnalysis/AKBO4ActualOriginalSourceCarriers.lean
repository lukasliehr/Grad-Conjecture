import AKBO3SameOriginalSourceMoments

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Set Filter MeasureTheory
namespace Grad.ActualOriginalSourceMoments
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.CartesianStartup
open Grad.ActualScalarWeakEquations Grad.QuotientProjection Grad.SourceCollarFullSource Grad.FlatSourceProjection

/-- Actual original planar force, determinant source and third source in the joint carrier, with every signed cell and all three same-field moments. -/
theorem actualOriginalSource_rawCarriers (parameters : PhaseParameters) (source : SmoothQuotient parameters) :
    ∃ force : StartupMoments 2, ∃ determinant third : StartupMoments 1,
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
        force.field point cell = originalCoreCell parameters (cartesianSourceVector source) cell point) ∧
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
        determinant.field point cell = originalCoreCell parameters (source 2) cell point) ∧
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
        third.field point cell = originalCoreCell parameters (source 3) cell point) :=
  ⟨originalSourceRawMoments parameters (cartesianSourceVector source),
    originalSourceRawMoments parameters (source 2),originalSourceRawMoments parameters (source 3),
    originalSourceRawMoments_same parameters (cartesianSourceVector source),
    originalSourceRawMoments_same parameters (source 2),originalSourceRawMoments_same parameters (source 3)⟩

/-- The identical source carriers retain the original analytic conjugation, without changing its width. -/
theorem actualOriginalSource_weightedCarriers (parameters : PhaseParameters) (source : SmoothQuotient parameters) :
    ∃ force : StartupMoments 2, ∃ determinant third : StartupMoments 1,
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
        force.field point cell = cartesianWeight parameters cell point • originalCoreCell parameters (cartesianSourceVector source) cell point) ∧
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
        determinant.field point cell = cartesianWeight parameters cell point • originalCoreCell parameters (source 2) cell point) ∧
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
        third.field point cell = cartesianWeight parameters cell point • originalCoreCell parameters (source 3) cell point) :=
  ⟨originalSourceMoments parameters (cartesianSourceVector source),
    originalSourceMoments parameters (source 2),originalSourceMoments parameters (source 3),
    originalSourceMoments_same parameters (cartesianSourceVector source),
    originalSourceMoments_same parameters (source 2),originalSourceMoments_same parameters (source 3)⟩

end Grad.ActualOriginalSourceMoments

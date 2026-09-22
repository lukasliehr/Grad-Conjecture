import COR12GradeComparison
import COR12FourierInverse

noncomputable section

open MeasureTheory

namespace Grad.COR12Extension

open Grad.ClosedJets
open Grad.CartesianState
open Grad.DiskExtension.Operator
open Grad.FourierGrade

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def continuousFourierCoefficientLinear {dimension : ℕ} (mode : FourierMode) :
    C(ProductTorus, ComplexEuclidean dimension) →ₗ[ℂ] ComplexEuclidean dimension where
  toFun field := UnitAddTorus.mFourierCoeff field (modeVector mode)
  map_add' first second := by
    change (∫ point : ProductTorus,
      UnitAddTorus.mFourier (-(modeVector mode)) point • (first point + second point)) = _
    simp only [smul_add]
    exact integral_add
      (productTorus_continuousMap_integrable
        ⟨fun point => UnitAddTorus.mFourier (-(modeVector mode)) point • first point,
          (UnitAddTorus.mFourier _).continuous.smul first.continuous⟩)
      (productTorus_continuousMap_integrable
        ⟨fun point => UnitAddTorus.mFourier (-(modeVector mode)) point • second point,
          (UnitAddTorus.mFourier _).continuous.smul second.continuous⟩)
  map_smul' scalar field := by
    change (∫ point : ProductTorus,
      UnitAddTorus.mFourier (-(modeVector mode)) point • (scalar • field point)) =
      scalar • ∫ point : ProductTorus,
        UnitAddTorus.mFourier (-(modeVector mode)) point • field point
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with point
    exact smul_comm _ _ _

theorem reconstructedTorus_add {dimension : ℕ}
    (first second : JCore (ComplexEuclidean dimension)) :
    reconstructedTorus (first + second) = reconstructedTorus first + reconstructedTorus second := by
  apply euclideanContinuousFourier_injective
  intro mode
  change continuousFourierCoefficientLinear mode (reconstructedTorus (first + second)) =
    continuousFourierCoefficientLinear mode (reconstructedTorus first + reconstructedTorus second)
  rw [map_add]
  simp only [continuousFourierCoefficientLinear, LinearMap.coe_mk, AddHom.coe_mk,
    euclidean_reconstructedTorus_coefficient]
  rfl

theorem reconstructedTorus_smul {dimension : ℕ} (scalar : ℂ)
    (values : JCore (ComplexEuclidean dimension)) :
    reconstructedTorus (scalar • values) = scalar • reconstructedTorus values := by
  apply euclideanContinuousFourier_injective
  intro mode
  change continuousFourierCoefficientLinear mode (reconstructedTorus (scalar • values)) =
    continuousFourierCoefficientLinear mode (scalar • reconstructedTorus values)
  rw [map_smul]
  simp only [continuousFourierCoefficientLinear, LinearMap.coe_mk, AddHom.coe_mk,
    euclidean_reconstructedTorus_coefficient]
  rfl

theorem normalizedExtension_add {dimension : ℕ}
    (first second : DiskCellClosedJet dimension) :
    torusSmoothNormalizedValue (ordinaryExtensionRetraction.extension dimension (first + second)) =
      torusSmoothNormalizedValue (ordinaryExtensionRetraction.extension dimension first) +
        torusSmoothNormalizedValue (ordinaryExtensionRetraction.extension dimension second) := by
  apply ContinuousMap.ext
  intro point
  exact ordinaryExtensionRetraction_linearity_real.2.1 dimension first second
    (torusCellToProduct.symm point)

theorem normalizedExtension_smul {dimension : ℕ} (scalar : ℂ)
    (field : DiskCellClosedJet dimension) :
    torusSmoothNormalizedValue (ordinaryExtensionRetraction.extension dimension (scalar • field)) =
      scalar • torusSmoothNormalizedValue (ordinaryExtensionRetraction.extension dimension field) := by
  apply ContinuousMap.ext
  intro point
  exact ordinaryExtensionRetraction_linearity_real.2.2.1 dimension scalar field
    (torusCellToProduct.symm point)

/-- The literal COR12 extension: first `Wγ`, then the one constructed P09
extension, then Fourier analysis on the physical `(4,4,2π)` torus. -/
def weightedFourierExtension {dimension : ℕ} (parameters : PhaseParameters) :
    ACore parameters dimension →ₗ[ℂ] JCore (ComplexEuclidean dimension) where
  toFun field := torusSmoothFourierCore
    (ordinaryExtensionRetraction.extension dimension (weightedSmoothEquiv parameters field))
  map_add' first second := by
    apply Subtype.ext
    funext mode
    change continuousFourierCoefficientLinear mode
      (torusSmoothNormalizedValue (ordinaryExtensionRetraction.extension dimension
        (weightedSmoothEquiv parameters (first + second)))) = _
    rw [map_add, normalizedExtension_add, map_add]
    rfl
  map_smul' scalar field := by
    apply Subtype.ext
    funext mode
    change continuousFourierCoefficientLinear mode
      (torusSmoothNormalizedValue (ordinaryExtensionRetraction.extension dimension
        (weightedSmoothEquiv parameters (scalar • field)))) = _
    rw [map_smul, normalizedExtension_smul, map_smul]
    rfl

/-- The literal COR12 reverse map: reconstruct, restrict through P09, and
apply the inverse of the same coefficientwise phase conjugation. -/
def weightedFourierRetraction {dimension : ℕ} (parameters : PhaseParameters) :
    JCore (ComplexEuclidean dimension) →ₗ[ℂ] ACore parameters dimension where
  toFun values := (weightedSmoothEquiv parameters).symm
    (ordinaryExtensionRetraction.restriction dimension (reconstructedTorusSmoothField values))
  map_add' first second := by
    rw [← map_add]
    apply congrArg (weightedSmoothEquiv parameters).symm
    apply diskCellClosedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    change reconstructedTorus (first + second) (torusCellToProduct (diskToTorus point)) =
      reconstructedTorus first (torusCellToProduct (diskToTorus point)) +
        reconstructedTorus second (torusCellToProduct (diskToTorus point))
    rw [reconstructedTorus_add, ContinuousMap.add_apply]
  map_smul' scalar values := by
    rw [← map_smul]
    apply congrArg (weightedSmoothEquiv parameters).symm
    apply diskCellClosedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    change reconstructedTorus (scalar • values) (torusCellToProduct (diskToTorus point)) =
      scalar • reconstructedTorus values (torusCellToProduct (diskToTorus point))
    rw [reconstructedTorus_smul, ContinuousMap.smul_apply]

theorem weightedFourierRetraction_extension {dimension : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension) :
    weightedFourierRetraction parameters (weightedFourierExtension parameters field) = field := by
  change (weightedSmoothEquiv parameters).symm
    (ordinaryExtensionRetraction.restriction dimension
      (reconstructedTorusSmoothField (torusSmoothFourierCore
        (ordinaryExtensionRetraction.extension dimension (weightedSmoothEquiv parameters field))))) = field
  rw [reconstructedTorusSmoothField_fourierCore,
    ordinaryExtensionRetraction_linearity_real.1]
  exact (weightedSmoothEquiv parameters).symm_apply_apply field

end Grad.COR12Extension

import AIP4PhysicalTorusIntegrals

noncomputable section
open MeasureTheory

namespace Grad.InteriorPeriodization
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.DiskExtension.Operator Grad.FourierGrade Grad.COR12Extension

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def diskCoreTorus (field : ClosedJet 1) : C(ProductTorus, ComplexEuclidean 1) :=
  torusSmoothNormalizedValue (ordinaryExtensionRetraction.extension 1 (constantDiskCellJet field))

theorem diskFourier_core_coefficient (parameters : PhaseParameters) (field : ClosedJet 1)
    (mode : FourierMode) :
    coefficient 0 (diskFourier parameters (closedL2Core field)) mode =
      UnitAddTorus.mFourierCoeff (diskCoreTorus field) (modeVector mode) := by
  rw [diskFourier_core, coreToGrade_coefficient]
  change torusSmoothCoefficient
    (ordinaryExtensionRetraction.extension 1
      (weightedSmoothEquiv parameters (normalizedSingleCore parameters field))) mode = _
  rw [normalizedSingleCore_weighted]
  rfl

/-- The actual Fourier extension of a compact interior core is precisely
the periodized zero extension on the physical fundamental square. -/
theorem compact_diskCoreTorus_literal (field : ClosedJet 1)
    (supported : ∀ point : ClosedDisk, (3 / 4 : ℝ) < ‖point.val‖ → field.value point = 0)
    (point : SpatialPlane) (cell : ℝ) (inside : point ∈ fundamentalHalfOpenSquare) :
    diskCoreTorus field (normalizedTorusPoint (point 0) (point 1) cell) = closedDiskLift field.value point := by
  have normalized := torusCellToProduct_torusCellPoint (assembleSpatialCell point cell)
  change torusCellToProduct (torusCellPoint (assembleSpatialCell point cell)) =
    normalizedTorusPoint (point 0) (point 1) cell at normalized
  change (periodizedExtension (constantDiskCellJet field)).value
    (torusCellToProduct.symm (normalizedTorusPoint (point 0) (point 1) cell)) = _
  rw [← normalized, Homeomorph.symm_apply_apply]
  exact (periodizedExtension_fundamental_formula (constantDiskCellJet field) point cell inside).trans
    (compact_ambientExtension_literal field supported point (cell : CellCircle))

def physicalCoefficientIntegrand (field : ClosedJet 1) (mode : FourierMode) :
    C(TorusCellDomain, ComplexEuclidean 1) :=
  ⟨fun point => UnitAddTorus.mFourier (-(modeVector mode)) (torusCellToProduct point) •
    (ordinaryExtensionRetraction.extension 1 (constantDiskCellJet field)).value point,
    ((UnitAddTorus.mFourier _).continuous.comp torusCellToProduct.continuous).smul
      (ordinaryExtensionRetraction.extension 1 (constantDiskCellJet field)).value.continuous⟩

theorem diskFourier_core_physical_integral (parameters : PhaseParameters) (field : ClosedJet 1)
    (mode : FourierMode) :
    coefficient 0 (diskFourier parameters (closedL2Core field)) mode =
      ∫ cell : CellCircle, ∫ second : SpatialCircle, ∫ first : SpatialCircle,
        physicalCoefficientIntegrand field mode ((first, second), cell)
          ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle := by
  rw [diskFourier_core_coefficient]
  change (∫ point : ProductTorus, UnitAddTorus.mFourier (-(modeVector mode)) point •
    diskCoreTorus field point) = _
  have integrand : (fun point : ProductTorus => UnitAddTorus.mFourier (-(modeVector mode)) point •
      diskCoreTorus field point) =
      fun point => physicalCoefficientIntegrand field mode (torusCellToProduct.symm point) := by
    funext point
    simp only [physicalCoefficientIntegrand, ContinuousMap.coe_mk, Homeomorph.apply_symm_apply]
    rfl
  rw [integrand]
  exact normalizedTorus_integral_physical_vector (physicalCoefficientIntegrand field mode)

end Grad.InteriorPeriodization

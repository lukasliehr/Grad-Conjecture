import COR12TorusEnergy

noncomputable section

open MeasureTheory

namespace Grad.COR12Extension

open Grad.ClosedJets
open Grad.DiskExtension.Operator
open Grad.FourierGrade

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem scalarContinuousFourier_injective
    (first second : C(ProductTorus, ℂ))
    (coefficients : ∀ mode : FourierMode,
      UnitAddTorus.mFourierCoeff first (modeVector mode) =
        UnitAddTorus.mFourierCoeff second (modeVector mode)) : first = second := by
  apply ContinuousMap.toLp_injective (p := 2) volume (𝕜 := ℂ)
  apply UnitAddTorus.mFourierBasis.repr.injective
  ext index
  rw [UnitAddTorus.mFourierBasis_repr, UnitAddTorus.mFourierBasis_repr,
    UnitAddTorus.mFourierCoeff_toLp, UnitAddTorus.mFourierCoeff_toLp]
  obtain ⟨mode, rfl⟩ := modeEquiv.surjective index
  exact coefficients mode

theorem euclideanContinuousFourier_injective {dimension : ℕ}
    (first second : C(ProductTorus, ComplexEuclidean dimension))
    (coefficients : ∀ mode : FourierMode,
      UnitAddTorus.mFourierCoeff first (modeVector mode) =
        UnitAddTorus.mFourierCoeff second (modeVector mode)) : first = second := by
  have coordinateEquality : ∀ coordinate : Fin dimension,
      euclideanContinuousComponent first coordinate =
        euclideanContinuousComponent second coordinate := by
    intro coordinate
    apply scalarContinuousFourier_injective
    intro mode
    rw [← euclideanContinuousComponent_mFourierCoeff,
      ← euclideanContinuousComponent_mFourierCoeff, coefficients]
  ext point coordinate
  exact congrArg (fun field : C(ProductTorus, ℂ) => field point)
    (coordinateEquality coordinate)

theorem reconstructedTorus_torusSmoothFourierCore {dimension : ℕ}
    (field : TorusSmoothField dimension) :
    reconstructedTorus (torusSmoothFourierCore field) = torusSmoothNormalizedValue field := by
  apply euclideanContinuousFourier_injective
  intro mode
  rw [euclidean_reconstructedTorus_coefficient]
  rfl

theorem reconstructedTorusSmoothField_fourierCore {dimension : ℕ}
    (field : TorusSmoothField dimension) :
    reconstructedTorusSmoothField (torusSmoothFourierCore field) = field := by
  apply torusSmoothField_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change reconstructedTorus (torusSmoothFourierCore field) (torusCellToProduct point) =
    field.value point
  rw [reconstructedTorus_torusSmoothFourierCore]
  simp [torusSmoothNormalizedValue]

theorem torusSmoothFourierCore_reconstructed {dimension : ℕ}
    (values : JCore (ComplexEuclidean dimension)) :
    torusSmoothFourierCore (reconstructedTorusSmoothField values) = values := by
  apply Subtype.ext
  funext mode
  exact reconstructedTorusSmoothField_coefficient values mode

end Grad.COR12Extension

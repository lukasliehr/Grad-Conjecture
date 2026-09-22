import FG1Proof
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

noncomputable section

open Set MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal

namespace Grad.FourierGrade

/-- The probability-normalized three-torus used for P10--P15.  A point with
physical coordinates `(y₁,y₂,ζ)` is represented by `(y₁/4,y₂/4,ζ/(2π))`. -/
abbrev ProductTorus := UnitAddTorus (Fin 3)

/-- The literal triple index as the function index used by mathlib's product-torus basis. -/
def modeVector (mode : FourierMode) : Fin 3 → ℤ :=
  ![mode.1, mode.2.1, mode.2.2]

/-- Recover the literal nested triple from a three-coordinate Fourier index. -/
def vectorMode (mode : Fin 3 → ℤ) : FourierMode :=
  (mode 0, mode 1, mode 2)

/-- Reindexing between the paper's `ℤ³` notation and mathlib's finite function notation. -/
def modeEquiv : FourierMode ≃ (Fin 3 → ℤ) where
  toFun := modeVector
  invFun := vectorMode
  left_inv mode := by
    rcases mode with ⟨first, second, third⟩
    rfl
  right_inv mode := by
    funext coordinate
    fin_cases coordinate <;> rfl

@[simp] theorem modeEquiv_apply (mode : FourierMode) :
    modeEquiv mode = modeVector mode := rfl

@[simp] theorem modeEquiv_symm_apply (mode : Fin 3 → ℤ) :
    modeEquiv.symm mode = vectorMode mode := rfl

/-- The product character with the probability Haar convention of P10. -/
def torusCharacter (mode : FourierMode) : C(ProductTorus, ℂ) :=
  UnitAddTorus.mFourier (modeVector mode)

/-- Embed physical period-four and period-`2π` representatives into the normalized torus. -/
def normalizedTorusPoint (y₁ y₂ ζ : ℝ) : ProductTorus :=
  ![((y₁ / 4 : ℝ) : UnitAddCircle), ((y₂ / 4 : ℝ) : UnitAddCircle),
    ((ζ / (2 * Real.pi) : ℝ) : UnitAddCircle)]

/-- On physical representatives the normalized product character is exactly P10's
`exp (i ((π/2) k₁ y₁ + (π/2) k₂ y₂ + n ζ))`. -/
theorem torusCharacter_normalized_apply (mode : FourierMode) (y₁ y₂ ζ : ℝ) :
    torusCharacter mode (normalizedTorusPoint y₁ y₂ ζ) =
      Complex.exp (Complex.I *
        (((Real.pi / 2) * mode.1) * y₁ +
          ((Real.pi / 2) * mode.2.1) * y₂ + mode.2.2 * ζ)) := by
  simp only [torusCharacter, normalizedTorusPoint, modeVector, UnitAddTorus.mFourier,
    ContinuousMap.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue,
    Fin.prod_univ_succ, Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton,
    fourier_coe_apply]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]
  ring

/- The imported product-torus Fourier theorems deliberately use local probability-Haar
instances.  We expose the same normalization, rather than the ambient length measure. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev ScalarTorusL2 := Lp ℂ 2 (volume : Measure ProductTorus)

/-- P10's scalar Fourier coefficient after the exact `ℤ³` reindexing. -/
def torusCoefficient (field : ScalarTorusL2) (mode : FourierMode) : ℂ :=
  UnitAddTorus.mFourierCoeff field (modeVector mode)

/-- The normalized character as an `L²` vector. -/
def torusCharacterL2 (mode : FourierMode) : ScalarTorusL2 :=
  UnitAddTorus.mFourierLp 2 (modeVector mode)

/-- P13: scalar Parseval on the probability product torus, with the paper's literal index. -/
theorem torus_parseval_hasSum (field : ScalarTorusL2) :
    HasSum (fun mode : FourierMode => ‖torusCoefficient field mode‖ ^ 2)
      (∫ point : ProductTorus, ‖field point‖ ^ 2) := by
  change HasSum
    ((fun index : Fin 3 → ℤ => ‖UnitAddTorus.mFourierCoeff field index‖ ^ 2) ∘ modeEquiv)
      (∫ point : ProductTorus, ‖field point‖ ^ 2)
  exact modeEquiv.hasSum_iff.mpr (UnitAddTorus.hasSum_sq_mFourierCoeff field)

theorem torus_parseval (field : ScalarTorusL2) :
    (∫ point : ProductTorus, ‖field point‖ ^ 2) =
      ∑' mode : FourierMode, ‖torusCoefficient field mode‖ ^ 2 :=
  (torus_parseval_hasSum field).tsum_eq.symm

/-- The complete scalar Fourier series converges in the actual `L²` norm. -/
theorem torus_fourier_series_L2 (field : ScalarTorusL2) :
    HasSum (fun mode : FourierMode => torusCoefficient field mode • torusCharacterL2 mode)
      field := by
  change HasSum
    ((fun index : Fin 3 → ℤ =>
      UnitAddTorus.mFourierCoeff field index • UnitAddTorus.mFourierLp 2 index) ∘ modeEquiv)
      field
  exact modeEquiv.hasSum_iff.mpr (UnitAddTorus.hasSum_mFourier_series_L2 field)

/-- Fourier coefficients of a continuous scalar field in the literal triple notation. -/
def continuousTorusCoefficient (field : C(ProductTorus, ℂ)) (mode : FourierMode) : ℂ :=
  UnitAddTorus.mFourierCoeff field (modeVector mode)

/-- Absolute coefficient summability gives uniform reconstruction, not merely an `L²` identity. -/
theorem torus_fourier_series_uniform {field : C(ProductTorus, ℂ)}
    (summable : Summable (continuousTorusCoefficient field)) :
    HasSum (fun mode : FourierMode =>
      continuousTorusCoefficient field mode • torusCharacter mode) field := by
  have reindexed : Summable (UnitAddTorus.mFourierCoeff field) := by
    exact modeEquiv.summable_iff.mp summable
  change HasSum
    ((fun index : Fin 3 → ℤ =>
      UnitAddTorus.mFourierCoeff field index • UnitAddTorus.mFourier index) ∘ modeEquiv) field
  exact modeEquiv.hasSum_iff.mpr
    (UnitAddTorus.hasSum_mFourier_series_of_summable reindexed)

/-- Actual finite-dimensional `L²` fields on the probability product torus. -/
abbrev EuclideanTorusL2 (dimension : ℕ) :=
  Lp (Grad.ClosedJets.ComplexEuclidean dimension) 2 (volume : Measure ProductTorus)

/-- The `coordinate` projection from the exact finite-dimensional value carrier. -/
def euclideanComponent (dimension : ℕ) (coordinate : Fin dimension) :
    Grad.ClosedJets.ComplexEuclidean dimension →L[ℂ] ℂ :=
  PiLp.proj 2 (fun _ : Fin dimension => ℂ) coordinate

/-- Apply a value-space coordinate projection to an `L²` field. -/
def euclideanComponentL2 {dimension : ℕ} (field : EuclideanTorusL2 dimension)
    (coordinate : Fin dimension) : ScalarTorusL2 :=
  (euclideanComponent dimension coordinate).compLp field

/-- The literal Bochner Fourier coefficient for a finite-dimensional field. -/
def euclideanTorusCoefficient {dimension : ℕ} (field : EuclideanTorusL2 dimension)
    (mode : FourierMode) : Grad.ClosedJets.ComplexEuclidean dimension :=
  UnitAddTorus.mFourierCoeff field (modeVector mode)

theorem euclideanComponentL2_ae {dimension : ℕ} (field : EuclideanTorusL2 dimension)
    (coordinate : Fin dimension) :
    (fun point : ProductTorus => euclideanComponentL2 field coordinate point) =ᵐ[volume]
      fun point => field point coordinate := by
  filter_upwards [(euclideanComponent dimension coordinate).coeFn_compLp field]
    with point equality
  simpa [euclideanComponentL2, euclideanComponent] using equality

theorem euclideanComponentL2_coefficient {dimension : ℕ}
    (field : EuclideanTorusL2 dimension) (coordinate : Fin dimension)
    (mode : FourierMode) :
    torusCoefficient (euclideanComponentL2 field coordinate) mode =
      euclideanTorusCoefficient field mode coordinate := by
  have componentIntegrable : ∀ index : Fin dimension,
      Integrable (fun point : ProductTorus => field point index) := by
    intro index
    have fromL2 : Integrable (fun point : ProductTorus =>
        euclideanComponentL2 field index point) :=
      (Lp.memLp (euclideanComponentL2 field index)).integrable (by norm_num)
    apply fromL2.congr
    filter_upwards [(euclideanComponent dimension index).coeFn_compLp field]
      with point equality
    exact equality
  have integrableCoordinates : ∀ index : Fin dimension,
      Integrable (fun point : ProductTorus =>
        (UnitAddTorus.mFourier (-(modeVector mode)) point • field point) index) := by
    intro index
    have bounded := (componentIntegrable index).bdd_smul 1
      (UnitAddTorus.mFourier (-(modeVector mode))).continuous.aestronglyMeasurable (by
        filter_upwards [] with point
        simp only [UnitAddTorus.mFourier, fourier_apply, ContinuousMap.coe_mk, norm_prod,
          Circle.norm_coe, Finset.prod_const_one, le_refl])
    apply bounded.congr
    filter_upwards [] with point
    rfl
  change ∫ point : ProductTorus,
      UnitAddTorus.mFourier (-(modeVector mode)) point •
        euclideanComponentL2 field coordinate point =
    (∫ point : ProductTorus,
      UnitAddTorus.mFourier (-(modeVector mode)) point • field point) coordinate
  rw [MeasureTheory.eval_integral_piLp integrableCoordinates coordinate]
  apply integral_congr_ae
  filter_upwards [(euclideanComponent dimension coordinate).coeFn_compLp field]
    with point equality
  change UnitAddTorus.mFourier (-(modeVector mode)) point •
      ((euclideanComponent dimension coordinate).compLp field) point =
    UnitAddTorus.mFourier (-(modeVector mode)) point • field point coordinate
  rw [equality]
  simp [euclideanComponent]

theorem euclidean_component_sq_integrable {dimension : ℕ}
    (field : EuclideanTorusL2 dimension) (coordinate : Fin dimension) :
    Integrable (fun point : ProductTorus => ‖field point coordinate‖ ^ 2) := by
  have componentMemLp := Lp.memLp (euclideanComponentL2 field coordinate)
  have componentIntegral : Integrable (fun point : ProductTorus =>
      ‖euclideanComponentL2 field coordinate point‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm componentMemLp.1).mp componentMemLp
  apply componentIntegral.congr
  filter_upwards [euclideanComponentL2_ae field coordinate] with point equality
  rw [equality]

/-- Coordinate form of P13, still using the actual vector-valued Bochner coefficient. -/
theorem euclidean_component_parseval {dimension : ℕ}
    (field : EuclideanTorusL2 dimension) (coordinate : Fin dimension) :
    (∫ point : ProductTorus, ‖field point coordinate‖ ^ 2) =
      ∑' mode : FourierMode, ‖euclideanTorusCoefficient field mode coordinate‖ ^ 2 := by
  calc
    (∫ point : ProductTorus, ‖field point coordinate‖ ^ 2) =
        ∫ point : ProductTorus, ‖euclideanComponentL2 field coordinate point‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [euclideanComponentL2_ae field coordinate] with point equality
      rw [equality]
    _ = ∑' mode : FourierMode,
        ‖torusCoefficient (euclideanComponentL2 field coordinate) mode‖ ^ 2 :=
      torus_parseval (euclideanComponentL2 field coordinate)
    _ = ∑' mode : FourierMode,
        ‖euclideanTorusCoefficient field mode coordinate‖ ^ 2 := by
      apply tsum_congr
      intro mode
      rw [euclideanComponentL2_coefficient]

theorem euclidean_component_sq_summable {dimension : ℕ}
    (field : EuclideanTorusL2 dimension) (coordinate : Fin dimension) :
    Summable (fun mode : FourierMode =>
      ‖euclideanTorusCoefficient field mode coordinate‖ ^ 2) := by
  have scalar := (torus_parseval_hasSum (euclideanComponentL2 field coordinate)).summable
  apply scalar.congr
  intro mode
  rw [euclideanComponentL2_coefficient]

/-- P13 for the actual finite-dimensional Euclidean-valued `L²` field. -/
theorem euclidean_torus_parseval {dimension : ℕ} (field : EuclideanTorusL2 dimension) :
    (∫ point : ProductTorus, ‖field point‖ ^ 2) =
      ∑' mode : FourierMode, ‖euclideanTorusCoefficient field mode‖ ^ 2 := by
  calc
    (∫ point : ProductTorus, ‖field point‖ ^ 2) =
        ∑ coordinate : Fin dimension,
          ∫ point : ProductTorus, ‖field point coordinate‖ ^ 2 := by
      rw [← integral_finsetSum Finset.univ (fun coordinate _ =>
        euclidean_component_sq_integrable field coordinate)]
      apply integral_congr_ae
      filter_upwards [] with point
      exact PiLp.norm_sq_eq_of_L2 (fun _ : Fin dimension => ℂ) (field point)
    _ = ∑ coordinate : Fin dimension,
        ∑' mode : FourierMode,
          ‖euclideanTorusCoefficient field mode coordinate‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro coordinate _
      exact euclidean_component_parseval field coordinate
    _ = ∑' mode : FourierMode,
        ∑ coordinate : Fin dimension,
          ‖euclideanTorusCoefficient field mode coordinate‖ ^ 2 := by
      exact (Summable.tsum_finsetSum (s := Finset.univ)
        (fun coordinate _ => euclidean_component_sq_summable field coordinate)).symm
    _ = ∑' mode : FourierMode, ‖euclideanTorusCoefficient field mode‖ ^ 2 := by
      apply tsum_congr
      intro mode
      exact (PiLp.norm_sq_eq_of_L2 (fun _ : Fin dimension => ℂ)
        (euclideanTorusCoefficient field mode)).symm

end Grad.FourierGrade

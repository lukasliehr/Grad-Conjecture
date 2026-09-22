import COR12Measure
import FP17Bijection

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Grad.COR12Extension

open Grad.ClosedJets
open Grad.CartesianState
open Grad.FourierGrade

local instance cor12ParsevalCellPeriodPositive : Fact (0 < (2 * Real.pi : ℝ)) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

abbrev CellScalarL2 :=
  Lp ℂ 2 (AddCircle.haarAddCircle : Measure CellCircle)

abbrev CellEuclideanL2 (dimension : ℕ) :=
  Lp (ComplexEuclidean dimension) 2
    (AddCircle.haarAddCircle : Measure CellCircle)

def cellEuclideanContinuousComponent {dimension : ℕ}
    (field : C(CellCircle, ComplexEuclidean dimension))
    (coordinate : Fin dimension) : C(CellCircle, ℂ) :=
  ⟨fun circle => euclideanComponent dimension coordinate (field circle),
    (euclideanComponent dimension coordinate).continuous.comp field.continuous⟩

theorem cellCircle_continuousMap_integrable
    {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    [CompleteSpace Value] (field : C(CellCircle, Value)) :
    Integrable field AddCircle.haarAddCircle := by
  have fromL2 :=
    (Lp.memLp (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ field)).integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  apply fromL2.congr
  exact ContinuousMap.coeFn_toLp AddCircle.haarAddCircle field

theorem cellEuclideanContinuousComponent_fourierCoeff {dimension : ℕ}
    (field : C(CellCircle, ComplexEuclidean dimension))
    (coordinate : Fin dimension) (cell : ℤ) :
    fourierCoeff field cell coordinate =
      fourierCoeff (cellEuclideanContinuousComponent field coordinate) cell := by
  let integrand : C(CellCircle, ComplexEuclidean dimension) :=
    ⟨fun circle => fourier (-cell) circle • field circle,
      (fourier (-cell)).continuous.smul field.continuous⟩
  have commutes := (euclideanComponent dimension coordinate).integral_comp_comm
    (cellCircle_continuousMap_integrable integrand)
  simpa [fourierCoeff, cellEuclideanContinuousComponent, integrand,
    euclideanComponent] using commutes.symm

def cellEuclideanComponentL2 {dimension : ℕ}
    (field : CellEuclideanL2 dimension) (coordinate : Fin dimension) :
    CellScalarL2 :=
  (euclideanComponent dimension coordinate).compLp field

def cellEuclideanCoefficient {dimension : ℕ}
    (field : CellEuclideanL2 dimension) (cell : ℤ) :
    ComplexEuclidean dimension :=
  fourierCoeff field cell

theorem cellEuclideanComponentL2_ae {dimension : ℕ}
    (field : CellEuclideanL2 dimension) (coordinate : Fin dimension) :
    (fun circle : CellCircle =>
      cellEuclideanComponentL2 field coordinate circle) =ᵐ[AddCircle.haarAddCircle]
      fun circle => field circle coordinate := by
  filter_upwards [(euclideanComponent dimension coordinate).coeFn_compLp field]
    with circle equality
  simpa [cellEuclideanComponentL2, euclideanComponent] using equality

theorem cellEuclideanComponentL2_coefficient {dimension : ℕ}
    (field : CellEuclideanL2 dimension) (coordinate : Fin dimension)
    (cell : ℤ) :
    fourierCoeff (cellEuclideanComponentL2 field coordinate) cell =
      cellEuclideanCoefficient field cell coordinate := by
  have componentIntegrable : ∀ index : Fin dimension,
      Integrable (fun circle : CellCircle => field circle index)
        AddCircle.haarAddCircle := by
    intro index
    have fromL2 : Integrable (fun circle : CellCircle =>
        cellEuclideanComponentL2 field index circle)
        AddCircle.haarAddCircle :=
      (Lp.memLp (cellEuclideanComponentL2 field index)).integrable (by norm_num)
    apply fromL2.congr
    filter_upwards [cellEuclideanComponentL2_ae field index]
      with circle equality
    exact equality
  have integrableCoordinates : ∀ index : Fin dimension,
      Integrable (fun circle : CellCircle =>
        (fourier (-cell) circle • field circle) index)
        AddCircle.haarAddCircle := by
    intro index
    have bounded := (componentIntegrable index).bdd_smul 1
      (fourier (-cell)).continuous.aestronglyMeasurable (by
        filter_upwards [] with circle
        have normIdentity : ‖fourier (-cell) circle‖ = 1 := by
          simpa only [fourier_apply] using
            (Circle.norm_coe (AddCircle.toCircle ((-cell) • circle :)))
        exact normIdentity.le)
    apply bounded.congr
    filter_upwards [] with circle
    rfl
  change (∫ circle : CellCircle,
      fourier (-cell) circle •
        cellEuclideanComponentL2 field coordinate circle
        ∂AddCircle.haarAddCircle) =
    (∫ circle : CellCircle,
      fourier (-cell) circle • field circle
        ∂AddCircle.haarAddCircle) coordinate
  rw [MeasureTheory.eval_integral_piLp integrableCoordinates coordinate]
  apply integral_congr_ae
  filter_upwards [cellEuclideanComponentL2_ae field coordinate]
    with circle equality
  exact congrArg (fun value : ℂ => fourier (-cell) circle • value) equality

theorem cellEuclideanComponent_sq_integrable {dimension : ℕ}
    (field : CellEuclideanL2 dimension) (coordinate : Fin dimension) :
    Integrable (fun circle : CellCircle => ‖field circle coordinate‖ ^ 2)
      AddCircle.haarAddCircle := by
  have componentMemLp := Lp.memLp (cellEuclideanComponentL2 field coordinate)
  have componentIntegral : Integrable (fun circle : CellCircle =>
      ‖cellEuclideanComponentL2 field coordinate circle‖ ^ 2)
      AddCircle.haarAddCircle :=
    (memLp_two_iff_integrable_sq_norm componentMemLp.1).mp componentMemLp
  apply componentIntegral.congr
  filter_upwards [cellEuclideanComponentL2_ae field coordinate]
    with circle equality
  rw [equality]

theorem cellEuclideanComponent_parseval {dimension : ℕ}
    (field : CellEuclideanL2 dimension) (coordinate : Fin dimension) :
    (∫ circle : CellCircle, ‖field circle coordinate‖ ^ 2
        ∂AddCircle.haarAddCircle) =
      ∑' cell : ℤ, ‖cellEuclideanCoefficient field cell coordinate‖ ^ 2 := by
  calc
    (∫ circle : CellCircle, ‖field circle coordinate‖ ^ 2
        ∂AddCircle.haarAddCircle) =
        ∫ circle : CellCircle,
          ‖cellEuclideanComponentL2 field coordinate circle‖ ^ 2
            ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [cellEuclideanComponentL2_ae field coordinate]
        with circle equality
      rw [equality]
    _ = ∑' cell : ℤ,
        ‖fourierCoeff (cellEuclideanComponentL2 field coordinate) cell‖ ^ 2 :=
      (tsum_sq_fourierCoeff (cellEuclideanComponentL2 field coordinate)).symm
    _ = ∑' cell : ℤ,
        ‖cellEuclideanCoefficient field cell coordinate‖ ^ 2 := by
      apply tsum_congr
      intro cell
      rw [cellEuclideanComponentL2_coefficient]

theorem cellEuclideanComponent_sq_summable {dimension : ℕ}
    (field : CellEuclideanL2 dimension) (coordinate : Fin dimension) :
    Summable (fun cell : ℤ =>
      ‖cellEuclideanCoefficient field cell coordinate‖ ^ 2) := by
  have scalar :=
    (hasSum_sq_fourierCoeff
      (cellEuclideanComponentL2 field coordinate)).summable
  apply scalar.congr
  intro cell
  rw [cellEuclideanComponentL2_coefficient]

theorem cell_euclidean_parseval {dimension : ℕ}
    (field : CellEuclideanL2 dimension) :
    (∫ circle : CellCircle, ‖field circle‖ ^ 2
        ∂AddCircle.haarAddCircle) =
      ∑' cell : ℤ, ‖cellEuclideanCoefficient field cell‖ ^ 2 := by
  calc
    (∫ circle : CellCircle, ‖field circle‖ ^ 2
        ∂AddCircle.haarAddCircle) =
        ∑ coordinate : Fin dimension,
          ∫ circle : CellCircle, ‖field circle coordinate‖ ^ 2
            ∂AddCircle.haarAddCircle := by
      rw [← integral_finsetSum Finset.univ (fun coordinate _ =>
        cellEuclideanComponent_sq_integrable field coordinate)]
      apply integral_congr_ae
      filter_upwards [] with circle
      exact PiLp.norm_sq_eq_of_L2
        (fun _ : Fin dimension => ℂ) (field circle)
    _ = ∑ coordinate : Fin dimension,
        ∑' cell : ℤ,
          ‖cellEuclideanCoefficient field cell coordinate‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro coordinate _
      exact cellEuclideanComponent_parseval field coordinate
    _ = ∑' cell : ℤ,
        ∑ coordinate : Fin dimension,
          ‖cellEuclideanCoefficient field cell coordinate‖ ^ 2 := by
      exact (Summable.tsum_finsetSum (s := Finset.univ)
        (fun coordinate _ =>
          cellEuclideanComponent_sq_summable field coordinate)).symm
    _ = ∑' cell : ℤ,
        ‖cellEuclideanCoefficient field cell‖ ^ 2 := by
      apply tsum_congr
      intro cell
      exact (PiLp.norm_sq_eq_of_L2
        (fun _ : Fin dimension => ℂ)
        (cellEuclideanCoefficient field cell)).symm

theorem cellEuclideanCoefficient_continuousToLp {dimension : ℕ}
    (field : C(CellCircle, ComplexEuclidean dimension)) (cell : ℤ) :
    cellEuclideanCoefficient
        (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ field) cell =
      fourierCoeff field cell := by
  ext coordinate
  calc
    cellEuclideanCoefficient
        (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ field) cell coordinate =
        fourierCoeff
          (cellEuclideanComponentL2
            (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ field) coordinate)
          cell :=
      (cellEuclideanComponentL2_coefficient
        (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ field)
        coordinate cell).symm
    _ = fourierCoeff
        (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
          (cellEuclideanContinuousComponent field coordinate)) cell := by
      apply congrArg (fun source : CellScalarL2 => fourierCoeff source cell)
      apply Lp.ext
      filter_upwards [
          cellEuclideanComponentL2_ae
            (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ field) coordinate,
          ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (𝕜 := ℂ)
            AddCircle.haarAddCircle field,
          ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (𝕜 := ℂ)
            AddCircle.haarAddCircle
            (cellEuclideanContinuousComponent field coordinate)]
          with circle component vector scalar
      rw [component, vector, scalar]
      rfl
    _ = fourierCoeff (cellEuclideanContinuousComponent field coordinate) cell :=
      fourierCoeff_toLp (cellEuclideanContinuousComponent field coordinate) cell
    _ = fourierCoeff field cell coordinate := by
      exact (cellEuclideanContinuousComponent_fourierCoeff
        field coordinate cell).symm

theorem cell_euclidean_continuous_parseval {dimension : ℕ}
    (field : C(CellCircle, ComplexEuclidean dimension)) :
    (∫ circle : CellCircle, ‖field circle‖ ^ 2
        ∂AddCircle.haarAddCircle) =
      ∑' cell : ℤ, ‖fourierCoeff field cell‖ ^ 2 := by
  calc
    (∫ circle : CellCircle, ‖field circle‖ ^ 2
        ∂AddCircle.haarAddCircle) =
        ∫ circle : CellCircle,
          ‖(ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ field) circle‖ ^ 2
            ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp
        (p := (2 : ℝ≥0∞)) (𝕜 := ℂ)
        AddCircle.haarAddCircle field] with circle equality
      rw [equality]
    _ = ∑' cell : ℤ,
        ‖cellEuclideanCoefficient
          (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ field) cell‖ ^ 2 :=
      cell_euclidean_parseval
        (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ field)
    _ = ∑' cell : ℤ, ‖fourierCoeff field cell‖ ^ 2 := by
      apply tsum_congr
      intro cell
      rw [cellEuclideanCoefficient_continuousToLp]

end Grad.COR12Extension

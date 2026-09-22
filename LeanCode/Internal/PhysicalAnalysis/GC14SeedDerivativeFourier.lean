import GC14SeedDerivativeCoefficient
import Mathlib.Analysis.Calculus.SmoothSeries

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Physical.Frame

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

def seedOrigin : ClosedDisk := ⟨0, by simp [closedUnitDisk]⟩

theorem seedValue_norm_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (rho alpha delta parameter : ℝ) :
    Summable (fun cell : ℤ => ‖seedDeviationCell rho alpha delta parameter cell‖) := by
  have each (cell : ℤ) : coefficientValue
      (seedMatrixDeviationCoefficient admissible 0 rho alpha delta parameter) cell seedOrigin =
        seedDeviationCell rho alpha delta parameter cell :=
    seedMatrixDeviation_cell admissible 0 rho alpha delta parameter cell seedOrigin
  exact (coefficientValue_point_norm_summable admissible
    (seedMatrixDeviationCoefficient admissible 0 rho alpha delta parameter) seedOrigin).congr
      (fun cell => congrArg norm (each cell))

theorem seedDerivativeValue_norm_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (rho alpha delta parameter : ℝ) :
    Summable (fun cell : ℤ => ‖scaledSeedDerivativeCell L ell rho alpha delta parameter cell‖) := by
  have each (cell : ℤ) : coefficientValue
      (seedDerivativeCoefficient admissible 0 rho alpha delta parameter) cell seedOrigin =
        scaledSeedDerivativeCell L ell rho alpha delta parameter cell := by
    change coefficientDerivative _ cell zeroDerivativeIndex seedOrigin = _
    rw [seedDerivativeCoefficient_derivative]
    rfl
  exact (coefficientValue_point_norm_summable admissible
    (seedDerivativeCoefficient admissible 0 rho alpha delta parameter) seedOrigin).congr
      (fun cell => congrArg norm (each cell))

theorem seedValue_fourier {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (rho alpha delta parameter angle : ℝ) :
    (∑' cell : ℤ, cellExponential cell angle • seedDeviationCell rho alpha delta parameter cell) =
      harmonicSeedOperator rho alpha delta parameter angle - ContinuousLinearMap.id ℂ (ComplexEuclidean 2) := by
  have each (cell : ℤ) : coefficientValue
      (seedMatrixDeviationCoefficient admissible 0 rho alpha delta parameter) cell seedOrigin =
        seedDeviationCell rho alpha delta parameter cell :=
    seedMatrixDeviation_cell admissible 0 rho alpha delta parameter cell seedOrigin
  have reconstruction := seedMatrixDeviation_fourier admissible rho alpha delta parameter angle seedOrigin
  change (∑' cell : ℤ, cellExponential cell angle • coefficientValue
    (seedMatrixDeviationCoefficient admissible 0 rho alpha delta parameter) cell seedOrigin) = _ at reconstruction
  simpa only [each] using reconstruction

theorem seedCharacter_hasDerivAt (cell : ℤ) (angle : ℝ) :
    HasDerivAt (cellExponential cell) ((Complex.I * (cell : ℂ)) * cellExponential cell angle) angle := by
  convert (cellExponential_hasFDerivAt cell angle).hasDerivAt using 1
  simp [cellExponentialDerivative]

theorem seedDerivativeValue_fourier {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (rho alpha delta parameter angle : ℝ) :
    (∑' cell : ℤ, cellExponential cell angle • scaledSeedDerivativeCell L ell rho alpha delta parameter cell) =
      ((ell / L : ℝ) : ℂ) • deriv (harmonicSeedOperator rho alpha delta parameter) angle := by
  let scalar : ℂ := ((ell / L : ℝ) : ℂ)
  let term (cell : ℤ) (coordinate : ℝ) : OperatorValue 2 2 :=
    cellExponential cell coordinate • (scalar • seedDeviationCell rho alpha delta parameter cell)
  let derivativeTerm (cell : ℤ) (coordinate : ℝ) : OperatorValue 2 2 :=
    cellExponential cell coordinate • scaledSeedDerivativeCell L ell rho alpha delta parameter cell
  have sourceNorms := seedValue_norm_summable admissible rho alpha delta parameter
  have derivativeNorms := seedDerivativeValue_norm_summable admissible rho alpha delta parameter
  have sourceSeries (coordinate : ℝ) : Summable (fun cell : ℤ =>
      cellExponential cell coordinate • seedDeviationCell rho alpha delta parameter cell) :=
    Summable.of_norm_bounded sourceNorms (fun cell => by rw [norm_smul, cellExponential_norm, one_mul])
  have termDerivative (cell : ℤ) (coordinate : ℝ) :
      HasDerivAt (term cell) (derivativeTerm cell coordinate) coordinate := by
    have raw := (seedCharacter_hasDerivAt cell coordinate).smul_const
      (scalar • seedDeviationCell rho alpha delta parameter cell)
    convert raw using 1 <;> try rfl
    unfold derivativeTerm scaledSeedDerivativeCell scalar
    apply ContinuousLinearMap.ext
    intro vector
    apply PiLp.ext
    intro index
    simp only [smul_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have derivativeBound (cell : ℤ) (coordinate : ℝ) :
      ‖derivativeTerm cell coordinate‖ ≤ ‖scaledSeedDerivativeCell L ell rho alpha delta parameter cell‖ := by
    unfold derivativeTerm
    rw [norm_smul, cellExponential_norm, one_mul]
  have initial : Summable (fun cell : ℤ => term cell 0) := by
    have scaled := sourceNorms.of_norm.const_smul scalar
    simpa only [term, cellExponential, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul] using scaled
  have derivative := hasDerivAt_tsum derivativeNorms termDerivative derivativeBound initial angle
  have functionIdentity (coordinate : ℝ) : (∑' cell : ℤ, term cell coordinate) =
      scalar • (harmonicSeedOperator rho alpha delta parameter coordinate -
        ContinuousLinearMap.id ℂ (ComplexEuclidean 2)) := by
    rw [← seedValue_fourier admissible rho alpha delta parameter coordinate,
      ← (sourceSeries coordinate).tsum_const_smul scalar]
    apply tsum_congr
    intro cell
    exact smul_comm _ _ _
  have actualDerivative : HasDerivAt (fun coordinate => scalar •
      (harmonicSeedOperator rho alpha delta parameter coordinate -
        ContinuousLinearMap.id ℂ (ComplexEuclidean 2))) (∑' cell : ℤ, derivativeTerm cell angle) angle := by
    simpa only [functionIdentity] using derivative
  have nonzero : scalar ≠ 0 := Complex.ofReal_ne_zero.mpr
    (div_ne_zero admissible.2.2.2.1.ne' admissible.1.ne')
  have unscaled : HasDerivAt (fun coordinate => harmonicSeedOperator rho alpha delta parameter coordinate -
      ContinuousLinearMap.id ℂ (ComplexEuclidean 2))
      (scalar⁻¹ • (∑' cell : ℤ, derivativeTerm cell angle)) angle := by
    have back := actualDerivative.const_smul scalar⁻¹
    have cancelFunction : scalar⁻¹ • (fun coordinate : ℝ => scalar •
        (harmonicSeedOperator rho alpha delta parameter coordinate -
          ContinuousLinearMap.id ℂ (ComplexEuclidean 2))) =
        (fun coordinate : ℝ => harmonicSeedOperator rho alpha delta parameter coordinate -
          ContinuousLinearMap.id ℂ (ComplexEuclidean 2)) := by
      funext coordinate
      change scalar⁻¹ • (scalar • (harmonicSeedOperator rho alpha delta parameter coordinate -
        ContinuousLinearMap.id ℂ (ComplexEuclidean 2))) = _
      rw [smul_smul, inv_mul_cancel₀ nonzero, one_smul]
    rw [cancelFunction] at back
    exact back
  have original : HasDerivAt (harmonicSeedOperator rho alpha delta parameter)
      (scalar⁻¹ • (∑' cell : ℤ, derivativeTerm cell angle)) angle := by
    simpa only [sub_add_cancel] using unscaled.add_const (ContinuousLinearMap.id ℂ (ComplexEuclidean 2))
  rw [original.deriv]
  change (∑' cell : ℤ, derivativeTerm cell angle) = scalar • (scalar⁻¹ • (∑' cell : ℤ, derivativeTerm cell angle))
  rw [smul_smul, mul_inv_cancel₀ nonzero, one_smul]

end Grad.GaugeCoefficients.Physical.Frame

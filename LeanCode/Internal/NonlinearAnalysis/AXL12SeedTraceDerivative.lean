import AXL9StoredPoloidal

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.Frame

theorem harmonicSeed_hasDerivAt (parameters : PhaseParameters) (seed : Seed.Parameters)
    (inside : seed ∈ Seed.parameterDomain) (angle : ℝ) :
    HasDerivAt (harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3))
      (deriv (harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3)) angle) angle := by
  let term (cell : ℤ) (coordinate : ℝ) : Grad.GaugeCoefficients.Algebra.OperatorValue 2 2 :=
    cellExponential cell coordinate • Seed.actualCells 0 seed cell
  let derivativeTerm (cell : ℤ) (coordinate : ℝ) : Grad.GaugeCoefficients.Algebra.OperatorValue 2 2 :=
    cellExponential cell coordinate • Seed.actualCells 2 seed cell
  have norms := Gauges.coefficientNorm_summable parameters _ (Gauges.seedCells_all_summable parameters seed inside 0 0)
  have derivativeNorms := Gauges.coefficientNorm_summable parameters _
    (Gauges.seedCells_all_summable parameters seed inside 2 0)
  have each (cell : ℤ) (coordinate : ℝ) : HasDerivAt (term cell) (derivativeTerm cell coordinate) coordinate := by
    have raw := (seedCharacter_hasDerivAt cell coordinate).smul_const (Seed.actualCells 0 seed cell)
    convert raw using 1 <;> try rfl
    change cellExponential cell coordinate • ((Complex.I * (cell : ℂ)) •
      seedDeviationCell (seed 0) (seed 1) (seed 2) (seed 3) cell) = _
    rw [smul_smul]
    congr 1
    ring
  have bound (cell : ℤ) (coordinate : ℝ) : ‖derivativeTerm cell coordinate‖ ≤ ‖Seed.actualCells 2 seed cell‖ := by
    dsimp only [derivativeTerm]
    rw [norm_smul, cellExponential_norm, one_mul]
  have initial : Summable (fun cell : ℤ => term cell 0) := by
    simpa only [term, cellExponential, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul] using norms.of_norm
  have summed := hasDerivAt_tsum derivativeNorms each bound initial angle
  have identity (coordinate : ℝ) : (∑' cell : ℤ, term cell coordinate) =
      harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3) coordinate -
        ContinuousLinearMap.id ℂ (ComplexEuclidean 2) := (Seed.actual_seed_fourier parameters seed inside coordinate).1
  have target := summed.add_const (ContinuousLinearMap.id ℂ (ComplexEuclidean 2))
  simpa only [identity, sub_add_cancel, derivativeTerm,
    (Seed.actual_seed_fourier parameters seed inside angle).2.2] using target

/-- Continuous extraction of one literal matrix entry. -/
def operatorEntryContinuous (row column : Fin 2) :
    (ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun mapping => Gauges.operatorEntry mapping row column
      map_add' := fun _ _ => Gauges.operatorEntry_add _ _ _ _
      map_smul' := fun _ _ => Gauges.operatorEntry_smul _ _ _ _ }
    1 (fun mapping => by
      change ‖Gauges.operatorEntry mapping row column‖ ≤ 1 * ‖mapping‖
      rw [one_mul]
      exact Gauges.operatorEntry_norm_le mapping row column)

theorem seedDerivative_trace_zero (parameters : PhaseParameters) (seed : Seed.Parameters)
    (inside : seed ∈ Seed.parameterDomain) (angle : ℝ) :
    Gauges.operatorTrace ((Gauges.transposeOperator
      (deriv (harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3)) angle)).comp
      (harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3) angle)) = 0 := by
  let matrix := harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3)
  have each (row column : Fin 2) : HasDerivAt (fun coordinate => Gauges.operatorEntry (matrix coordinate) row column)
      (Gauges.operatorEntry (deriv matrix angle) row column) angle :=
    ((operatorEntryContinuous row column).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt angle
      (harmonicSeed_hasDerivAt parameters seed inside angle)
  have squared := (((each 0 0).pow 2).add ((each 1 0).pow 2)).add
    (((each 0 1).pow 2).add ((each 1 1).pow 2))
  have identity (coordinate : ℝ) :
      Gauges.operatorEntry (matrix coordinate) 0 0 ^ 2 + Gauges.operatorEntry (matrix coordinate) 1 0 ^ 2 +
      (Gauges.operatorEntry (matrix coordinate) 0 1 ^ 2 + Gauges.operatorEntry (matrix coordinate) 1 1 ^ 2) = 2 := by
    rw [← add_assoc, ← Gauges.transposeOperator_comp_trace]
    exact Gauges.seedMatrix_trace_pointwise seed inside coordinate
  simp only [Pi.add_def, Pi.pow_def, identity] at squared
  norm_num only at squared
  have zero := squared.unique (hasDerivAt_const angle (2 : ℂ))
  change Gauges.operatorTrace ((Gauges.transposeOperator (deriv matrix angle)).comp (matrix angle)) = 0
  simp only [Gauges.operatorTrace, Gauges.operatorEntry_comp, Gauges.transposeOperator_entry]
  linear_combination (1 / 2 : ℂ) * zero

end Grad.ChartAxisLift

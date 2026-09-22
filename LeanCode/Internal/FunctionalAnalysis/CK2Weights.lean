import CK1Pair

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open scoped BigOperators Topology

namespace Grad.RepresentedKernel.Composition.Countable

theorem row_product_summable (first second : ℤ → ℤ → ℝ) (firstBound secondBound : ℝ)
    (firstNonnegative : ∀ output input, 0 ≤ first output input)
    (secondNonnegative : ∀ output input, 0 ≤ second output input)
    (firstRows : ∀ output, Summable (first output))
    (secondRows : ∀ output, Summable (second output))
    (firstBounded : ∀ output, ∑' input, first output input ≤ firstBound)
    (secondBounded : ∀ output, ∑' input, second output input ≤ secondBound)
    (secondBoundNonnegative : 0 ≤ secondBound) (output : ℤ) :
    Summable (fun pair : ℤ × ℤ => first output pair.1 * second pair.1 pair.2) ∧
      Summable (fun input : ℤ => ∑' middle : ℤ, first output middle * second middle input) ∧
      (∑' input : ℤ, ∑' middle : ℤ, first output middle * second middle input) ≤ firstBound * secondBound := by
  have nonnegative (pair : ℤ × ℤ) : 0 ≤ first output pair.1 * second pair.1 pair.2 :=
    mul_nonneg (firstNonnegative _ _) (secondNonnegative _ _)
  have each (middle : ℤ) : Summable (fun input : ℤ => first output middle * second middle input) :=
    (secondRows middle).mul_left (first output middle)
  have rowBound (middle : ℤ) :
      (∑' input : ℤ, first output middle * second middle input) ≤ first output middle * secondBound := by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (secondBounded middle) (firstNonnegative _ _)
  have rowSums : Summable (fun middle : ℤ => ∑' input : ℤ, first output middle * second middle input) :=
    Summable.of_nonneg_of_le (fun middle => tsum_nonneg (fun input => nonnegative (middle, input)))
      rowBound ((firstRows output).mul_right secondBound)
  have total : Summable (fun pair : ℤ × ℤ => first output pair.1 * second pair.1 pair.2) :=
    (summable_prod_of_nonneg nonnegative).mpr ⟨each, rowSums⟩
  refine ⟨total, total.prod_symm.prod, ?_⟩
  calc
    _ = ∑' middle : ℤ, ∑' input : ℤ, first output middle * second middle input := total.tsum_comm
    _ ≤ ∑' middle : ℤ, first output middle * secondBound :=
      Summable.tsum_le_tsum rowBound rowSums ((firstRows output).mul_right secondBound)
    _ = (∑' middle : ℤ, first output middle) * secondBound := tsum_mul_right
    _ ≤ _ := mul_le_mul_of_nonneg_right (firstBounded output) secondBoundNonnegative

variable {Outer Inner : Type*} [MeasurableSpace Outer] [MeasurableSpace Inner]
  {outerMeasure : Measure Outer} {innerMeasure : Measure Inner}
  [SigmaFinite outerMeasure] [SigmaFinite innerMeasure]
  {inputDimension middleDimension outputDimension : ℕ} {domain : Set Spatial}
  (outer : Grad.FullCellKernel.L2KernelData outerMeasure middleDimension outputDimension domain)
  (inner : Grad.FullCellKernel.L2KernelData innerMeasure inputDimension middleDimension domain)

def middleWeight (output input middle : ℤ) : ℝ :=
  Grad.FullCellKernel.integratedWeight outer output middle * Grad.FullCellKernel.integratedWeight inner middle input

def combinedWeight (output input : ℤ) : ℝ := ∑' middle : ℤ, middleWeight outer inner output input middle

omit [SigmaFinite outerMeasure] [SigmaFinite innerMeasure] in
theorem middleWeight_nonnegative (output input middle : ℤ) : 0 ≤ middleWeight outer inner output input middle :=
  mul_nonneg (Grad.FullCellKernel.integratedWeight_nonneg outer output middle)
    (Grad.FullCellKernel.integratedWeight_nonneg inner middle input)

omit [SigmaFinite outerMeasure] [SigmaFinite innerMeasure] in
theorem rowProducts_summable (output : ℤ) :
    Summable (fun pair : ℤ × ℤ => middleWeight outer inner output pair.2 pair.1) ∧
      Summable (combinedWeight outer inner output) ∧
      (∑' input : ℤ, combinedWeight outer inner output input) ≤ outer.rowBound * inner.rowBound :=
  row_product_summable (Grad.FullCellKernel.integratedWeight outer) (Grad.FullCellKernel.integratedWeight inner)
    outer.rowBound inner.rowBound (Grad.FullCellKernel.integratedWeight_nonneg outer)
    (Grad.FullCellKernel.integratedWeight_nonneg inner) outer.rowsSummable inner.rowsSummable
    outer.rows inner.rows inner.rowNonnegative output

omit [SigmaFinite outerMeasure] [SigmaFinite innerMeasure] in
theorem middleWeight_summable (output input : ℤ) : Summable (middleWeight outer inner output input) :=
  (rowProducts_summable outer inner output).1.prod_symm.prod_factor input

omit [SigmaFinite outerMeasure] [SigmaFinite innerMeasure] in
theorem combinedWeight_nonnegative (output input : ℤ) : 0 ≤ combinedWeight outer inner output input :=
  tsum_nonneg (middleWeight_nonnegative outer inner output input)

omit [SigmaFinite outerMeasure] [SigmaFinite innerMeasure] in
theorem columnProducts_summable (input : ℤ) :
    Summable (fun output : ℤ => combinedWeight outer inner output input) ∧
      (∑' output : ℤ, combinedWeight outer inner output input) ≤ outer.columnBound * inner.columnBound := by
  have result := row_product_summable (fun input middle => Grad.FullCellKernel.integratedWeight inner middle input)
    (fun middle output => Grad.FullCellKernel.integratedWeight outer output middle)
    inner.columnBound outer.columnBound
    (fun input middle => Grad.FullCellKernel.integratedWeight_nonneg inner middle input)
    (fun middle output => Grad.FullCellKernel.integratedWeight_nonneg outer output middle)
    inner.columnsSummable outer.columnsSummable inner.columns outer.columns outer.columnNonnegative input
  simpa only [combinedWeight, middleWeight, mul_comm] using result.2

theorem pairOperator_norm_summable (output input : ℤ) :
    Summable (fun middle : ℤ => ‖pairOperator outer inner output middle input‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun middle => pairOperator_norm_le outer inner output middle input)
    (middleWeight_summable outer inner output input)

theorem pairOperator_summable (output input : ℤ) :
    Summable (fun middle : ℤ => pairOperator outer inner output middle input) :=
  (pairOperator_norm_summable outer inner output input).of_norm

def combinedEntry (output input : ℤ) :
    DomainL2 (PhysicalValue inputDimension) domain →L[ℂ] DomainL2 (PhysicalValue outputDimension) domain :=
  ∑' middle : ℤ, pairOperator outer inner output middle input

theorem combinedEntry_norm_le (output input : ℤ) :
    ‖combinedEntry outer inner output input‖ ≤ combinedWeight outer inner output input := by
  exact (norm_tsum_le_tsum_norm (pairOperator_norm_summable outer inner output input)).trans
    (Summable.tsum_le_tsum (fun middle => pairOperator_norm_le outer inner output middle input)
      (pairOperator_norm_summable outer inner output input) (middleWeight_summable outer inner output input))

end Grad.RepresentedKernel.Composition.Countable

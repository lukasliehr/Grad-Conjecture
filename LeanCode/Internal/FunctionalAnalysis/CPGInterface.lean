import SI3Proof
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Grad.CellProjections.Generic

def projection (Value : Type*) [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (cells : Finset ℤ) : lp (fun _ : ℤ => Value) 2 →L[ℂ] lp (fun _ : ℤ => Value) 2 :=
  ∑ cell ∈ cells, (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => Value) 2 cell).comp
    (lp.evalCLM ℂ (fun _ : ℤ => Value) 2 cell)

def fieldProjection {Space : Type*} [MeasurableSpace Space] (measure : Measure Space)
    (Value : Type*) [NormedAddCommGroup Value] [NormedSpace ℂ Value] (cells : Finset ℤ) :
    Lp (lp (fun _ : ℤ => Value) 2) 2 measure →L[ℂ] Lp (lp (fun _ : ℤ => Value) 2) 2 measure :=
  (projection Value cells).compLpL 2 measure

def ProjectionGoal {Space Value : Type*} [MeasurableSpace Space]
    [NormedAddCommGroup Value] [InnerProductSpace ℂ Value] (measure : Measure Space) : Prop :=
  (∀ (cells : Finset ℤ) (field : Lp (lp (fun _ : ℤ => Value) 2) 2 measure),
    (∀ᵐ point ∂measure, ∀ cell : ℤ,
      fieldProjection measure Value cells field point cell = if cell ∈ cells then field point cell else 0) ∧
    ‖fieldProjection measure Value cells field‖ ≤ ‖field‖ ∧
    fieldProjection measure Value cells (fieldProjection measure Value cells field) =
      fieldProjection measure Value cells field) ∧
  (∀ cells : Finset ℤ, ‖fieldProjection measure Value cells‖ ≤ 1) ∧
  ∀ field : Lp (lp (fun _ : ℤ => Value) 2) 2 measure,
    Tendsto (fun cells : Finset ℤ => fieldProjection measure Value cells field) atTop (𝓝 field)

def RectangularSectionsGoal {Space ValueIn ValueOut : Type*} [MeasurableSpace Space]
    [NormedAddCommGroup ValueIn] [InnerProductSpace ℂ ValueIn]
    [NormedAddCommGroup ValueOut] [InnerProductSpace ℂ ValueOut] (measure : Measure Space) : Prop :=
  ∀ (operator : Lp (lp (fun _ : ℤ => ValueIn) 2) 2 measure →L[ℂ]
      Lp (lp (fun _ : ℤ => ValueOut) 2) 2 measure)
    (field : Lp (lp (fun _ : ℤ => ValueIn) 2) 2 measure),
    Tendsto (fun cells : Finset ℤ => fieldProjection measure ValueOut cells
      (operator (fieldProjection measure ValueIn cells field))) atTop (𝓝 (operator field))

def finiteCellField {Space Value : Type*} [MeasurableSpace Space] [NormedAddCommGroup Value]
    (measure : Measure Space) (field : Lp (lp (fun _ : ℤ => Value) 2) 2 measure) : Prop :=
  ∃ cells : Finset ℤ, ∀ᵐ point ∂measure, ∀ cell : ℤ, cell ∉ cells → field point cell = 0

def DensityGoal {Space Value : Type*} [MeasurableSpace Space]
    [NormedAddCommGroup Value] [InnerProductSpace ℂ Value] (measure : Measure Space) : Prop :=
  Dense {field : Lp (lp (fun _ : ℤ => Value) 2) 2 measure | finiteCellField measure field}

end Grad.CellProjections.Generic

#check Grad.SchurKernel.RealEnergy.realLp_norm_sq
#check lp.hasSum_single
#check lp.norm_mono
#check ContinuousLinearMap.norm_compLpL_le
#check Lp.coeFn_sub
#check tendsto_integral_filter_of_dominated_convergence
#check IsClosed.mem_of_tendsto
#check subset_closure

section
variable {Value : Type*} [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
  (measure : Measure Grad.PDEBootstrap.Spatial)
  (field : Lp (lp (fun _ : ℤ => Value) 2) 2 measure)
example : ‖field‖ ^ 2 = ∫ point, ‖field point‖ ^ 2 ∂measure := by
  let := InnerProductSpace.rclikeToReal ℂ Value
  exact Grad.SchurKernel.RealEnergy.realLp_norm_sq measure field
end

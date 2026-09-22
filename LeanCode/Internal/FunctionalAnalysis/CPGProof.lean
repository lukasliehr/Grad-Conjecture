import CPGInterface

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Grad.CellProjections.Generic

section Values

variable (Value : Type*) [NormedAddCommGroup Value] [NormedSpace ℂ Value]

theorem projection_apply (cells : Finset ℤ) (value : lp (fun _ : ℤ => Value) 2) :
    projection Value cells value = ∑ cell ∈ cells, lp.single 2 cell (value cell) := by
  simp only [projection, sum_apply, ContinuousLinearMap.comp_apply,
    lp.singleContinuousLinearMap_apply]
  rfl

theorem projection_coordinate (cells : Finset ℤ) (value : lp (fun _ : ℤ => Value) 2) (cell : ℤ) :
    projection Value cells value cell = if cell ∈ cells then value cell else 0 := by
  rw [projection_apply]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Finset.sum_pi_single]

theorem projection_norm_apply (cells : Finset ℤ) (value : lp (fun _ : ℤ => Value) 2) :
    ‖projection Value cells value‖ ≤ ‖value‖ := by
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro cell
  rw [projection_coordinate]
  split_ifs <;> simp

theorem projection_norm_le (cells : Finset ℤ) : ‖projection Value cells‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro value
  simpa only [one_mul] using projection_norm_apply Value cells value

theorem projection_strong (value : lp (fun _ : ℤ => Value) 2) :
    Tendsto (fun cells : Finset ℤ => projection Value cells value) atTop (𝓝 value) := by
  simpa only [HasSum, SummationFilter.unconditional, projection_apply] using
    (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) value)

theorem projection_idempotent (cells : Finset ℤ) (value : lp (fun _ : ℤ => Value) 2) :
    projection Value cells (projection Value cells value) = projection Value cells value := by
  apply lp.ext
  funext cell
  change projection Value cells (projection Value cells value) cell = projection Value cells value cell
  rw [projection_coordinate]
  by_cases membership : cell ∈ cells
  · rw [if_pos membership]
  · rw [if_neg membership, projection_coordinate, if_neg membership]

theorem complement_norm_apply (cells : Finset ℤ) (value : lp (fun _ : ℤ => Value) 2) :
    ‖projection Value cells value - value‖ ≤ ‖value‖ := by
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro cell
  change ‖projection Value cells value cell - value cell‖ ≤ ‖value cell‖
  rw [projection_coordinate]
  split_ifs <;> simp

variable {Space : Type*} [MeasurableSpace Space] (measure : Measure Space)

theorem field_projection_norm_le (cells : Finset ℤ) : ‖fieldProjection measure Value cells‖ ≤ 1 :=
  (ContinuousLinearMap.norm_compLpL_le (p := 2) (μ := measure) (projection Value cells)).trans
    (projection_norm_le Value cells)

theorem field_projection_norm_apply (cells : Finset ℤ)
    (field : Lp (lp (fun _ : ℤ => Value) 2) 2 measure) :
    ‖fieldProjection measure Value cells field‖ ≤ ‖field‖ := by
  calc
    _ ≤ ‖fieldProjection measure Value cells‖ * ‖field‖ :=
      (fieldProjection measure Value cells).le_opNorm field
    _ ≤ 1 * ‖field‖ := mul_le_mul_of_nonneg_right (field_projection_norm_le Value measure cells)
      (norm_nonneg field)
    _ = _ := one_mul _

theorem field_projection_coordinate (cells : Finset ℤ)
    (field : Lp (lp (fun _ : ℤ => Value) 2) 2 measure) :
    ∀ᵐ point ∂measure, ∀ cell : ℤ,
      fieldProjection measure Value cells field point cell = if cell ∈ cells then field point cell else 0 := by
  filter_upwards [(projection Value cells).coeFn_compLpL field] with point equality
  intro cell
  change ((projection Value cells).compLpL 2 measure field) point cell = _
  rw [equality]
  exact projection_coordinate Value cells (field point) cell

theorem field_projection_idempotent (cells : Finset ℤ)
    (field : Lp (lp (fun _ : ℤ => Value) 2) 2 measure) :
    fieldProjection measure Value cells (fieldProjection measure Value cells field) =
      fieldProjection measure Value cells field := by
  apply Lp.ext
  filter_upwards [(projection Value cells).coeFn_compLpL (fieldProjection measure Value cells field),
    (projection Value cells).coeFn_compLpL field] with point outer inner
  calc
    _ = projection Value cells (fieldProjection measure Value cells field point) := outer
    _ = projection Value cells (projection Value cells (field point)) :=
      congrArg (projection Value cells) inner
    _ = projection Value cells (field point) := projection_idempotent Value cells (field point)
    _ = _ := inner.symm

theorem field_projection_finite (cells : Finset ℤ)
    (field : Lp (lp (fun _ : ℤ => Value) 2) 2 measure) :
    finiteCellField measure (fieldProjection measure Value cells field) := by
  refine ⟨cells, ?_⟩
  filter_upwards [field_projection_coordinate Value measure cells field] with point coordinates
  intro cell outside
  rw [coordinates, if_neg outside]

end Values

section Hilbert

variable {Space : Type*} [MeasurableSpace Space] (measure : Measure Space)
  (Value : Type*) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]

theorem error_norm_sq (cells : Finset ℤ) (field : Lp (lp (fun _ : ℤ => Value) 2) 2 measure) :
    ‖fieldProjection measure Value cells field - field‖ ^ 2 =
      ∫ point, ‖projection Value cells (field point) - field point‖ ^ 2 ∂measure := by
  let := InnerProductSpace.rclikeToReal ℂ Value
  rw [Grad.SchurKernel.RealEnergy.realLp_norm_sq measure]
  apply integral_congr_ae
  have projection_ae : (fieldProjection measure Value cells field : Space → lp (fun _ : ℤ => Value) 2)
      =ᵐ[measure] fun point => projection Value cells (field point) :=
    (projection Value cells).coeFn_compLpL field
  filter_upwards [Lp.coeFn_sub (fieldProjection measure Value cells field) field, projection_ae]
    with point subtraction projectionLaw
  simp only [Pi.sub_apply] at subtraction
  rw [subtraction, projectionLaw]

theorem error_norm_sq_tendsto (field : Lp (lp (fun _ : ℤ => Value) 2) 2 measure) :
    Tendsto (fun cells : Finset ℤ => ‖fieldProjection measure Value cells field - field‖ ^ 2)
      atTop (𝓝 0) := by
  have integralLimit := tendsto_integral_filter_of_dominated_convergence
    (μ := measure) (l := (atTop : Filter (Finset ℤ)))
    (F := fun cells (point : Space) => ‖projection Value cells (field point) - field point‖ ^ 2)
    (f := fun _ : Space => (0 : ℝ)) (fun point : Space => ‖field point‖ ^ 2)
    (Eventually.of_forall (fun cells =>
      (((projection Value cells).continuous.comp_aestronglyMeasurable
        (Lp.memLp field).aestronglyMeasurable).sub
        (Lp.memLp field).aestronglyMeasurable).norm.pow 2))
    (Eventually.of_forall (fun cells => Eventually.of_forall (fun point => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (complement_norm_apply Value cells (field point)) 2)))
    (Lp.memLp field).norm.integrable_sq
    (Eventually.of_forall (fun point => by
      simpa only [sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
        ((projection_strong Value (field point)).sub
          (tendsto_const_nhds (x := field point))).norm.pow 2))
  simpa only [← error_norm_sq, integral_zero] using integralLimit

theorem field_strong (field : Lp (lp (fun _ : ℤ => Value) 2) 2 measure) :
    Tendsto (fun cells : Finset ℤ => fieldProjection measure Value cells field) atTop (𝓝 field) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have sqrtLimit := Real.continuous_sqrt.continuousAt.tendsto.comp
    (error_norm_sq_tendsto measure Value field)
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using sqrtLimit

theorem projections : ProjectionGoal (Value := Value) measure :=
  ⟨fun cells field => ⟨field_projection_coordinate Value measure cells field,
    field_projection_norm_apply Value measure cells field, field_projection_idempotent Value measure cells field⟩,
    field_projection_norm_le Value measure, field_strong measure Value⟩

theorem finite_cell_dense : DensityGoal (Value := Value) measure := by
  intro field
  apply isClosed_closure.mem_of_tendsto (field_strong measure Value field)
  exact Eventually.of_forall (fun cells => subset_closure (field_projection_finite Value measure cells field))

end Hilbert

theorem rectangular_section_error_bound {ValueIn ValueOut : Type*}
    [NormedAddCommGroup ValueIn] [NormedSpace ℂ ValueIn]
    [NormedAddCommGroup ValueOut] [NormedSpace ℂ ValueOut]
    (inputProjection : ValueIn →L[ℂ] ValueIn) (outputProjection : ValueOut →L[ℂ] ValueOut)
    (operator : ValueIn →L[ℂ] ValueOut)
    (contractive : ∀ value : ValueOut, ‖outputProjection value‖ ≤ ‖value‖) (value : ValueIn) :
    ‖outputProjection (operator (inputProjection value)) - operator value‖ ≤
      ‖operator‖ * ‖inputProjection value - value‖ + ‖outputProjection (operator value) - operator value‖ := by
  have decomposition : outputProjection (operator (inputProjection value)) - operator value =
      outputProjection (operator (inputProjection value - value)) +
        (outputProjection (operator value) - operator value) := by
    rw [map_sub, map_sub, sub_add_sub_cancel]
  calc
    _ = _ := congrArg norm decomposition
    _ ≤ ‖outputProjection (operator (inputProjection value - value))‖ +
        ‖outputProjection (operator value) - operator value‖ := norm_add_le _ _
    _ ≤ _ := add_le_add
      ((contractive (operator (inputProjection value - value))).trans
        (operator.le_opNorm (inputProjection value - value))) le_rfl

theorem rectangular_sections {Space ValueIn ValueOut : Type*} [MeasurableSpace Space]
    [NormedAddCommGroup ValueIn] [InnerProductSpace ℂ ValueIn]
    [NormedAddCommGroup ValueOut] [InnerProductSpace ℂ ValueOut] (measure : Measure Space) :
    RectangularSectionsGoal (ValueIn := ValueIn) (ValueOut := ValueOut) measure := by
  intro operator field
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have inputLimit := tendsto_iff_norm_sub_tendsto_zero.mp (field_strong measure ValueIn field)
  have outputLimit := tendsto_iff_norm_sub_tendsto_zero.mp (field_strong measure ValueOut (operator field))
  apply squeeze_zero (fun _ => norm_nonneg _) (fun cells =>
    rectangular_section_error_bound (fieldProjection measure ValueIn cells)
      (fieldProjection measure ValueOut cells) operator
      (field_projection_norm_apply ValueOut measure cells) field)
  simpa only [mul_zero, zero_add] using (inputLimit.const_mul ‖operator‖).add outputLimit

end Grad.CellProjections.Generic

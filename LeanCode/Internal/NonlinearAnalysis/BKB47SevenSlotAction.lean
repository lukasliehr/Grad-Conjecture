import BKB46ActualCovariantReconstruction

noncomputable section

open scoped BigOperators

universe u


namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision

section CellExchange

variable {Cell : Type u}

private theorem memlp_two_iff_summable_sq {Value : Type*} [NormedAddCommGroup Value]
    (coordinates : Cell → Value) :
    Memℓp coordinates 2 ↔ Summable (fun cell : Cell => ‖coordinates cell‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using
    (memℓp_gen_iff (p := 2) (f := coordinates) (by norm_num))

private theorem lp_summable_sq {Value : Type*} [NormedAddCommGroup Value]
    (cells : lp (fun _ : Cell => Value) 2) :
    Summable (fun cell : Cell => ‖cells cell‖ ^ 2) :=
  (memlp_two_iff_summable_sq cells).mp (lp.memℓp cells)

private theorem lp_norm_sq {Value : Type*} [NormedAddCommGroup Value]
    (cells : lp (fun _ : Cell => Value) 2) :
    ‖cells‖ ^ 2 = ∑' cell : Cell, ‖cells cell‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using
    (lp.norm_rpow_eq_tsum (p := 2) (by norm_num) cells)

private def sevenCollectCoordinates
    (tensor : PiLp 2 (fun _ : Fin 7 => lp (fun _ : Cell => ComplexEuclidean 1) 2)) :
    Cell → ComplexEuclidean 7 :=
  fun cell => WithLp.toLp 2 (fun slot => tensor slot cell 0)

private theorem euclideanOne_norm_sq (value : ComplexEuclidean 1) :
    ‖value‖ ^ 2 = ‖value 0‖ ^ 2 := by
  simpa [Fin.sum_univ_succ] using
    (PiLp.norm_sq_eq_of_L2 (fun _ : Fin 1 => ℂ) value)

private theorem sevenCollect_coordinate_norm_sq
    (tensor : PiLp 2 (fun _ : Fin 7 => lp (fun _ : Cell => ComplexEuclidean 1) 2))
    (cell : Cell) :
    ‖sevenCollectCoordinates tensor cell‖ ^ 2 =
      ∑ slot : Fin 7, ‖tensor slot cell‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro slot _
  exact (euclideanOne_norm_sq (tensor slot cell)).symm

private theorem sevenCollect_square_summable
    (tensor : PiLp 2 (fun _ : Fin 7 => lp (fun _ : Cell => ComplexEuclidean 1) 2)) :
    Summable (fun cell : Cell => ‖sevenCollectCoordinates tensor cell‖ ^ 2) := by
  have summed : Summable (fun cell : Cell => ∑ slot : Fin 7, ‖tensor slot cell‖ ^ 2) :=
    (hasSum_sum (s := Finset.univ)
      (fun slot _ => (lp_summable_sq (tensor slot)).hasSum)).summable
  exact summed.congr (fun cell => (sevenCollect_coordinate_norm_sq tensor cell).symm)

private def sevenCollect
    (tensor : PiLp 2 (fun _ : Fin 7 => lp (fun _ : Cell => ComplexEuclidean 1) 2)) :
    lp (fun _ : Cell => ComplexEuclidean 7) 2 :=
  ⟨sevenCollectCoordinates tensor,
    (memlp_two_iff_summable_sq _).mpr (sevenCollect_square_summable tensor)⟩

private theorem sevenCollect_norm_sq
    (tensor : PiLp 2 (fun _ : Fin 7 => lp (fun _ : Cell => ComplexEuclidean 1) 2)) :
    ‖sevenCollect tensor‖ ^ 2 = ‖tensor‖ ^ 2 := by
  rw [lp_norm_sq, PiLp.norm_sq_eq_of_L2]
  calc
    (∑' cell : Cell, ‖sevenCollect tensor cell‖ ^ 2) =
        ∑' cell : Cell, ∑ slot : Fin 7, ‖tensor slot cell‖ ^ 2 := by
      apply tsum_congr
      intro cell
      exact sevenCollect_coordinate_norm_sq tensor cell
    _ = ∑ slot : Fin 7, ∑' cell : Cell, ‖tensor slot cell‖ ^ 2 := by
      exact Summable.tsum_finsetSum
        (fun slot _ => lp_summable_sq (tensor slot))
    _ = ∑ slot : Fin 7, ‖tensor slot‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro slot _
      exact (lp_norm_sq (tensor slot)).symm

private theorem sevenCollect_norm
    (tensor : PiLp 2 (fun _ : Fin 7 => lp (fun _ : Cell => ComplexEuclidean 1) 2)) :
    ‖sevenCollect tensor‖ = ‖tensor‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (sevenCollect_norm_sq tensor)

private theorem sevenCollect_add
    (first second : PiLp 2
      (fun _ : Fin 7 => lp (fun _ : Cell => ComplexEuclidean 1) 2)) :
    sevenCollect (first + second) = sevenCollect first + sevenCollect second := by
  apply lp.ext
  funext cell
  apply PiLp.ext
  intro slot
  rfl

private theorem sevenCollect_smul (scalar : ℂ)
    (tensor : PiLp 2 (fun _ : Fin 7 => lp (fun _ : Cell => ComplexEuclidean 1) 2)) :
    sevenCollect (scalar • tensor) = scalar • sevenCollect tensor := by
  apply lp.ext
  funext cell
  apply PiLp.ext
  intro slot
  rfl

private def sevenCollectLinear :
    PiLp 2 (fun _ : Fin 7 => lp (fun _ : Cell => ComplexEuclidean 1) 2) →ₗ[ℂ]
      lp (fun _ : Cell => ComplexEuclidean 7) 2 where
  toFun := sevenCollect
  map_add' := sevenCollect_add
  map_smul' := sevenCollect_smul

private def sevenCollectCLM :
    PiLp 2 (fun _ : Fin 7 => lp (fun _ : Cell => ComplexEuclidean 1) 2) →L[ℂ]
      lp (fun _ : Cell => ComplexEuclidean 7) 2 :=
  LinearMap.mkContinuous sevenCollectLinear 1 (fun tensor => by
    change ‖sevenCollect tensor‖ ≤ 1 * ‖tensor‖
    rw [sevenCollect_norm, one_mul])

private theorem sevenCollectCLM_norm
    (tensor : PiLp 2 (fun _ : Fin 7 => lp (fun _ : Cell => ComplexEuclidean 1) 2)) :
    ‖sevenCollectCLM tensor‖ = ‖tensor‖ :=
  sevenCollect_norm tensor

end CellExchange

/-- The canonical isometric flattening of AH20's seven scalar traces into one
seven-vector trace, without reindexing either physical Fourier mode. -/
def sevenSlotFlatten (parameters : PhaseParameters) (angular cell : ℕ) :
    SevenSlotTrace parameters angular cell →L[ℂ]
      NegativeTrace parameters angular cell 7 :=
  sevenCollectCLM

theorem sevenSlotFlatten_apply (parameters : PhaseParameters) (angular cell : ℕ)
    (input : SevenSlotTrace parameters angular cell) (mode : ℤ × ℤ)
    (slot : Fin 7) :
    sevenSlotFlatten parameters angular cell input mode slot = input slot mode 0 := rfl

theorem sevenSlotFlatten_norm (parameters : PhaseParameters) (angular cell : ℕ)
    (input : SevenSlotTrace parameters angular cell) :
    ‖sevenSlotFlatten parameters angular cell input‖ = ‖input‖ :=
  sevenCollectCLM_norm input

theorem sevenSlotFlatten_coefficient (parameters : PhaseParameters) (angular cell : ℕ)
    (input : SevenSlotTrace parameters angular cell) (mode : ℤ × ℤ)
    (slot : Fin 7) :
    negativeTraceCoefficient parameters angular cell
        (sevenSlotFlatten parameters angular cell input) mode slot =
      negativeTraceCoefficient parameters angular cell (input slot) mode 0 := rfl

/-- The exact AH18 action of a full `7 -> d` kernel on AH20's dependent
seven-slot Hilbert trace. -/
def fullSevenSlotKernelAction {targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FullTwoFrequencyKernel parameters 7 targetDimension) :
    SevenSlotTrace parameters angular cell →L[ℂ]
      NegativeTrace parameters angular cell targetDimension :=
  (fullNegativeKernelAction parameters angular cell kernel).comp
    (sevenSlotFlatten parameters angular cell)

theorem fullSevenSlotKernelAction_bound {targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FullTwoFrequencyKernel parameters 7 targetDimension)
    (input : SevenSlotTrace parameters angular cell) :
    ‖fullSevenSlotKernelAction parameters angular cell kernel input‖ ≤
      fullKernelMoment parameters (angular + cell + 1) kernel * ‖input‖ := by
  exact (fullNegativeKernelAction_bound parameters angular cell kernel
    (sevenSlotFlatten parameters angular cell input)).trans_eq
      (by rw [sevenSlotFlatten_norm])

end Grad.BoundaryKernelAction

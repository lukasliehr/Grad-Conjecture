import TCX1Interface

noncomputable section

universe indexUniverse valueUniverse

namespace Grad.TensorCellExchange

variable {Index : Type indexUniverse} [Fintype Index]
variable {Value : Type valueUniverse} [NormedAddCommGroup Value]

theorem memlp_iff_summable_sq (coordinates : ℤ → Value) :
    Memℓp coordinates 2 ↔ Summable (fun cell : ℤ => ‖coordinates cell‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using
    (memℓp_gen_iff (p := 2) (f := coordinates) (by norm_num))

theorem lp_summable_sq (cells : lp (fun _ : ℤ => Value) 2) :
    Summable (fun cell : ℤ => ‖cells cell‖ ^ 2) :=
  (memlp_iff_summable_sq cells).mp (lp.memℓp cells)

theorem lp_norm_sq (cells : lp (fun _ : ℤ => Value) 2) :
    ‖cells‖ ^ 2 = ∑' cell : ℤ, ‖cells cell‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using
    (lp.norm_rpow_eq_tsum (p := 2) (by norm_num) cells)

theorem collect_square_summable
    (tensor : PiLp 2 (fun _ : Index => lp (fun _ : ℤ => Value) 2)) :
    Summable (fun cell : ℤ => ‖collectCoordinates Index Value tensor cell‖ ^ 2) := by
  have summed : Summable (fun cell : ℤ => ∑ index : Index, ‖tensor index cell‖ ^ 2) :=
    (hasSum_sum (s := Finset.univ)
      (fun index _ => (lp_summable_sq (tensor index)).hasSum)).summable
  apply summed.congr
  intro cell
  exact (PiLp.norm_sq_eq_of_L2 (fun _ : Index => Value)
    (collectCoordinates Index Value tensor cell)).symm

theorem collect_memlp
    (tensor : PiLp 2 (fun _ : Index => lp (fun _ : ℤ => Value) 2)) :
    Memℓp (collectCoordinates Index Value tensor) 2 :=
  (memlp_iff_summable_sq _).mpr (collect_square_summable tensor)

theorem separate_memlp
    (cells : lp (fun _ : ℤ => PiLp 2 (fun _ : Index => Value)) 2) (index : Index) :
    Memℓp (separateCoordinates Index Value cells index) 2 :=
  (lp.memℓp cells).mono' (fun cell => PiLp.norm_apply_le (cells cell) index)

theorem separate_square_summable
    (cells : lp (fun _ : ℤ => PiLp 2 (fun _ : Index => Value)) 2) (index : Index) :
    Summable (fun cell : ℤ => ‖cells cell index‖ ^ 2) :=
  (memlp_iff_summable_sq _).mp (separate_memlp cells index)

theorem source_norm_sq
    (tensor : PiLp 2 (fun _ : Index => lp (fun _ : ℤ => Value) 2)) :
    ‖tensor‖ ^ 2 = ∑ index : Index, ∑' cell : ℤ, ‖tensor index cell‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_congr rfl (fun index _ => lp_norm_sq (tensor index))

theorem target_norm_sq
    (cells : lp (fun _ : ℤ => PiLp 2 (fun _ : Index => Value)) 2) :
    ‖cells‖ ^ 2 = ∑ index : Index, ∑' cell : ℤ, ‖cells cell index‖ ^ 2 := by
  rw [lp_norm_sq]
  calc
    (∑' cell : ℤ, ‖cells cell‖ ^ 2) =
        ∑' cell : ℤ, ∑ index : Index, ‖cells cell index‖ ^ 2 :=
      tsum_congr (fun cell => PiLp.norm_sq_eq_of_L2 (fun _ : Index => Value) (cells cell))
    _ = ∑ index : Index, ∑' cell : ℤ, ‖cells cell index‖ ^ 2 :=
      Summable.tsum_finsetSum (fun index _ => separate_square_summable cells index)

variable (Index Value) in
def collect (tensor : PiLp 2 (fun _ : Index => lp (fun _ : ℤ => Value) 2)) :
    lp (fun _ : ℤ => PiLp 2 (fun _ : Index => Value)) 2 :=
  ⟨collectCoordinates Index Value tensor, collect_memlp tensor⟩

variable (Index Value) in
def separate (cells : lp (fun _ : ℤ => PiLp 2 (fun _ : Index => Value)) 2) :
    PiLp 2 (fun _ : Index => lp (fun _ : ℤ => Value) 2) :=
  WithLp.toLp 2 (fun index =>
    ⟨separateCoordinates Index Value cells index, separate_memlp cells index⟩)

theorem collect_apply
    (tensor : PiLp 2 (fun _ : Index => lp (fun _ : ℤ => Value) 2)) (cell : ℤ) (index : Index) :
    collect Index Value tensor cell index = tensor index cell := rfl

theorem separate_apply
    (cells : lp (fun _ : ℤ => PiLp 2 (fun _ : Index => Value)) 2) (index : Index) (cell : ℤ) :
    separate Index Value cells index cell = cells cell index := rfl

theorem separate_collect
    (tensor : PiLp 2 (fun _ : Index => lp (fun _ : ℤ => Value) 2)) :
    separate Index Value (collect Index Value tensor) = tensor := by
  apply PiLp.ext
  intro index
  apply lp.ext
  funext cell
  rfl

theorem collect_separate (cells : lp (fun _ : ℤ => PiLp 2 (fun _ : Index => Value)) 2) :
    collect Index Value (separate Index Value cells) = cells := by
  apply lp.ext
  funext cell
  apply PiLp.ext
  intro index
  rfl

theorem collect_norm_sq
    (tensor : PiLp 2 (fun _ : Index => lp (fun _ : ℤ => Value) 2)) :
    ‖collect Index Value tensor‖ ^ 2 = ‖tensor‖ ^ 2 :=
  (target_norm_sq (collect Index Value tensor)).trans (source_norm_sq tensor).symm

theorem collect_norm
    (tensor : PiLp 2 (fun _ : Index => lp (fun _ : ℤ => Value) 2)) :
    ‖collect Index Value tensor‖ = ‖tensor‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (collect_norm_sq tensor)

theorem collect_add
    (first second : PiLp 2 (fun _ : Index => lp (fun _ : ℤ => Value) 2)) :
    collect Index Value (first + second) = collect Index Value first + collect Index Value second := by
  apply lp.ext
  funext cell
  apply PiLp.ext
  intro index
  rfl

theorem squareSum : SquareSumGoal Index Value := ⟨source_norm_sq, target_norm_sq⟩

variable [NormedSpace ℂ Value]

theorem collect_smul (scalar : ℂ)
    (tensor : PiLp 2 (fun _ : Index => lp (fun _ : ℤ => Value) 2)) :
    collect Index Value (scalar • tensor) = scalar • collect Index Value tensor := by
  apply lp.ext
  funext cell
  apply PiLp.ext
  intro index
  rfl

variable (Index Value) in
def exchange : PiLp 2 (fun _ : Index => lp (fun _ : ℤ => Value) 2) ≃ₗᵢ[ℂ]
    lp (fun _ : ℤ => PiLp 2 (fun _ : Index => Value)) 2 where
  toFun := collect Index Value
  invFun := separate Index Value
  left_inv := separate_collect
  right_inv := collect_separate
  map_add' := collect_add
  map_smul' := collect_smul
  norm_map' := collect_norm

theorem exchange_apply
    (tensor : PiLp 2 (fun _ : Index => lp (fun _ : ℤ => Value) 2)) (cell : ℤ) (index : Index) :
    exchange Index Value tensor cell index = tensor index cell := rfl

theorem exchange_symm_apply
    (cells : lp (fun _ : ℤ => PiLp 2 (fun _ : Index => Value)) 2) (index : Index) (cell : ℤ) :
    (exchange Index Value).symm cells index cell = cells cell index := rfl

theorem exchange_symm_exchange
    (tensor : PiLp 2 (fun _ : Index => lp (fun _ : ℤ => Value) 2)) :
    (exchange Index Value).symm (exchange Index Value tensor) = tensor :=
  (exchange Index Value).symm_apply_apply tensor

theorem exchange_exchange_symm
    (cells : lp (fun _ : ℤ => PiLp 2 (fun _ : Index => Value)) 2) :
    exchange Index Value ((exchange Index Value).symm cells) = cells :=
  (exchange Index Value).apply_symm_apply cells

theorem exchange_norm
    (tensor : PiLp 2 (fun _ : Index => lp (fun _ : ℤ => Value) 2)) :
    ‖exchange Index Value tensor‖ = ‖tensor‖ :=
  (exchange Index Value).norm_map tensor

theorem constructor : ExchangeGoal Index Value :=
  ⟨exchange Index Value, exchange_apply, exchange_symm_apply, exchange_norm⟩

theorem block : BlockGoal Index Value := ⟨squareSum, constructor⟩

def orderedExchange (rank : ℕ) : Grad.TensorLpExchange.OrderedCellValues rank ≃ₗᵢ[ℂ]
    lp (fun _ : ℤ => PiLp 2 (fun _ : Fin rank → Fin 2 => EuclideanSpace ℂ (Fin 3))) 2 :=
  exchange (Fin rank → Fin 2) (EuclideanSpace ℂ (Fin 3))

theorem orderedExchange_apply (rank : ℕ) (tensor : Grad.TensorLpExchange.OrderedCellValues rank)
    (cell : ℤ) (word : Fin rank → Fin 2) :
    orderedExchange rank tensor cell word = tensor word cell := rfl

theorem orderedExchange_symm_apply (rank : ℕ)
    (cells : lp (fun _ : ℤ => PiLp 2 (fun _ : Fin rank → Fin 2 => EuclideanSpace ℂ (Fin 3))) 2)
    (word : Fin rank → Fin 2) (cell : ℤ) :
    (orderedExchange rank).symm cells word cell = cells cell word := rfl

end Grad.TensorCellExchange

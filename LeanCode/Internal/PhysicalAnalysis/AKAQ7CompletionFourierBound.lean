import AKAQ5ExactRetractionCell

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open scoped BigOperators ENNReal Topology
open Filter
namespace Grad.OriginalFlatAxisDecay
open Grad.FourierGrade Grad.CartesianState Grad.ClosedJets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem continuous_fibre_hasSum (cell : ℤ) (symbol : SpatialMode → ℂ)
    (functional : JGrade E 4 →L[ℂ] E)
    (single : ∀ (mode : SpatialMode) (source : ℤ) (value : E),
      functional (coefficientSingle 4 (fibreMode (source,mode)) value) =
        if source = cell then symbol mode • value else 0)
    (field : JGrade E 4) :
    HasSum (fun mode : SpatialMode => symbol mode • coefficient 4 field (fibreMode (cell,mode)))
      (functional field) := by
  classical
  have raw : HasSum (fun mode : FourierMode => coefficientSingle 4 mode (coefficient 4 field mode)) field := by
    convert lp.hasSum_single (p := 2) (by norm_num) field using 1
    funext mode
    exact coefficientSingle_eq_weightedSingle 4 field mode
  have mapped := raw.map functional functional.continuous
  have injective : Function.Injective (fun mode : SpatialMode => fibreMode (cell,mode)) := by
    intro first second same
    exact (Prod.mk.inj (fibreMode_injective same)).2
  have vanished (mode : FourierMode) (outside : mode ∉ Set.range (fun spatial : SpatialMode => fibreMode (cell,spatial))) :
      functional (coefficientSingle 4 mode (coefficient 4 field mode)) = 0 := by
    have different : mode.2.2 ≠ cell := by
      intro same
      apply outside
      refine ⟨(mode.1,mode.2.1),?_⟩
      change (mode.1,mode.2.1,cell) = mode
      rw [← same]
    have same : fibreMode (mode.2.2,(mode.1,mode.2.1)) = mode := rfl
    simpa only [same,if_neg different] using single (mode.1,mode.2.1) mode.2.2 (coefficient 4 field mode)
  have restricted := (injective.hasSum_iff (f := fun mode : FourierMode =>
    functional (coefficientSingle 4 mode (coefficient 4 field mode))) vanished).mpr mapped
  convert restricted using 1
  funext mode
  simpa only [Function.comp_apply,ite_true] using (single mode cell (coefficient 4 field (fibreMode (cell,mode)))).symm

theorem completedFourier_symbol_bound (symbol : SpatialMode → ℂ) (payment : ℝ) (nonnegative : 0 ≤ payment)
    (bound : ∀ mode, ‖symbol mode‖^2 ≤ payment * Real.sqrt (spatialSquare mode)^3)
    (field : JGrade E 4) (values : ℤ → E)
    (series : ∀ cell, HasSum (fun mode : SpatialMode => symbol mode • coefficient 4 field (fibreMode (cell,mode))) (values cell))
    (cells : Finset ℤ) :
    ∑ cell ∈ cells, cellFrequency cell^2 * ‖values cell‖^2 ≤
      payment * spatialDecayConstant * ‖field‖^2 := by
  have convergence : Tendsto (fun support : Finset SpatialMode =>
      ∑ cell ∈ cells, cellFrequency cell^2 *
        ‖∑ mode ∈ support, symbol mode • coefficient 4 field (fibreMode (cell,mode))‖^2)
      (SummationFilter.unconditional SpatialMode).filter (𝓝 (∑ cell ∈ cells, cellFrequency cell^2 * ‖values cell‖^2)) := by
    classical
    induction cells using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (tendsto_const_nhds (x := (0:ℝ)))
    | @insert cell cells outside induction =>
      simpa only [Finset.sum_insert outside] using
        ((tendsto_const_nhds.mul ((series cell).norm.pow 2)).add induction)
  exact le_of_tendsto convergence (Eventually.of_forall fun support =>
    finiteFourier_symbol_bound symbol payment nonnegative bound field cells support)

theorem completedFourier_symbol_memlp (symbol : SpatialMode → ℂ) (payment : ℝ) (nonnegative : 0 ≤ payment)
    (bound : ∀ mode, ‖symbol mode‖^2 ≤ payment * Real.sqrt (spatialSquare mode)^3)
    (field : JGrade E 4) (values : ℤ → E)
    (series : ∀ cell, HasSum (fun mode : SpatialMode => symbol mode • coefficient 4 field (fibreMode (cell,mode))) (values cell)) :
    Memℓp (fun cell => (cellFrequency cell : ℂ) • values cell) 2 := by
  apply (memℓp_gen_iff (p := 2) (by norm_num)).mpr
  have summable := summable_of_sum_le (f := fun cell => cellFrequency cell^2 * ‖values cell‖^2)
    (fun cell => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (completedFourier_symbol_bound symbol payment nonnegative bound field values series)
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (cellFrequency_pos _),mul_pow] using summable

end Grad.OriginalFlatAxisDecay

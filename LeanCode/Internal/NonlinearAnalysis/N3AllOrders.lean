import MajorantExpActual
import Mathlib.Analysis.Analytic.IteratedFDeriv

/-!
# NG_F06 / N3: all-orders actual Fréchet derivative identification

The accepted `compositionWordMultilinear` is a continuous `p`-linear map.
Mathlib's arbitrary-order derivative formula for a multilinear map is indexed
by embeddings `Fin order ↪ Fin p`, exactly the placement indexing already used
by `exponentialDerivativeTerm`.  This file identifies those terms without
changing either accepted definition.
-/

noncomputable section

open scoped BigOperators ContDiff Classical

namespace Grad.CoefficientMajorants

open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity Grad.GaugeCoefficients.Physical.Frame
open Grad.Constraints.Seed

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000

/-- Replace the slots hit by an embedding with independent directions, and
leave all other slots at the base point.  This generic placement function is
shared by the coefficient word and by fixed-grade commutative powers. -/
def multilinearPlacedFactor {E : Type*} {order p : ℕ}
    (placement : Fin order ↪ Fin p) (base : E) (directions : Fin order → E)
    (slot : Fin p) : E :=
  if hit : ∃ index, placement index = slot then directions (Classical.choose hit) else base

/-- The arbitrary Fréchet derivative of a continuous multilinear map composed
with the diagonal is the sum over injective placements of derivative
directions.  This statement is independent of the coefficient carrier. -/
theorem ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal_all_orders
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {p : ℕ} (f : E [×p]→L[𝕜] F) (order : ℕ) (base : E)
    (directions : Fin order → E) :
    (iteratedFDeriv 𝕜 order (fun x => f (fun _ => x)) base) directions =
      ∑ placement : Fin order ↪ Fin p,
        f (multilinearPlacedFactor placement base directions) := by
  classical
  let diagonal : E →L[𝕜] (Fin p → E) :=
    ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id 𝕜 E)
  change (iteratedFDeriv 𝕜 order (f ∘ diagonal) base) directions = _
  rw [diagonal.iteratedFDeriv_comp_right f.contDiff base
    (show (order : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)]
  rw [f.iteratedFDeriv_eq]
  simp only [ContinuousMultilinearMap.iteratedFDeriv,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, _root_.sum_apply,
    ContinuousMultilinearMap.iteratedFDerivComponent_apply, Pi.compRightL_apply]
  apply Finset.sum_congr rfl
  intro placement _
  congr 1
  funext slot
  unfold multilinearPlacedFactor
  by_cases hit : ∃ index, placement index = slot
  · rw [dif_pos hit]
    simp only [Set.mem_range, hit, ↓reduceDIte, diagonal,
      ContinuousLinearMap.pi_apply, ContinuousLinearMap.id_apply]
    congr 1
    apply placement.injective
    let rangeEquiv := @Function.Embedding.toEquivRange
      (Fin order) (Fin p) (Fin.fintype order) (Classical.decEq _) placement
    change placement (rangeEquiv.symm ⟨slot, _⟩) = placement (Classical.choose hit)
    have inverseImage : placement (rangeEquiv.symm ⟨slot, hit⟩) = slot :=
      congrArg Subtype.val (rangeEquiv.apply_symm_apply ⟨slot, hit⟩)
    exact inverseImage.trans (Classical.choose_spec hit).symm
  · rw [dif_neg hit]
    simp only [Set.mem_range, hit, ↓reduceDIte, diagonal,
      ContinuousLinearMap.pi_apply, ContinuousLinearMap.id_apply]

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
  {grade dimension : ℕ}

abbrev N3Coefficient :=
  Coefficient L sigma gamma ell grade dimension dimension

local instance n3ComplexSpace : NormedSpace ℂ
    (N3Coefficient (L := L) (sigma := sigma) (gamma := gamma) (ell := ell)
      (grade := grade) (dimension := dimension)) := inferInstance

local instance n3RealSpace : NormedSpace ℝ
    (N3Coefficient (L := L) (sigma := sigma) (gamma := gamma) (ell := ell)
      (grade := grade) (dimension := dimension)) := inferInstance

local instance n3ScalarTower : IsScalarTower ℝ ℂ
    (N3Coefficient (L := L) (sigma := sigma) (gamma := gamma) (ell := ell)
      (grade := grade) (dimension := dimension)) := inferInstance

/-- The arbitrary complex Fréchet derivative of the diagonal coefficient word
is exactly the existing sum over ordered placements. -/
theorem iteratedFDeriv_compositionWord_diagonal_apply (order p : ℕ)
    (base : N3Coefficient (L := L) (sigma := sigma) (gamma := gamma) (ell := ell)
      (grade := grade) (dimension := dimension))
    (directions : Fin order → N3Coefficient (L := L) (sigma := sigma)
      (gamma := gamma) (ell := ell) (grade := grade) (dimension := dimension)) :
    (iteratedFDeriv ℂ order
        (fun x => compositionWordMultilinear admissible
          (grade := grade) (dimension := dimension) p (fun _ => x)) base) directions =
      ∑ placement : Fin order ↪ Fin p,
        compositionWord admissible p (placedFactor placement base directions) := by
  rw [ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal_all_orders]
  apply Finset.sum_congr rfl
  intro placement _
  rw [compositionWordMultilinear_apply]
  congr 1

/-- All independent complex derivative orders of the accepted exponential
coefficient are the pre-existing placement expression. -/
theorem iteratedFDeriv_seedExponentialTerm_complex_eq (order p : ℕ)
    (base : N3Coefficient (L := L) (sigma := sigma) (gamma := gamma) (ell := ell)
      (grade := grade) (dimension := dimension))
    (directions : Fin order → N3Coefficient (L := L) (sigma := sigma)
      (gamma := gamma) (ell := ell) (grade := grade) (dimension := dimension)) :
    (iteratedFDeriv ℂ order (fun x => seedExponentialTerm admissible x p) base) directions =
      exponentialDerivativeTerm admissible order p base directions := by
  simp_rw [seedExponentialTerm_eq_multilinear_diagonal admissible p]
  have diagonalSmooth : ContDiffAt ℂ order
      (fun x : N3Coefficient (L := L) (sigma := sigma) (gamma := gamma) (ell := ell)
          (grade := grade) (dimension := dimension) =>
        compositionWordMultilinear admissible (grade := grade) (dimension := dimension) p
          (fun _ => x)) base :=
    ((compositionWordMultilinear admissible (grade := grade) (dimension := dimension) p).contDiff.comp
      ((contDiff_pi).2 fun _ => contDiff_id)).contDiffAt
  rw [iteratedFDeriv_const_smul_apply' diagonalSmooth, smul_apply]
  rw [iteratedFDeriv_compositionWord_diagonal_apply admissible order p base directions]
  rfl

/-- Literal all-orders real Fréchet derivative identity required by NG_F04.
It includes the vanishing case `order > p`, since then the embedding type in
`exponentialDerivativeTerm` is empty. -/
theorem iteratedFDeriv_seedExponentialTerm_eq (order p : ℕ)
    (base : N3Coefficient (L := L) (sigma := sigma) (gamma := gamma) (ell := ell)
      (grade := grade) (dimension := dimension))
    (directions : Fin order → N3Coefficient (L := L) (sigma := sigma)
      (gamma := gamma) (ell := ell) (grade := grade) (dimension := dimension)) :
    (iteratedFDeriv ℝ order (fun x => seedExponentialTerm admissible x p) base) directions =
      exponentialDerivativeTerm admissible order p base directions := by
  have restricted :
      iteratedFDeriv ℝ order (fun x => seedExponentialTerm admissible x p) base =
        (iteratedFDeriv ℂ order
          (fun x => seedExponentialTerm admissible x p) base).restrictScalars ℝ := by
    symm
    simpa only [Function.comp_apply] using
      ((seedExponentialTerm_contDiff admissible p).contDiffAt.of_le
        (show (order : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).restrictScalars_iteratedFDeriv
          (𝕜 := ℝ)
  rw [restricted]
  exact iteratedFDeriv_seedExponentialTerm_complex_eq admissible order p base directions

end Grad.CoefficientMajorants

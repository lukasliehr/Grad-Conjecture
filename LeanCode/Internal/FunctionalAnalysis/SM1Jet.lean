import SM1Weak

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue CellValues FieldL2)
open scoped BigOperators ContDiff

namespace Grad.WeightedJets.SpatialMultiplier

theorem tupleMultiplier_mem_graph (dimension order : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (symbol : Symbol order domain) (exponent : JetIndex order → ℕ)
    (compatible : ExponentAntitone exponent) (jet : WJet dimension order domain exponent) :
    tupleMultiplier dimension order domain openDomain symbol exponent jet.val ∈
      jetGraph dimension order domain exponent := by
  apply (jetGraph_mem dimension order domain exponent _).mpr
  intro upper cell vector test
  have recovery := congrArg (testPairing dimension domain cell vector test)
    (tupleMultiplier_recovery dimension order domain openDomain symbol exponent compatible upper jet)
  rw [Inclusions.testPairing_inverse, unweightedCoordinate_weak] at recovery
  have sameBase : ambientBase dimension order domain exponent jet.val =
      base dimension order domain exponent jet := rfl
  rw [tupleMultiplier_base, sameBase]
  calc
    _ = Grad.CellWeights.positiveFactor (exponent upper) cell *
        (Grad.CellWeights.inverseFactor (exponent upper) cell *
          testPairing dimension domain cell vector test
            (tupleMultiplier dimension order domain openDomain symbol exponent jet.val upper)) := by
      rw [← mul_assoc, mul_comm (Grad.CellWeights.positiveFactor _ _),
        Realization.inverse_positiveFactor, one_mul]
    _ = _ := by
      rw [recovery]
      ring

theorem graph_consumer : GraphGoal := by
  intro dimension order domain openDomain symbol exponent compatible jet
  exact ⟨tupleMultiplier_mem_graph dimension order domain openDomain symbol exponent compatible jet,
    fun upper => tupleMultiplier_recovery dimension order domain openDomain symbol exponent compatible upper jet⟩

def jetMultiplier (dimension order : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (symbol : Symbol order domain) (exponent : JetIndex order → ℕ)
    (compatible : ExponentAntitone exponent) :
    WJet dimension order domain exponent →L[ℂ] WJet dimension order domain exponent :=
  ((tupleMultiplier dimension order domain openDomain symbol exponent).comp
    (jetGraph dimension order domain exponent).subtypeL).codRestrict
    (jetGraph dimension order domain exponent)
    (tupleMultiplier_mem_graph dimension order domain openDomain symbol exponent compatible)

theorem jetMultiplier_tuple (dimension order : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (symbol : Symbol order domain) (exponent : JetIndex order → ℕ)
    (compatible : ExponentAntitone exponent) (jet : WJet dimension order domain exponent) :
    (jetMultiplier dimension order domain openDomain symbol exponent compatible jet).val =
      tupleMultiplier dimension order domain openDomain symbol exponent jet.val := rfl

theorem jetMultiplier_coordinates (dimension order : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (symbol : Symbol order domain) (exponent : JetIndex order → ℕ)
    (compatible : ExponentAntitone exponent) (jet : WJet dimension order domain exponent)
    (upper : JetIndex order) :
    (jetMultiplier dimension order domain openDomain symbol exponent compatible jet).val upper =
      ∑ lower ∈ below upper, (binomial upper lower : ℂ) •
        fieldMultiplier dimension domain openDomain (derivativeScalar symbol (difference upper lower))
          (Grad.CellWeights.inverseFieldCLM dimension domain (exponent lower - exponent upper)
            (jet.val lower)) :=
  coordinateMultiplier_apply dimension order domain openDomain symbol exponent upper jet.val

theorem jetMultiplier_subtype (dimension order : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (symbol : Symbol order domain) (exponent : JetIndex order → ℕ)
    (compatible : ExponentAntitone exponent) :
    (jetGraph dimension order domain exponent).subtypeL.comp
        (jetMultiplier dimension order domain openDomain symbol exponent compatible) =
      (tupleMultiplier dimension order domain openDomain symbol exponent).comp
        (jetGraph dimension order domain exponent).subtypeL := rfl

theorem jetMultiplier_norm_le (dimension order : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (symbol : Symbol order domain) (exponent : JetIndex order → ℕ)
    (compatible : ExponentAntitone exponent) :
    ‖jetMultiplier dimension order domain openDomain symbol exponent compatible‖ ≤ matrixBound symbol := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro jet
  exact tupleMultiplier_apply_norm_le dimension order domain openDomain symbol exponent jet.val

theorem jetMultiplier_base_apply (dimension order : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (symbol : Symbol order domain) (exponent : JetIndex order → ℕ)
    (compatible : ExponentAntitone exponent) (jet : WJet dimension order domain exponent) :
    base dimension order domain exponent (jetMultiplier dimension order domain openDomain symbol exponent compatible jet) =
      fieldMultiplier dimension domain openDomain (derivativeScalar symbol (zeroIndex order))
        (base dimension order domain exponent jet) :=
  tupleMultiplier_base dimension order domain openDomain symbol exponent jet.val

theorem jetMultiplier_base (dimension order : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (symbol : Symbol order domain) (exponent : JetIndex order → ℕ)
    (compatible : ExponentAntitone exponent) :
    (base dimension order domain exponent).comp (jetMultiplier dimension order domain openDomain symbol exponent compatible) =
      (fieldMultiplier dimension domain openDomain (derivativeScalar symbol (zeroIndex order))).comp
        (base dimension order domain exponent) :=
  ContinuousLinearMap.ext (jetMultiplier_base_apply dimension order domain openDomain symbol exponent compatible)

theorem jetMultiplier_norm_sq (dimension order : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (symbol : Symbol order domain) (exponent : JetIndex order → ℕ)
    (compatible : ExponentAntitone exponent) (jet : WJet dimension order domain exponent) :
    ‖jetMultiplier dimension order domain openDomain symbol exponent compatible jet‖ ^ 2 =
      ∑ upper, ‖coordinateMultiplier dimension order domain openDomain symbol exponent upper jet.val‖ ^ 2 :=
  tupleMultiplier_norm_sq dimension order domain openDomain symbol exponent jet.val

theorem jetMultiplier_recovery (dimension order : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (symbol : Symbol order domain) (exponent : JetIndex order → ℕ)
    (compatible : ExponentAntitone exponent) (jet : WJet dimension order domain exponent)
    (upper : JetIndex order) :
    Realization.recoveredDerivative dimension order domain exponent upper
        (jetMultiplier dimension order domain openDomain symbol exponent compatible jet) =
      unweightedCoordinate dimension order domain openDomain symbol exponent upper jet :=
  tupleMultiplier_recovery dimension order domain openDomain symbol exponent compatible upper jet

theorem jetMultiplier_weak (dimension order : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (symbol : Symbol order domain) (exponent : JetIndex order → ℕ)
    (compatible : ExponentAntitone exponent) (jet : WJet dimension order domain exponent)
    (upper : JetIndex order) (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction domain) :
    testPairing dimension domain cell vector test
        (Realization.recoveredDerivative dimension order domain exponent upper
          (jetMultiplier dimension order domain openDomain symbol exponent compatible jet)) =
      (-1 : ℂ) ^ degree upper * derivativeTestPairing dimension order domain upper cell vector test
        (fieldMultiplier dimension domain openDomain (derivativeScalar symbol (zeroIndex order))
          (base dimension order domain exponent jet)) := by
  rw [jetMultiplier_recovery]
  exact unweightedCoordinate_weak dimension order domain openDomain symbol exponent upper jet cell vector test

theorem jetMultiplier_ae (dimension order : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (symbol : Symbol order domain) (exponent : JetIndex order → ℕ)
    (compatible : ExponentAntitone exponent) (jet : WJet dimension order domain exponent) :
    ∀ᵐ point ∂volume.restrict domain, ∀ (upper : JetIndex order) (cell : ℤ),
      (jetMultiplier dimension order domain openDomain symbol exponent compatible jet).val upper point cell =
        ∑ lower ∈ below upper, ((binomial upper lower : ℂ) *
          (scalarDerivative (difference upper lower).val symbol.toFun point : ℂ) *
          Grad.CellWeights.inverseFactor (exponent lower - exponent upper) cell) •
          jet.val lower point cell := by
  classical
  apply ae_all_iff.mpr
  intro upper
  let family (lower : JetIndex order) : FieldL2 dimension domain :=
    (binomial upper lower : ℂ) •
      fieldMultiplier dimension domain openDomain (derivativeScalar symbol (difference upper lower))
        (Grad.CellWeights.inverseFieldCLM dimension domain (exponent lower - exponent upper) (jet.val lower))
  have terms (lower : JetIndex order) :
      ∀ᵐ point ∂volume.restrict domain, ∀ cell : ℤ,
        family lower point cell = ((binomial upper lower : ℂ) *
          (scalarDerivative (difference upper lower).val symbol.toFun point : ℂ) *
          Grad.CellWeights.inverseFactor (exponent lower - exponent upper) cell) • jet.val lower point cell := by
    filter_upwards [Lp.coeFn_smul (binomial upper lower : ℂ)
      (fieldMultiplier dimension domain openDomain (derivativeScalar symbol (difference upper lower))
        (Grad.CellWeights.inverseFieldCLM dimension domain (exponent lower - exponent upper) (jet.val lower))),
      fieldMultiplier_ae dimension domain openDomain (derivativeScalar symbol (difference upper lower))
        (Grad.CellWeights.inverseFieldCLM dimension domain (exponent lower - exponent upper) (jet.val lower)),
      Grad.CellWeights.inverseFieldCLM_coordinate dimension domain (exponent lower - exponent upper) (jet.val lower)]
      with point scaled multiplied weighted
    intro cell
    change ((binomial upper lower : ℂ) •
      fieldMultiplier dimension domain openDomain (derivativeScalar symbol (difference upper lower))
        (Grad.CellWeights.inverseFieldCLM dimension domain (exponent lower - exponent upper) (jet.val lower))) point cell = _
    rw [scaled]
    change (binomial upper lower : ℂ) •
      (fieldMultiplier dimension domain openDomain (derivativeScalar symbol (difference upper lower))
        (Grad.CellWeights.inverseFieldCLM dimension domain (exponent lower - exponent upper) (jet.val lower)) point cell) = _
    rw [multiplied cell, weighted cell]
    simp only [smul_smul, derivativeScalar, mul_assoc]
  filter_upwards [Lp.coeFn_fun_finsetSum (below upper) family, ae_all_iff.mpr terms]
    with point summed literal
  intro cell
  rw [jetMultiplier_coordinates]
  change (∑ lower ∈ below upper, family lower) point cell = _
  rw [summed]
  simp only [lp.coeFn_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun lower _ => literal lower cell)

theorem jetMultiplier_laws (dimension order : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (symbol : Symbol order domain) (exponent : JetIndex order → ℕ)
    (compatible : ExponentAntitone exponent) :
    JetMultiplierLaws dimension order domain openDomain symbol exponent
      (jetMultiplier dimension order domain openDomain symbol exponent compatible) :=
  ⟨jetMultiplier_subtype dimension order domain openDomain symbol exponent compatible,
    jetMultiplier_norm_le dimension order domain openDomain symbol exponent compatible,
    jetMultiplier_base dimension order domain openDomain symbol exponent compatible,
    jetMultiplier_norm_sq dimension order domain openDomain symbol exponent compatible,
    fun jet upper => ⟨jetMultiplier_recovery dimension order domain openDomain symbol exponent compatible jet upper,
      jetMultiplier_weak dimension order domain openDomain symbol exponent compatible jet upper⟩,
    jetMultiplier_ae dimension order domain openDomain symbol exponent compatible⟩

theorem jet_consumer : JetGoal := by
  intro dimension order domain openDomain symbol exponent compatible
  exact ⟨jetMultiplier dimension order domain openDomain symbol exponent compatible,
    jetMultiplier_laws dimension order domain openDomain symbol exponent compatible⟩

end Grad.WeightedJets.SpatialMultiplier

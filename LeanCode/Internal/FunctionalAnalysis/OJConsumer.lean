import OJNorms

noncomputable section

namespace Grad.WeightedJets.Ordered

theorem index_consumer : IndexGoal := by
  intro rank order bound word
  exact ⟨wordIndex_pair bound word, wordIndex_degree bound word, jetCanonicalWord_eq bound word,
    word_sameCounts bound word⟩

theorem assembly_consumer : AssemblyGoal := by
  intro dimension order rank domain exponent bound jet
  exact ⟨orderedDerivative_apply dimension order rank domain exponent bound jet,
    orderedDerivative_norm_sq dimension order rank domain exponent bound jet,
    orderedDerivative_eq_orderedTensor dimension order rank domain exponent bound jet,
    canonicalFamily_identification dimension order rank domain exponent bound jet⟩

theorem weak_consumer : WeakGoal := by
  intro dimension order rank domain exponent bound jet
  exact ⟨orderedDerivative_hasWeak dimension order rank domain exponent bound jet,
    orderedDerivative_weakFamily dimension order rank domain exponent bound jet⟩

theorem integral_consumer : IntegralGoal := orderedDerivative_integral

theorem multiplicity_consumer : MultiplicityGoal := by
  intro dimension order rank domain exponent bound jet
  exact ⟨orderedDerivative_multiplicity_sum dimension order rank domain exponent bound jet,
    orderedDerivative_multiplicity_norm dimension order rank domain exponent bound jet⟩

theorem norm_consumer : NormGoal := orderedDerivative_normComparison

theorem bound_consumer : BoundGoal := by
  intro dimension order rank domain exponent bound
  exact ⟨canonical_norm_le dimension order rank domain exponent bound,
    orderedDerivative_norm_le dimension order rank domain exponent bound,
    orderedDerivative_opNorm_le dimension order rank domain exponent bound⟩

theorem zero_consumer : ZeroGoal := by
  intro dimension order domain exponent jet
  exact ⟨orderedDerivative_zero dimension order domain exponent jet,
    orderedDerivative_zero_norm dimension order domain exponent jet⟩

theorem coherence_consumer : CoherenceGoal := orderedDerivative_inclusion

theorem block_consumer : BlockGoal :=
  ⟨index_consumer, assembly_consumer, weak_consumer, integral_consumer, multiplicity_consumer,
    norm_consumer, bound_consumer, zero_consumer, coherence_consumer⟩

end Grad.WeightedJets.Ordered

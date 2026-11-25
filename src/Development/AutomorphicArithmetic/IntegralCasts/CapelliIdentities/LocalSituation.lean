module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

@[expose] public section

theorem UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem :
    ∀ {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
      (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (w : Fin r → E),
      ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ c • w ∈ X.Λ := by
  intro E _ _ _ r X w
  have hw : w ∈ Submodule.span E (X.Λ : Set (Fin r → E)) := by
    rw [X.Λ_span]; exact Submodule.mem_top
  obtain ⟨v, hv, c, rfl⟩ :=
    (IsLocalization.mem_span_iff (nonZeroDivisors (NumberField.RingOfIntegers E))).mp hw
  refine ⟨c, nonZeroDivisors.ne_zero c.property, ?_⟩
  rw [← smul_assoc, IsLocalization.smul_mk'_self, map_one, one_smul]
  simpa using hv

module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalRootReZeroImSq

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CompanionTheory.Ar.Fl Submodule

namespace PositivityTheory.Xgf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem symplectic_form_skew (D : Datum H) (x y : D.La) : D.EF x y = -D.EF y x := by
  have := D.alt (x + y); simp [D.alt] at this; linarith

theorem Host_rt0_ne_neg : H.rt0 ≠ -H.rt0 := fun h =>
  H.d_prime.ne_zero (Nat.cast_eq_zero.1 (by grind [H.sqrt_neg_disc_sq] : (H.d : ℂ) = 0))

theorem pure_type_lattices_orthogonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (a b : D.La), a ∈ PureType.lat hP (sgnRt H true) → b ∈ PureType.lat hP (sgnRt H false) → sesq D a b = 0 ∧ sesq D b a = 0 := by
  intro E _ _ _ H D g ty P hP a b ha hb
  constructor <;> refine Finset.sum_eq_zero fun k _ => ?_
  · simp [CM.FamCompare.orth_of_pure hP (smul_mem _ _ ha) hb]
  · rw [symplectic_form_skew D]
    simp [CM.FamCompare.orth_of_pure hP ha (smul_mem _ _ hb)]

theorem pure_family_decomposition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (p q : ℕ) (x : Fin p ⊕ Fin q → D.La) (n : ℕ), IsPure hP x → (∀ y : D.La, n • y ∈ Submodule.span (𝓞 E) (Set.range x)) → (∀ y : D.La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) ∧ (∀ y ∈ PureType.lat hP (sgnRt H true), n • y ∈ Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inl))) ∧ ∀ y ∈ PureType.lat hP (sgnRt H false), n • y ∈ Submodule.span (𝓞 E) (Set.range (x ∘ Sum.inr)) := by
  intro E _ _ _ H D g ty P hP p q x n hx hn
  have hL := span_le.2 (Set.range_subset_iff.2 hx.1)
  have hR := span_le.2 (Set.range_subset_iff.2 hx.2)
  have hd := disjoint_def.1 (PureType.disjoint_lat hP (Host_rt0_ne_neg (H := H)))
  simp_rw [Sum.range_eq, span_union, mem_sup] at hn
  refine ⟨?_, ?_, ?_⟩ <;> intro y <;> obtain ⟨a, ha, b, hb, e⟩ := hn y
  · exact ⟨a, hL ha, b, hR hb, e.symm⟩
  · intro hy
    have := hd _ (eq_sub_of_add_eq' e ▸ sub_mem (nsmul_mem hy n) (hL ha)) (hR hb)
    grind
  · intro hy
    have := hd _ (hL ha) (eq_sub_of_add_eq e ▸ sub_mem (nsmul_mem hy n) (hR hb))
    grind

end PositivityTheory.Xgf

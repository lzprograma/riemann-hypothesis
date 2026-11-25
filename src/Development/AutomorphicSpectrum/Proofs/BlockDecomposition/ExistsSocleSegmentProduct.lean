module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityCuspidalProductStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentTermInjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegSocle

theorem dec_injective {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) :
    Function.Injective (dec Δ) :=
  (_root_.GlobalTheory.CompanionTheory.SegTerm.term_injective hA Δ).comp Fin.rev_injective

theorem ncard_perm_dec_le_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) :
    Set.ncard {e : Fin Δ.len ≃ Fin Δ.len | ∀ a, dec Δ a = dec Δ (e a)} ≤ 1 := by
  rw [Set.ncard_le_one_iff_subsingleton]
  intro e₁ h₁ e₂ h₂
  ext a
  have i₁ := dec_injective hA Δ (h₁ a)
  have i₂ := dec_injective hA Δ (h₂ a)
  rw [← i₁, ← i₂]

theorem exists_isSocle_prodIrr_dec : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (_ : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ}
    (hd : ∑ a, (dec Δ a).1 = N), ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr (dec Δ) hd) := by
  intro k _ _ _ _ hA Δ N hd
  apply GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one hA (dec Δ) hd
  have hc : ∀ a, (dec Δ a).IsCusp := fun a => Δ.isCusp_term (Fin.rev a)
  rw [_root_.GlobalTheory.CompanionTheory.CuspJm.main hA (dec Δ) (dec Δ) hd hd hc hc]
  exact_mod_cast ncard_perm_dec_le_one hA Δ

end GlobalTheory.CompanionTheory.SegSocle

end

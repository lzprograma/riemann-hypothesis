module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FixedNeBotOfEquiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRecLawsSuppUnitSurj
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt

@[expose] public section



section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.SplitRead
namespace GlobalTheory.LocLanglands
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
theorem _root_.UpperTheory.Zero.LLC.IsRecT.recSupp {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : _root_.UpperTheory.Zero.LLC.IsRecT h rc) :
    RecSupp fun _ (π : Irr (w.adicCompletion E) _) => rc (cls (toIrrRep π)) := by
  first | (have hOpn := UpperTheory.One.M.opn _ (H); obtain ⟨a, ha, ε, H⟩ := hOpn)
  intro n s π d σ hs g
  have h1 := (hasSupport_of_isCuspSupport hs).of_equiv (equivRep (toIrrRep π))
  have h2 := H.supp (cls (toIrrRep π)) _ h1 g
  rw [Multiset.map_map] at h2
  exact h2
theorem _root_.UpperTheory.Zero.LLC.IsRecT.recUnit {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : _root_.UpperTheory.Zero.LLC.IsRecT h rc) :
    RecUnit fun _ (π : Irr (w.adicCompletion E) _) => rc (cls (toIrrRep π)) := by
  first | (have hOpn := UpperTheory.One.M.opn _ (H); obtain ⟨a, ha, ε, H⟩ := hOpn)
  intro χ c hu hc g α hα
  obtain ⟨hχ, e⟩ := cls_eq_ofChar χ c hc
  simp only [e, H.one, eig_lpOfChar, Multiset.mem_singleton] at hα
  rw [hα]
  exact hu _
end GlobalTheory.LocLanglands
end
end

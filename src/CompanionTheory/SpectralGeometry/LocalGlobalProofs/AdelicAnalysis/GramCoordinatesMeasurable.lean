module
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussQ
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompact
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
@[expose] public section
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.BB

theorem continuous_gmat_entry {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    (p q : Fin M × Fin d) :
    Continuous fun h : HA R σ J => gmat R σ J b h p q := by
  classical
  let X : Fin 1 → Fin M → R ⊗[F] E := fun _ => Pi.single q.1 (inclR R (b q.2))
  suffices Continuous (fun h : HA R σ J => (Algebra.TensorProduct.basis R b).repr (actW R σ J h X 0 p.1) p.2) by
    simpa [gmat, actW, actTup, X, Matrix.mulVec_single] using this
  exact (continuous_apply p.2).comp <|
    ((_root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R).2.2.2.2.2.2.1 d b).continuous.comp <|
    (continuous_apply p.1).comp <| (continuous_apply (0 : Fin 1)).comp <|
    ((_root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hσ M J hJ R).2.2.2.2.2 1).1.comp
      (continuous_id.prodMk (continuous_const : Continuous fun _ : HA R σ J => X))

theorem ginf_gfin_measurable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ w p q, Measurable fun ω => ginf e σ J b ω w p q) ∧ (∀ p q, Measurable fun ω => gfin σ J b ω p q) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b e he
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨htg, -, -, -, hbor, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hσ M J hJ (AF F)
  have hinv (p q : Fin M × Fin d) := (continuous_gmat_entry σ hσ J hJ b (AF F) p q).comp continuous_inv
  letI : BorelSpace (Af F) := ⟨rfl⟩
  exact ⟨fun w p q => ((continuous_apply w).comp (he.continuous.comp (hinv p q).fst)).measurable,
    fun p q => (hinv p q).snd.measurable⟩
end GlobalTheory.CompanionTheory.SW.BB

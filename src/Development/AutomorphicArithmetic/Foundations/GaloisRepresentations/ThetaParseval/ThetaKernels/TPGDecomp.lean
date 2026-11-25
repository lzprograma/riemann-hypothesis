module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LatAtVSelfDualK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Stab2CptK
public import Development.WeilBound.ThetaLifts.LatticeBasics.CommuteTheta
public import Development.WeilBound.ThetaLifts.LatticeBasics.HodgeTateFromSandwich
public import Development.WeilBound.ThetaLifts.LatticeBasics.SchrUnit
public import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.AdelInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleEqZeroOfComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcCompFinAwayPtOfNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTransitive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.ContinuousExpG
public import Development.WeilBound.ThetaLifts.LatticeBasics.BadFactor
public import Development.WeilBound.ThetaLifts.LatticeBasics.EulerProd
public import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.TracePiReal
public import Development.WeilBound.ThetaLifts.LatticeBasics.ContinuousFlat

/-! # TPGDecomp: Consolidated global theta-kernel definitions and proofs (TPGDecomp). -/
@[expose] public section

open GlobalTheory.ThK (IsPair_k)

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
open GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
open GlobalTheory.UnitaryBC (RU HasWeightAt)
open GlobalTheory.UnitaryBC (IsAutFormU IsAutRepU UA)
namespace UpperTheory.TP
structure Tools_k : Prop where
  swFull : SWFullX_k
  boxSec : BoxSecX_k
  dbl : DblX_k
  stab2 : Stab2Cpt_k
  cpt : CptAll_k
  basic : ThetaBasic_k
  polSch : PolSch_k
  unfold0 : Unfold0_k
  pairEx : PositivityTheory.ThKG.Tow.PairEx_k
  split : SplitModel_k
  vacFix : VacFix2_k
  acts : ActsEx_k
  lie1 : GlobalTheory.RealLift.LieFirst
  lie2 : GlobalTheory.RealLift.LieSecond
def TLift_k : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E), W.GoodK (cj E) B →
    ∀ (n : ℕ), 1 ≤ n → ∀ X : Spc (maximalRealSubfield E) E n, X.J = 1 → X.IsHerm (cj E) B n 0 →
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ (W : Spc (maximalRealSubfield E) E d) (δ : E), W.J = δ • (1 : Matrix (Fin d) (Fin d) E) →
      W.IsSkew (cj E) B d 0 → ∀ (χX χW : Chr (maximalRealSubfield E) E) (mX mW : InfinitePlace (maximalRealSubfield E) →
        ℤ),
      IsHecke (maximalRealSubfield E) E χX → IsHecke (maximalRealSubfield E) E χW →
      ResEtaPow (Units.map (algebraMap (maximalRealSubfield E) (AF (maximalRealSubfield E))).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap (maximalRealSubfield E) (AF (maximalRealSubfield E))).toMonoidHom).range χW d →
      HasExp B.emb χX mX → HasExp B.emb χW mW →
      ∀ (U : Submodule ℂ (UA E n → ℂ)) (lam : InfinitePlace (maximalRealSubfield E) → DomWeight
        n),
        IsAutRepU U → (∀ w, HasWeightAt U (B.emb w).1 (lam w)) →
        (∀ w k, (d : ℤ) + mW w ≤ 2 * (lam w).w k) → ∃ U' : Submodule ℂ (UA E d → ℂ),
          IsLift B χX χW mX mW lam U U'
def HgtFst_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n :
    ℕ) (X : Spc F E n), W.GoodK σ B → X.IsHerm σ B n 0 →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∃ t₀ : ℝ, ∀ μ : Measure (UA σ X.J), μ.IsHaarMeasure → ∀ t, t₀ ≤ t → Integrable (fun g => a (e (g, 1)) ^ t) μ
def Rallis_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d :
    ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W),
      IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n → 1 ≤ d →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ t₀ : ℝ, (∀ t, t₀ ≤ t → Integrable (fun g => a (e (g, 1)) ^ t) M.μ) → t₀ < (d : ℝ) / 2 →
    ∀ ν, @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ Φ ∈ PolData B M, ∀ φ, IsFn φ →
      Integrable (fun g => coef om ν Φ g * star (mc M φ g)) M.μ ∧
        (lift M om Φ φ = 0 → ∫ g, coef om ν Φ g * star (mc M φ g) ∂M.μ = 0)
def Decomp_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n :
    ℕ) (X : Spc F E n), W.GoodK σ B → X.IsHerm σ B n 0 → ∀ S : Finset (Pl F),
    (∃ j : gInf σ X × gAt σ X S × gOff σ X S ≃ₜ* UA σ X.J, ∀ x, j x = x.1.1 * x.2.1.1 * x.2.2.1) ∧
    IsCompact (gInf σ X : Set (UA σ X.J)) ∧ IsClosed (gAt σ X S : Set (UA σ X.J)) ∧ IsClosed (gOff σ X S : Set (UA σ
      X.J)) ∧
    IsCompact {g : UA σ X.J | IntAll g} ∧ IsOpen {g : UA σ X.J | IntAll g} ∧ (∀ g ∈ gInf σ X, IntAll g) ∧
    (∀ b ∈ gAt σ X S, ∃ c : Pl F → UA σ X.J, (∀ v, c v ∈ locGrp σ X v) ∧ (∀ v ∈ S, OffAt v ((c v)⁻¹ * b)) ∧
      ∀ H : Subgroup (UA σ X.J), (∀ v ∈ S, c v ∈ H) → b ∈ H) ∧
    ∀ g : UA σ X.J, {v | ¬ IntAt v g}.Finite
def BumpAny_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d :
    ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W),
      IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n → 2 * n ≤ d →
    ∀ v, ∀ N ∈ 𝓝 (1 : UA σ X.J), ∃ H φ, IsBump B M om v H φ ∧ (H : Set (UA σ X.J)) ⊆ N
def Datum_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d :
    ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W),
      IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ ν, @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ S : Finset (Pl F), UnrOff χW (S : Set (Pl F)) →
    ∀ (H : Pl F → Subgroup (UA σ X.J)) φ, IsFin M φ → (∀ v ∈ S, IsBump B M om v (H v) (φ v)) → (∀ v ∉ S,
      φ v = M.vac v) →
    ∀ f₀ ∈ M.Pol B.ψ B.emb, f₀ ≠ 0 → coef om ν (pure f₀ φ) 1 ≠ 0 ∧
      ∀ x ∈ gInf σ X, ∀ b ∈ gAt σ X S, ∀ c ∈ gOff σ X S, (b ∉ ⨆ v ∈ S, H v → coef om ν (pure f₀ φ) (x * b * c) = 0) ∧
        ∃ s : ℂ, ‖s‖ = a (e (c, 1)) ^ ((d : ℝ) / 2) ∧ (IntAll c → s = 1) ∧
          ∀ x' ∈ gInf σ X, ∀ b' ∈ ⨆ v ∈ S, H v, coef om ν (pure f₀ φ) (x' * b' * c) = s * coef om ν (pure f₀ φ) x'
def Tail_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n :
    ℕ) (X : Spc F E n), W.GoodK σ B → X.IsHerm σ B n 0 →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ (μ : Measure (UA σ X.J)) (t : ℝ), μ.IsHaarMeasure → Integrable (fun g => a (e (g,
      1)) ^ t) μ → ∀ S₀ : Finset (Pl F),
      ∃ S : Finset (Pl F), S₀ ⊆ S ∧ ∀ μC : Measure (gOff σ X S), μC.IsHaarMeasure →
        ∫⁻ c in {c : gOff σ X S | ¬ IntAll c.1}, ENNReal.ofReal (a (e (c.1, 1)) ^ t) ∂μC < μC {c | IntAll c.1}
def RealPair_k : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E) (n d : ℕ) (X : Spc
    (maximalRealSubfield E) E n) (W : Spc (maximalRealSubfield E) E d)
    (M : Model (cj E) X W) (χX χW : Chr (maximalRealSubfield E) E) (om : Rep (cj E) X W),
      IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ (e : UA E n ≃ₜ* UA (cj E) X.J) (e' : UA E d ≃ₜ* UA (cj E) W.J),
      IsBr X e → IsBr W e' → n ≤ d →
    ∀ (δ : E) (mX mW : InfinitePlace (maximalRealSubfield E) → ℤ),
      X.J = 1 → W.J = δ • (1 : Matrix (Fin d) (Fin d) E) → HasExp B.emb χX mX →
    HasExp B.emb χW mW → ∀ (U : Submodule ℂ (UA E n → ℂ)) (lam : InfinitePlace
      (maximalRealSubfield E) → DomWeight n),
      IsAutRepU U → (∀ w, HasWeightAt U (B.emb w).1 (lam w)) →
      (∀ w k, (d : ℤ) + mW w ≤ 2 * (lam w).w k) → ∃ f₀ ∈ M.Pol B.ψ B.emb, f₀ ≠ 0 ∧ ∃ φ ∈ U,
        φ ≠ 0 ∧ SameType om e U f₀ φ ∧
        ∀ w, ∃ lam', IsLiftWt (lam w) (mX w) (mW w) lam' ∧ HasType B M om e' f₀ w lam'
def SchurStep_k : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E) (n d : ℕ) (X : Spc
    (maximalRealSubfield E) E n) (W : Spc (maximalRealSubfield E) E d)
    (M : Model (cj E) X W) (χX χW : Chr (maximalRealSubfield E) E) (om : Rep (cj E) X W),
      IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ (e : UA E n ≃ₜ* UA (cj E) X.J) (e' : UA E d ≃ₜ* UA (cj E) W.J),
      IsBr X e → IsBr W e' →
    ∀ (U : Submodule ℂ (UA E n → ℂ)), IsAutRepU U → ∀ f₀, f₀ ≠ 0 → ∀ φ,
      φ ≠ 0 → SameType om e U f₀ φ →
    ∀ ν, @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ φf, IsFin M φf → ∀ μA : Measure (gInf (cj E) X),
      μA.IsHaarMeasure →
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ c ∈ gOff (cj E) X ∅, ∫ x, coef om ν (pure f₀ φf) x.1 * star (mc M (φ ∘ e.symm) (x.1 * c)) ∂μA =
      κ * coef om ν (pure f₀ φf) 1 * star (mc M (φ ∘ e.symm) c)
def NonVan_k : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E) (n d : ℕ) (X : Spc
    (maximalRealSubfield E) E n) (W : Spc (maximalRealSubfield E) E d)
    (M : Model (cj E) X W) (χX χW : Chr (maximalRealSubfield E) E) (om : Rep (cj E) X W),
      IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ (e : UA E n ≃ₜ* UA (cj E) X.J) (e' : UA E d ≃ₜ* UA (cj E) W.J),
      IsBr X e → IsBr W e' → 2 * n ≤ d →
    ∀ K a (ε : UA (cj E) X.J × UA (cj E) X.J →* G2 (cj E) X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (ε (g,
      g'))) →
    ∀ t₀ : ℝ, (∀ t, t₀ ≤ t → Integrable (fun g => a (ε (g, 1)) ^ t) M.μ) → t₀ < (d : ℝ) / 2 →
    ∀ (U : Submodule ℂ (UA E n → ℂ)),
      IsAutRepU U → ∀ f₀ ∈ M.Pol B.ψ B.emb, f₀ ≠ 0 → ∀ φ, φ ≠ 0 →
      SameType om e U f₀ φ → ∃ φf, IsFin M φf ∧ lift M om (pure f₀ φf) (φ ∘ e.symm) ≠ 0
def LiftAut_k : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E) (n d : ℕ) (X : Spc
    (maximalRealSubfield E) E n) (W : Spc (maximalRealSubfield E) E d)
    (M : Model (cj E) X W) (χX χW : Chr (maximalRealSubfield E) E) (om : Rep (cj E) X W),
      IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ (e : UA E n ≃ₜ* UA (cj E) X.J) (e' : UA E d ≃ₜ* UA (cj E) W.J),
      IsBr X e → IsBr W e' →
    ∃ Θ : PolData B M →ₗ[ℂ] (UA E n → ℂ) →ₛₗ[starRingEnd ℂ] (UA E d → ℂ),
      ∀ (Φ : PolData B M) φ,
        IsAutFormU φ → Θ Φ φ = lift M om Φ.1 (φ ∘ e.symm) ∘ e' ∧
        IsAutFormU (Θ Φ φ) ∧
        ∀ g h, ∃ Φ₁ : PolData B M, Φ₁.1 = om (e g, e' h) Φ.1 ∧
          Θ Φ₁ (RU E n g φ) = RU E d h (Θ Φ φ)
def ReadLift_k : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E) (n d : ℕ) (X : Spc
    (maximalRealSubfield E) E n) (W : Spc (maximalRealSubfield E) E d)
    (M : Model (cj E) X W) (χX χW : Chr (maximalRealSubfield E) E) (om : Rep (cj E) X W),
      IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ (e : UA E n ≃ₜ* UA (cj E) X.J) (e' : UA E d ≃ₜ* UA (cj E) W.J),
      IsBr X e → IsBr W e' →
    ∀ (U : Submodule ℂ (UA E n → ℂ)) (U' : Submodule ℂ (UA E d → ℂ))
      (pr : (UA E d → ℂ) →ₗ[ℂ] (UA E d → ℂ)),
        IsAutRepU U → IsAutRepU U' →
      (∀ f, IsAutFormU f → pr f ∈ U' ∧ ∀ x,
        pr (RU E d x f) = RU E d x (pr f)) →
      ∀ f₀ ∈ M.Pol B.ψ B.emb, ∀ φ ∈ U, ∀ φf, IsFin M φf → pr (lift M om (pure f₀ φf) (φ ∘ e.symm) ∘ e') ≠ 0 →
      (∀ w lam', HasType B M om e' f₀ w lam' → HasWeightAt U' (B.emb w).1 lam') ∧
      ∀ (v : Pl (maximalRealSubfield E)) (t : E →ₐ[maximalRealSubfield E] Fv (maximalRealSubfield E) v) τ τ',
        CompAt U (splitPrime t) τ → CompAt U' (splitPrime t) τ' →
        LocPair t χX χW τ τ'
theorem tLift_of_k (T : Tools_k) (hH : GlobalTheory.ThK.Dbl.HgtEx_k) (h1 : BrEx) (h2 : HgtFst_k) (h3 :
  RealPair_k) (h4 : NonVan_k) (h5 : LiftAut_k) (h6 : ProjEx)
    (h7 : ReadLift_k) : TLift_k := by
  intro E _ _ _ B hB n hn X hXJ hX
  obtain ⟨⟨K, a, hK, ha, -⟩, ε, -, hε⟩ := hH _ E (cj E) B n X n 0 hB (Or.inl hX)
  obtain ⟨t₀, ht₀⟩ := h2 _ E (cj E) B n X hB hX K a ε hK ha hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * t₀)
  refine ⟨max N (2 * n), fun d hd W δ hWJ hW χX χW mX mW hχX hχW rX rW eX eW U lam hU hwt hdom => ?_⟩
  have hd1 : 2 * n ≤ d := (le_max_right _ _).trans hd
  have hd2 : t₀ < (d : ℝ) / 2 := by
    have : (N : ℝ) ≤ d := by exact_mod_cast (le_max_left _ _).trans hd
    linarith
  have hδ : δ ≠ 0 := by
    rintro rfl
    obtain ⟨w⟩ : Nonempty (InfinitePlace (maximalRealSubfield E)) := inferInstance
    obtain ⟨-, A, hA⟩ := hW.sig w
    have := congrFun (congrFun hA (Sum.inl ⟨0, by omega⟩)) (Sum.inl ⟨0, by omega⟩)
    simp [hWJ] at this
  obtain ⟨⟨M, hM⟩, hom⟩ := T.pairEx _ E (cj E) B hB n d X W n 0 d 0 hX hW
  obtain ⟨om, hP⟩ := hom χX χW hχX hχW rX rW M hM
  obtain ⟨e, he⟩ := h1 E n X 1 one_ne_zero (by rw [hXJ, one_smul])
  obtain ⟨e', he'⟩ := h1 E d W δ hδ hWJ
  obtain ⟨f₀, hf₀, hf0, φ, hφ, hφ0, hS, hT⟩ := h3 E B n d X W M χX χW om hP hn e e' he he'
    (by omega) δ mX mW hXJ hWJ eX eW U lam hU hwt hdom
  obtain ⟨φf, hfin,
    hne⟩ := h4 E B n d X W M χX χW om hP hn e e' he he' hd1 K a ε hK ha hε t₀ (ht₀ M.μ hM.haar) hd2 U hU f₀ hf₀ hf0 φ
    hφ0 hS
  obtain ⟨Θ, hΘ⟩ := h5 E B n d X W M χX χW om hP hn e e' he he'
  have hmem : pure f₀ φf ∈ PolData B M := Submodule.subset_span ⟨f₀, hf₀, φf, hfin.1, hfin.2, rfl⟩
  obtain ⟨q1, q2, -⟩ := hΘ ⟨_, hmem⟩ φ (hU.aut φ hφ)
  have hne' : Θ ⟨_, hmem⟩ φ ≠ 0 := by
    rw [q1]
    intro h0
    apply hne
    funext h
    have := congrFun h0 (e'.symm h)
    simpa using this
  obtain ⟨U', pr, hU', hpr, hp⟩ := h6 E d _ q2 hne'
  rw [q1] at hpr
  obtain ⟨r1, r2⟩ := h7 E B n d X W M χX χW om hP hn e e' he he' U U' pr hU hU' hp f₀ hf₀ φ hφ φf hfin hpr
  exact ⟨U', hU', fun w => (hT w).imp fun lam' h => ⟨r1 w lam' h.2, h.1⟩, r2⟩
end UpperTheory.TP
end

noncomputable section
namespace GlobalTheory.ThK.Dbl.Bad
open PositivityTheory.ThKG.Loc.Cone
open UpperTheory.TP.W (GoodK)
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc (idem)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
section
variable {Y : Spc F E n} {B : Base F E} {v : Pl F} {r s : ℕ}
theorem theta_pm_k (hB : GoodK σ B) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) (w) : Y.θ w = 1 ∨
  Y.θ w = -1 :=
  cartan_pm (h.sig w) h0 (fun i j => (hB.cm.2.2.2 _ _).symm.trans (congrArg _ (h.herm i j))) (h.cartan w)
theorem commute_theta_k (hB : GoodK σ B) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) (w) (A) :
  Commute A (Y.θ w) := by
  rcases theta_pm_k hB h h0 w with e | e <;> rw [e]
  exacts [Commute.one_right _, Commute.neg_one_right _]
theorem stab_iff_k (hB : GoodK σ B) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) {K : Subgroup (UA
  σ Y.J)} (hK : IsStab B K)
    {g : UA σ Y.J} : g ∈ K ↔ ∀ v, IntAt v g :=
  (hK g).trans ⟨fun a _ z hz _ => a.2 z hz, fun a => ⟨fun w => commute_theta_k hB h h0 w _, fun _ hz =>
    ⟨mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (a v z h1 h2).1) hz,
      mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (a v z h1 h2).2) hz⟩⟩⟩
theorem emb_mem_k (hB : GoodK σ B) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) {K : Subgroup (G2 σ
  Y)} (hK : IsStab2 B K)
    {e : UA σ Y.J × UA σ Y.J →* G2 σ Y} (he : ∀ g g', IsEmb g g' (e (g, g'))) {g : UA σ Y.J} (hg : ∀ v, IntAt v g) :
    e (g, 1) ∈ K := by
  refine (hK _).2 ⟨fun w => ?_, fun z z' hz hz' k hk => ?_⟩
  · rw [he g 1, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _)]
    simp only [Commute, SemiconjBy, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      (commute_theta_k hB h h0 w _).eq, (commute_theta_k hB h h0 w _).neg_right.eq]
  · obtain ⟨g', e1, hg'⟩ : ∃ g', k = e (g', 1) ∧ mat g' *ᵥ z ∈ latHat Y := by
      rcases hk with rfl | rfl
      · exact ⟨g, rfl, mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (hg v z h1 h2).1) hz⟩
      · exact ⟨g⁻¹, by rw [← map_inv, Prod.inv_mk, inv_one],
          mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (hg v z h1 h2).2) hz⟩
    rw [e1, he g' 1, Matrix.fromBlocks_mulVec, show mat (1 : UA σ Y.J) = 1 from rfl]
    simpa using ⟨hg', hz'⟩
end

section
variable {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r'
  s' : ℕ}
theorem orth_k (P : IsPair_k B M χX χW om r s r' s') {ν} (hν : @Measure.IsAddHaarMeasure _ _ _
  (borel _) ν) {Φ} (h : Φ ∈ schA F _)
    (h0 : Φ ≠ 0) {g u} {c c' : ℂ} (hc : c ≠ c') (h1 : M.co.rho B.ψ u Φ = c • Φ) (h2 : M.co.rho B.ψ (mat g * u) Φ = c' •
      Φ) :
    coef om ν Φ g = 0 := by
  by_contra hn
  have i := P.weil.isUSplitting.impl (g, 1) u Φ h
  rw [h1, map_smul, show actAB (cA σ) (g,
    1) u = mat g * u from (congrArg _ Matrix.transpose_one).trans (Matrix.mul_one _)] at i
  have a1 := schr_unit P.base.std ν hν (M.co.e (mat g * u)) (om (g, 1) Φ) Φ
  have a2 := schr_unit P.base.std ν hν (M.co.e (mat g * u)) Φ Φ
  have k : ∀ (A : Fn F n d) (t : ℂ), ∫ x, (t • A) x * star ((c' • Φ) x) ∂ν = t * star c' * ∫ x,
    A x * star (Φ x) ∂ν := fun A t => by
    rw [← integral_const_mul]
    exact integral_congr_ae (.of_forall fun x => by simp only [Pi.smul_apply, smul_eq_mul, star_mul']; ring)
  rw [show schr B.ψ (M.co.e (mat g * u)) Φ = _ from h2] at a1 a2
  rw [show schr B.ψ (M.co.e (mat g * u)) (om (g, 1) Φ) = _ from i.symm, k] at a1
  rw [k] at a2
  have b1 := (mul_eq_right₀ hn).1 a1
  have b2 := (mul_eq_right₀ (sq_ne ν hν h h0)).1 a2
  exact hc (mul_right_cancel₀ (right_ne_zero_of_mul_eq_one b1) (b1.trans b2.symm))
theorem law_k {dd om₂ S l} (hB : GoodK σ B) (h : IsDbl (σ := σ) (A := W) (Y := X) (κ := (Fin n ×
  Fin d) ⊕ (Fin n × Fin d)) B.ψ dd χW om₂ S l)
    {Ψ} (hΨ : Ψ ∈ schA F _) : Law χW (d / 2) fun x => l (om₂ x Ψ) := fun p t x hp => by
  have := hB.cm.1
  beta_reduce
  rw [map_mul, mul_apply_eq_comp, h.weil.2.2 l h.adm h.kill p t hp _ (h.weil.2.1.pres x Ψ hΨ),
    PositivityTheory.ThKF0.Chr.absE_eq,
    Complex.ofReal_cpow (NNReal.coe_nonneg _), Fintype.card_fin]
  push_cast
  rfl
end
end GlobalTheory.ThK.Dbl.Bad
end

section
open GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions UpperTheory.TP
theorem UpperTheory.continuous_thetaLift_of_definite :
    UpperTheory.TP.Tools_k → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ
      : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om :
      Rep σ X W), IsPair_k B M χX χW om n 0 d 0 → ∀ Φ ∈ schA F (Fin n × Fin d),
      ∀ φ : UA σ X.J → ℂ, IsFn φ → Continuous (lift M om Φ φ) := by
  intro T F E _ _ _ _ _ σ B n d X W M χX χW om hp Φ hΦ φ hφ
  have cX : Cpt σ X.J := T.cpt F E σ B n X n 0 hp.base (Or.inl hp.herm) (by simp)
  have cW : Cpt σ W.J := T.cpt F E σ B d W d 0 hp.base (Or.inr hp.skew) (by simp)
  obtain ⟨t1, t2, -⟩ := (T.basic F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp).1 Φ hΦ
  obtain ⟨C, hC⟩ := cX.bdd₂ cW (f := fun x => theta om Φ x.1 x.2) t1 fun γ hγ δ hδ g g' => t2 γ hγ δ hδ g g'
  obtain ⟨C', hC'⟩ := cX.bdd hφ.1 hφ.2
  have hfin : M.μ M.dom < ⊤ := cX.fin _ _ hp.good.haar hp.good.dom
  have : IsFiniteMeasure (M.μ.restrict M.dom) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have := cW.sc
  have : FirstCountableTopology (UA σ W.J) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  have hs := hφ.1.star
  unfold lift
  refine continuous_of_dominated (bound := fun _ => C * C') (fun h => ?_) (fun h => ?_) (integrable_const _) ?_
  · exact ((t1.comp (continuous_id.prodMk continuous_const)).mul hs).aestronglyMeasurable
  · refine Eventually.of_forall fun g => ?_
    rw [norm_mul, norm_star]
    exact mul_le_mul (hC (g, h)) (hC' g) (norm_nonneg _) ((norm_nonneg _).trans (hC (g, h)))
  · refine Eventually.of_forall fun g => ?_
    exact (t1.comp (continuous_const.prodMk continuous_id)).mul continuous_const
end

noncomputable section
namespace UpperTheory.TP
open scoped Classical
open Formalism.BasicNotions GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Bad GlobalTheory.PRep
  PositivityTheory.ThKG.Loc.Cone
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc (idem)
open GlobalTheory.ThK.Dbl.Euler (cut cut_mul cut_form cut_sub cut_eq cut_one mm cont_mat prj)
private theorem cut_add_pk {S R k : Type} [CommRing S] [CommRing R] [Algebra S R] [Fintype k] [DecidableEq k]
    {a b : S} (hab : a * b = 0) (A : Matrix k k R) : cut a A * cut b A = cut (a + b) A := by
  have e : ∀ c : S, cut c A = 1 + c • (A - 1) := fun c => eq_add_of_sub_eq' (cut_sub A)
  have h' : b * a = 0 := by rw [mul_comm, hab]
  rw [e, e, e]
  simp only [add_mul, mul_add, one_mul, mul_one, add_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h',
    zero_smul, add_zero]; abel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
variable {X : Spc F E n}

private def pr_pk (e : AF F) (he : e * e = e) : UA σ X.J →* UA σ X.J :=
  MonoidHom.mk' (fun g => ⟨⟨cut e (mat g), cut e (mat g⁻¹),
    by rw [cut_mul he, ← mm, mul_inv_cancel]; exact cut_one,
    by rw [cut_mul he, ← mm, inv_mul_cancel]; exact cut_one⟩, cut_form he _ g.2⟩)
    fun _ _ => Subtype.ext (Units.ext (cut_mul he _ _).symm)

private theorem pr_eq_pk {e : AF F} {he : e * e = e} {g : UA σ X.J} :
    pr_pk e he g = g ↔ e • (mat g - 1) = mat g - 1 :=
  ⟨fun h => cut_eq.1 (congrArg mat h), fun h => Subtype.ext (Units.ext (cut_eq.2 h))⟩

private theorem pr_one_pk {e : AF F} {he : e * e = e} {g : UA σ X.J} (h : e • (mat g - 1) = 0) : pr_pk e he g = 1 :=
  Subtype.ext (Units.ext (sub_eq_zero.1 ((cut_sub (mat g)).trans h)))

private theorem cont_pr_pk {e : AF F} (he : e * e = e) : Continuous (pr_pk e he : UA σ X.J → UA σ X.J) := by
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  have c1 : Continuous fun g : UA σ X.J => cut e (mat g) := by
    have hm := cont_mat (σ := σ) (Y := X); unfold cut
    refine continuous_matrix fun i j => ?_
    have := hm.matrix_elem i j; simp only [Matrix.add_apply, Matrix.smul_apply]; fun_prop
  exact Continuous.subtype_mk (Units.continuous_iff.2 ⟨c1, c1.comp continuous_inv⟩) _

private theorem closed_fix_pk {e : AF F} (he : e * e = e) : IsClosed {g : UA σ X.J | e • (mat g - 1) = mat g - 1} := by
  have := (Euler.lcsc_UA σ X.J).2.2
  rw [show {g : UA σ X.J | e • (mat g - 1) = mat g - 1} = {g | pr_pk e he g = g} from Set.ext fun _ => pr_eq_pk.symm]
  exact isClosed_eq (cont_pr_pk he) continuous_id

private theorem idem_mul_sum_pk {T : Finset (Pl F)} {v : Pl F} (h : v ∈ T) :
    (Euler.idem v : AF F) * ∑ u ∈ T, Euler.idem u = Euler.idem v := by
  rw [Finset.mul_sum, Finset.sum_eq_single v (fun u _ hu => Euler.mul_idem (Euler.ev_ne hu)) (fun h' => absurd h h'),
    Euler.idem_sq]

private theorem sum_sq_pk (T : Finset (Pl F)) :
    (∑ v ∈ T, (Euler.idem v : AF F)) * ∑ v ∈ T, (Euler.idem v : AF F) = ∑ v ∈ T, (Euler.idem v : AF F) := by
  rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ hv => idem_mul_sum_pk hv

private theorem eps_sq_pk : realAd F 1 * realAd F 1 = realAd F 1 :=
  Prod.ext (by change (realAd F 1).1 * (realAd F 1).1 = _; rw [PositivityTheory.ThKG.Loc.Bump.eps_fst, one_mul])
    (by change (realAd F 1).2 * (realAd F 1).2 = _; rw [PositivityTheory.ThKG.Loc.Bump.eps_snd, zero_mul])

private theorem eps_mul_sum_pk (T : Finset (Pl F)) : realAd F 1 * ∑ v ∈ T, (Euler.idem v : AF F) = 0 := by
  have sf : (∑ v ∈ T, (Euler.idem v : AF F)).1 = 0 := by
    induction T using Finset.induction_on with
    | empty => rfl
    | insert v T hv ih => rw [Finset.sum_insert hv]; change (0 : Ainf F) + _ = 0; rw [ih, add_zero]
  exact Prod.ext (by change (realAd F 1).1 * _ = 0; rw [sf, mul_zero])
    (by change (realAd F 1).2 * _ = 0; rw [PositivityTheory.ThKG.Loc.Bump.eps_snd, zero_mul])

private theorem pr_sum_mem_pk (H : Subgroup (UA σ X.J)) (g : UA σ X.J) (T : Finset (Pl F))
    (h : ∀ v ∈ T, prj v g ∈ H) : pr_pk (∑ v ∈ T, Euler.idem v) (sum_sq_pk T) g ∈ H := by
  induction T using Finset.induction_on with
  | empty =>
    rw [show pr_pk (∑ v ∈ (∅ : Finset (Pl F)), Euler.idem v) (sum_sq_pk ∅) g = 1 from
      Subtype.ext (Units.ext (show cut _ (mat g) = 1 by simp [cut]))]
    exact one_mem _
  | insert v T hv ih =>
    have hoff : (Euler.idem v : AF F) * ∑ u ∈ T, Euler.idem u = 0 := by
      rw [Finset.mul_sum]; exact Finset.sum_eq_zero fun u hu => Euler.mul_idem (Euler.ev_ne fun e => hv (e ▸ hu))
    have : pr_pk (∑ u ∈ insert v T, Euler.idem u) (sum_sq_pk _) g =
        prj v g * pr_pk (∑ u ∈ T, Euler.idem u) (sum_sq_pk T) g := Subtype.ext (Units.ext (by
      change cut _ (mat g) = cut (Euler.idem v) (mat g) * cut _ (mat g)
      rw [cut_add_pk hoff, Finset.sum_insert hv]))
    rw [this]; exact mul_mem (h v (Finset.mem_insert_self _ _)) (ih fun u hu => h u (Finset.mem_insert_of_mem hu))

private theorem mem_gInf_pk {g : UA σ X.J} : g ∈ gInf σ X ↔ realAd F 1 • (mat g - 1) = mat g - 1 :=
  ⟨fun h => pr_eq_pk.1 (((Subgroup.closure_le (K := (pr_pk (σ := σ) (X := X) (realAd F 1) eps_sq_pk).eqLocus
      (MonoidHom.id _))).2 fun _ hg => pr_eq_pk.2 (PositivityTheory.ThKG.Loc.Bump.at_iff.1 hg)) h),
   fun h => Subgroup.subset_closure (PositivityTheory.ThKG.Loc.Bump.at_iff.2 h)⟩

private theorem mem_gAt_pk {S : Finset (Pl F)} {g : UA σ X.J} :
    g ∈ gAt σ X S ↔ (∑ v ∈ S, (Euler.idem v : AF F)) • (mat g - 1) = mat g - 1 :=
  ⟨fun h => pr_eq_pk.1 ((show gAt σ X S ≤ (pr_pk (∑ v ∈ S, Euler.idem v)
      (sum_sq_pk S)).eqLocus (MonoidHom.id _) from iSup₂_le fun v hv g hg => pr_eq_pk.2 (by
        have e := (pr_eq_pk (he := Euler.idem_sq v)).1 (Euler.mem_loc.1 hg)
        rw [← e, smul_smul, mul_comm, idem_mul_sum_pk hv])) h),
   fun h => by
    rw [← pr_eq_pk (he := sum_sq_pk S)] at h; rw [← h]
    exact pr_sum_mem_pk _ g S fun v hv => (le_iSup₂_of_le v hv le_rfl : locGrp σ X v ≤ gAt σ X S) (Euler.prj_mem g)⟩

private theorem smul_off_pk {v : Pl F} {g : UA σ X.J} (h : OffAt v g) : Euler.idem v • (mat g - 1) = 0 :=
  Matrix.ext fun i j => Bad.idem_off (by
    have := congrFun₂ h i j; rw [Matrix.map_apply] at this
    simp [this, Matrix.one_apply, apply_ite (compFin F E v)])

private theorem mem_gOff_pk {S : Finset (Pl F)} {g : UA σ X.J} :
    g ∈ gOff σ X S ↔ (1 - realAd F 1 - ∑ v ∈ S, (Euler.idem v : AF F)) • (mat g - 1) = mat g - 1 := by
  set b := ∑ v ∈ S, (Euler.idem v : AF F) with hb
  have h1 := eps_sq_pk (F := F); have h2 := sum_sq_pk S; have h3 := eps_mul_sum_pk S
  rw [← hb] at h2 h3
  have key : (1 - realAd F 1 - b) * (1 - realAd F 1 - b) = 1 - realAd F 1 - b := by linear_combination h1 + h2 + 2 * h3
  constructor
  · intro h
    refine pr_eq_pk.1 ((show gOff σ X S ≤ (pr_pk (σ := σ) (X := X) _ key).eqLocus (MonoidHom.id _) from
      (Subgroup.closure_le _).2 fun g ⟨hg1, hg2⟩ => pr_eq_pk.2 (by
        have e1 : realAd F 1 • (mat g - 1) = 0 := Matrix.ext fun i j => GlobalTheory.SWOpFin.tens_eq_zero_of_comp
          (fun v => PositivityTheory.ThKG.Loc.Bump.compFin_eps v _) fun w => by
            change compInf F E w (realAd F 1 • (mat g - 1) i j) = 0
            rw [PositivityTheory.ThKG.Loc.Bump.compInf_eps]
            have := congrFun₂ (hg1 w) i j; rw [Matrix.map_apply] at this
            simp [this, Matrix.one_apply, apply_ite (compInf F E w)]
        have e2 : b • (mat g - 1) = 0 := by
          rw [hb, Finset.sum_smul]; exact Finset.sum_eq_zero fun v hv => smul_off_pk (hg2 v hv)
        rw [sub_smul, sub_smul, one_smul, e1, e2, sub_zero, sub_zero])) h)
  · intro h
    refine Subgroup.subset_closure ⟨fun w => Matrix.ext fun i j => ?_, fun v hv => Euler.off_of (pr_one_pk (he :=
      Euler.idem_sq v) ?_)⟩
    · have hi : realAd F 1 • (mat g - 1) = 0 := by
        rw [← h, smul_smul, show realAd F 1 * (1 - realAd F 1 - b) = 0 by linear_combination -h3 - h1, zero_smul]
      have ht := PositivityTheory.ThKG.Loc.Bump.compInf_eps (E := E) w ((mat g - 1) i j)
      rw [show realAd F 1 • (mat g - 1) i j = 0 from congrFun₂ hi i j, map_zero, Matrix.sub_apply, map_sub] at ht
      rw [Matrix.map_apply, sub_eq_zero.1 ht.symm]; simp [Matrix.one_apply, apply_ite (compInf F E w)]
    · have h3' : (Euler.idem v : AF F) * realAd F 1 = 0 := Prod.ext (zero_mul _) (mul_zero _)
      have h4 := idem_mul_sum_pk hv; rw [← hb] at h4
      rw [← h, smul_smul, show (Euler.idem v : AF F) * (1 - realAd F 1 - b) = 0 by linear_combination -h3' - h4,
        zero_smul]

theorem decomp_k : Tools_k → Decomp_k := by
  intro _ F E _ _ _ _ _ σ B n X hB hX S
  have h00 : min n 0 = 0 := by simp
  obtain ⟨K, -, -, hK, hKc, -, -⟩ := PositivityTheory.ThKG.Tow.stabEx_k F E σ B n X n 0 hB hX
  have eK : (K : Set (UA σ X.J)) = {g | IntAll g} := Set.ext fun g => Bad.stab_iff_k hB hX h00 hK
  have h1 := eps_sq_pk (F := F); have h2 := sum_sq_pk (F := F) S; have h3 := eps_mul_sum_pk (F := F) S
  have hc : (1 - realAd F 1 - ∑ v ∈ S, (Euler.idem v : AF F)) * (1 - realAd F 1 - ∑ v ∈ S, (Euler.idem v : AF F)) =
      1 - realAd F 1 - ∑ v ∈ S, (Euler.idem v : AF F) := by linear_combination h1 + h2 + 2 * h3
  have hinfInt : ∀ g ∈ gInf σ X, IntAll g := fun g hg v => by
    have e : (Euler.idem v : AF F) * realAd F 1 = 0 := Prod.ext (zero_mul _) (mul_zero _)
    have hp : prj v g = 1 := pr_one_pk (he := Euler.idem_sq v) (by rw [← mem_gInf_pk.1 hg, smul_smul, e, zero_smul])
    exact Euler.int_prj.1 (hp ▸ one_mem (Euler.intGrp σ X v))
  have cI : IsClosed (gInf σ X : Set (UA σ X.J)) := by
    rw [show (gInf σ X : Set (UA σ X.J)) = {g | realAd F 1 • (mat g - 1) = mat g - 1} from Set.ext fun _ => mem_gInf_pk]
    exact closed_fix_pk h1
  have hprod : ∃ j : gInf σ X × gAt σ X S × gOff σ X S ≃ₜ* UA σ X.J, ∀ x, j x = x.1.1 * x.2.1.1 * x.2.2.1 := by
    set a := realAd F 1; set b := ∑ v ∈ S, (Euler.idem v : AF F); set c := 1 - a - b
    have hab : a * b = 0 := h3; have hac : a * c = 0 := by linear_combination -h3 - h1
    have hbc : b * c = 0 := by linear_combination -h3 - h2
    have hba : b * a = 0 := by rw [mul_comm, hab]
    have hca : c * a = 0 := by rw [mul_comm, hac]
    have hcb : c * b = 0 := by rw [mul_comm, hbc]
    have hd : (a + b) * (a + b) = a + b := by linear_combination h1 + h2 + 2 * hab
    have hdc : (a + b) * c = 0 := by linear_combination hac + hbc
    have p1 : ∀ {e f : AF F} {he : e * e = e}, e * f = 0 → ∀ {g : UA σ X.J}, f • (mat g - 1) = mat g - 1 →
        pr_pk e he g = 1 := by intro _ _ _ hef _ hg; exact pr_one_pk (by rw [← hg, smul_smul, hef, zero_smul])
    have pf : ∀ {e : AF F} (he : e * e = e) (g : UA σ X.J), e • (mat (pr_pk e he g) - 1) = mat (pr_pk e he g) - 1 :=
      fun {e} he g => by change e • (cut e (mat g) - 1) = _; rw [cut_sub, smul_smul, he]; exact (cut_sub _).symm
    let φ : UA σ X.J ≃ₜ* gInf σ X × gAt σ X S × gOff σ X S :=
      { toFun := fun g => (⟨pr_pk a h1 g, mem_gInf_pk.2 (pf h1 g)⟩, ⟨pr_pk b h2 g, mem_gAt_pk.2 (pf h2 g)⟩,
          ⟨pr_pk c hc g, mem_gOff_pk.2 (pf hc g)⟩)
        invFun := fun x => x.1.1 * x.2.1.1 * x.2.2.1
        left_inv := fun g => Subtype.ext (Units.ext (show cut a (mat g) * cut b (mat g) * cut c (mat g) = mat g by
          rw [cut_add_pk hab, cut_add_pk hdc, show a + b + c = 1 by ring]; simp [cut]))
        right_inv := fun ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩⟩ => by
          have p1' := mem_gInf_pk.1 hp; have q1' := mem_gAt_pk.1 hq; have r1' := mem_gOff_pk.1 hr
          refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
          · change pr_pk a h1 (p * q * r) = p
            rw [map_mul, map_mul, pr_eq_pk.2 p1', p1 hab q1', p1 hac r1', mul_one, mul_one]
          · change pr_pk b h2 (p * q * r) = q
            rw [map_mul, map_mul, pr_eq_pk.2 q1', p1 hba p1', p1 hbc r1', mul_one, one_mul]
          · change pr_pk c hc (p * q * r) = r
            rw [map_mul, map_mul, pr_eq_pk.2 r1', p1 hca p1', p1 hcb q1', one_mul, one_mul]
        map_mul' := fun _ _ => Prod.ext (Subtype.ext (map_mul _ _ _))
          (Prod.ext (Subtype.ext (map_mul _ _ _)) (Subtype.ext (map_mul _ _ _)))
        continuous_toFun := ((cont_pr_pk h1).subtype_mk _).prodMk
          (((cont_pr_pk h2).subtype_mk _).prodMk ((cont_pr_pk hc).subtype_mk _))
        continuous_invFun := ((continuous_subtypeVal.comp continuous_fst).mul
          (continuous_subtypeVal.comp (continuous_fst.comp continuous_snd))).mul
          (continuous_subtypeVal.comp (continuous_snd.comp continuous_snd)) }
    exact ⟨φ.symm, fun _ => rfl⟩
  refine ⟨hprod, (eK ▸ hKc).of_isClosed_subset cI hinfInt,
    by rw [show (gAt σ X S : Set (UA σ X.J)) = {g | (∑ v ∈ S, (Euler.idem v : AF F)) • (mat g - 1) = mat g - 1} from
         Set.ext fun _ => mem_gAt_pk]; exact closed_fix_pk h2,
    by rw [show (gOff σ X S : Set (UA σ X.J)) = {g | (1 - realAd F 1 - ∑ v ∈ S, (Euler.idem v : AF F)) • (mat g - 1) =
         mat g - 1} from Set.ext fun _ => mem_gOff_pk]; exact closed_fix_pk hc,
    eK ▸ hKc, by rw [← eK]; exact Subgroup.isOpen_of_mem_nhds K (g := 1) (by rw [eK]; exact Bad.int_nhds hX.lat),
    hinfInt,
    fun b hb => ⟨fun v => Euler.prj v b, fun v => Euler.prj_mem b,
      fun v _ => Euler.off_of (by rw [map_mul, map_inv, Euler.mem_loc.1 (Euler.prj_mem b), inv_mul_cancel]),
      fun H hH => by have := pr_sum_mem_pk H b S hH; rwa [pr_eq_pk.2 (mem_gAt_pk.1 hb)] at this⟩,
    fun g => ?_⟩
  have hFull : X.L.IsFullLattice E := by
    let := hX.lat
    refine { span_eq_top := by_contra fun hW => ?_ }
    let W := Submodule.span E (X.L : Set (Fin n → E))
    let g' : (Fin n → E) →ₗ[E] Module.Dual E W :=
      ((dotProductBilin E E).compl₂ (Matrix.mulVecLin X.Jᵀ)).domRestrict₂ W
    obtain ⟨z, hz, hz₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g')
      (by rw [Subspace.dual_finrank_eq]; exact Submodule.finrank_lt hW))
    let y : Fin n → E := fun i => σ (z i)
    have hy₀ : y ≠ 0 := fun hy => hz₀ (funext fun i => σ.injective ((congrFun hy i).trans (map_zero σ).symm))
    have hJ : X.Jᵀ.map σ = X.J := Matrix.ext hX.herm
    have hline (a : E) : a • y ∈ X.L := (hX.dual _).2 fun x hx => by
      have hz' : z ⬝ᵥ X.Jᵀ *ᵥ x = 0 :=
        congrArg (fun f : Module.Dual E W => f ⟨x, Submodule.subset_span hx⟩) (LinearMap.mem_ker.mp hz)
      have horth : form σ X.J y x = 0 := by
        have he := σ.toRingHom.map_dotProduct z (X.Jᵀ *ᵥ x); rw [hz', map_zero] at he
        have hm : σ.toRingHom ∘ (X.Jᵀ *ᵥ x) = X.J *ᵥ (fun i => σ (x i)) := funext fun i => by
          rw [Function.comp_apply, σ.toRingHom.map_mulVec]
          exact congrFun (congrArg (fun M => M *ᵥ (fun j => σ (x j))) hJ) i
        rw [hm] at he; exact he.symm
      have ha0 : form σ X.J (a • y) x = 0 := by
        dsimp only [form]; rw [smul_dotProduct, smul_eq_mul]; exact mul_eq_zero_of_right a horth
      rw [ha0]
      exact isIntegral_zero
    let i : E →ₗ[𝓞 E] X.L := ((LinearMap.toSpanSingleton E _ y).restrictScalars (𝓞 E)).codRestrict X.L hline
    let : Module.Finite (𝓞 E) X.L := Module.Finite.iff_fg.mpr hX.lat.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun _ _ hab =>
      smul_left_injective E hy₀ (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  exact (Filter.eventually_cofinite.1 ((Euler.ae_mulVec hFull (mat g)).and (Euler.ae_mulVec hFull (mat g⁻¹)))).subset
    fun _ hv h => hv fun z hz h3 => ⟨h.1 z hz h3, h.2 z hz h3⟩

private def triv_pk (σ : E →ₐ[F] E) {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (c : AF F) : Subgroup (UA σ J) where
  carrier := {g | c • (mat g - 1) = 0}
  one_mem' := by rw [Set.mem_ofPred_eq, show mat (1 : UA σ J) = 1 from rfl, sub_self, smul_zero]
  mul_mem' := fun {g h} hg hh => by
    rw [Set.mem_ofPred_eq] at *
    have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
      rw [show mat (g * h) = mat g * mat h from rfl]; noncomm_ring
    rw [e, smul_add, hh, add_zero, ← Matrix.smul_mul, hg, Matrix.zero_mul]
  inv_mem' := fun {g} hg => by
    rw [Set.mem_ofPred_eq] at *
    have h1 : mat g⁻¹ * mat g = 1 := show mat (g⁻¹ * g) = 1 by rw [inv_mul_cancel]; rfl
    have e : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by rw [mul_sub, h1]; noncomm_ring
    rw [e, smul_neg, ← Matrix.mul_smul, hg, Matrix.mul_zero, neg_zero]

private theorem evFin_aS_not_pk {S : Finset (Pl F)} {v : Pl F} (h : v ∉ S) : evFin F v (aS F S) = 0 := by
  have := congrArg (evFin F v) (idem_mul_aS h); rwa [map_mul, evFin_idem_self, one_mul, map_zero] at this

private theorem evFin_aS_pk {S : Finset (Pl F)} {v : Pl F} (h : v ∈ S) : evFin F v (aS F S) = 1 := by
  induction S using Finset.induction_on with
  | empty => exact absurd h (Finset.notMem_empty v)
  | insert u S hu ih =>
    rw [aS_insert hu, map_add (f := _)]
    rcases Finset.mem_insert.1 h with rfl | h'
    · rw [evFin_idem_self, evFin_aS_not_pk hu, add_zero]
    · rw [ih h', evFin_idem_ne (by rintro rfl; exact hu h'), zero_add]

private def cutG_pk {Y : Spc F E n} (c : AF F) (hc : c * c = c) : G2 σ Y →* G2 σ Y :=
  MonoidHom.mk' (fun g => ⟨⟨cut c (mat2 g), cut c (mat2 g⁻¹),
    by rw [cut_mul hc, show mat2 g * mat2 g⁻¹ = 1 from g.1.mul_inv]; exact cut_one,
    by rw [cut_mul hc, show mat2 g⁻¹ * mat2 g = 1 from g.1.inv_mul]; exact cut_one⟩, cut_form hc _ g.2⟩)
    fun _ _ => Subtype.ext (Units.ext (cut_mul hc _ _).symm)

private theorem cutG_mem_pk {Y : Spc F E n} {B : Base F E} {K : Subgroup (G2 σ Y)} (hK : IsStab2 B K) {c : AF F}
    (hc : c * c = c) (i1 : ∀ u, evFin F u c ∈ u.adicCompletionIntegers F)
    (i2 : ∀ u, evFin F u (1 - c) ∈ u.adicCompletionIntegers F) {k : G2 σ Y} (hk : k ∈ K) : cutG_pk c hc k ∈ K := by
  refine (hK _).2 ⟨fun w => ?_, fun z z' hz hz' k' hk' => ?_⟩
  · have e : (mat2 (cutG_pk c hc k)).map (piInf (B.emb w)) = piInf (B.emb w) (algebraMap _ _ (1 - c)) • 1 +
        piInf (B.emb w) (algebraMap _ _ c) • (mat2 k).map (piInf (B.emb w)) := Matrix.ext fun i j => by
      change piInf (B.emb w) (cut c (mat2 k) i j) = _
      rw [cut, Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.smul_apply,
        Matrix.smul_apply, map_add, Algebra.smul_def (1 - c), Algebra.smul_def c, map_mul, map_mul,
        Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [e]; exact ((Commute.one_left _).smul_left _).add_left ((((hK k).1 hk).1 w).smul_left _)
  · obtain ⟨k₁, rfl, h3⟩ : ∃ k₁, k' = cutG_pk c hc k₁ ∧ k₁ ∈ ({k, k⁻¹} : Set (G2 σ Y)) := by
      rcases hk' with rfl | rfl; exacts [⟨k, rfl, .inl rfl⟩, ⟨k⁻¹, (map_inv _ k).symm, .inr rfl⟩]
    obtain ⟨b1, b2⟩ := ((hK k).1 hk).2 z z' hz hz' k₁ h3
    rw [show mat2 (cutG_pk c hc k₁) = cut c (mat2 k₁) from rfl, cut, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec]
    exact ⟨add_mem (latHat_smul i2 hz) (latHat_smul i1 b1), add_mem (latHat_smul i2 hz') (latHat_smul i1 b2)⟩

theorem datum_k : Tools_k → Datum_k := by
  intro T F E _ _ _ _ _ σ B n d X W M χX χW om P hn K a e hK ha he ν hν S uW H φ hfin hbump hoff f₀ hf₀ n0
  have h0 : min n 0 = 0 := Nat.min_zero n
  obtain ⟨dd, om₂, S₂, l, d1, d2, d3, d4⟩ := T.dbl F E σ B n d X W M χX χW om n 0 d 0 P
  obtain ⟨c₀, c0, hc⟩ := d4 ν hν
  have c1 := Complex.ofReal_ne_zero.2 c0.ne'
  have hSB := hfin.1; have hs := (hfin.2.and P.good.std).mono fun _ h => h.1.trans h.2
  have hne : ∀ v, φ v ≠ 0 := fun v => by by_cases h : v ∈ S; exacts [(hbump v h).2.1, hoff v h ▸ (P.good.vac v).2.1]
  have m := GlobalTheory.TensUniq.pure_mem_schA f₀ φ hSB hs
  have m0 := GlobalTheory.EvNonzero.pure_ne_zero f₀ n0 φ hne hs
  have fx : ∀ v ∉ S, ∀ k ∈ K, At (evFin F v) (mat2 k - 1) → om₂ k (boxFun (pure f₀ φ) (star (pure f₀ φ))) = _ :=
    fun v h k hk h' => fix_box hSB hs (hoff v h ▸ T.vacFix F E σ B n d X W M n 0 d 0 P.base P.herm P.skew P.good χW
      P.hW dd om₂ d3 d1.weil K hK v (fun w hw => uW w (by show ¬ w.under (𝓞 F) ∈ (S : Set (Pl F)); rw [hw]; exact h))
      k hk h')
  have e1 := fun v R (c : ℂ) (h' : Acts (evFin F v) R (φ v) (c • φ v)) => eig (f := f₀) hSB hs h'
  generalize pure f₀ φ = Φ at *
  have hbox := (d2 Φ m Φ m).1
  have bx : ∀ g, om₂ (e (g, 1)) (boxFun Φ (star Φ)) = boxFun (om (g, 1) Φ) (star Φ) := fun g => by
    simpa [detInv, show ((1, 1) : UA σ X.J × UA σ W.J) = 1 from rfl] using ((d2 Φ m Φ m).2 1 g 1 _ (he g 1)).2
  have cf : ∀ g, l (om₂ (e (g, 1)) (boxFun Φ (star Φ))) = c₀ * coef om ν Φ g := fun g => by
    rw [bx, hc _ (P.weil.isUSplitting.pres _ _ m) _ m]; rfl
  have L := Bad.law_k P.base d1 hbox
  have hcomm : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {c : AF F} {A B : Matrix ι ι (AE F E)},
      c • (A - 1) = A - 1 → c • (B - 1) = 0 → A * B = B * A := by
    intro _ _ _ _ A B h1 h2
    have a1 : (A - 1) * (B - 1) = 0 := by rw [← h1, Matrix.smul_mul, ← Matrix.mul_smul, h2, Matrix.mul_zero]
    have a2 : (B - 1) * (A - 1) = 0 := by rw [← h1, Matrix.mul_smul, ← Matrix.smul_mul, h2, Matrix.zero_mul]
    exact sub_eq_zero.1 (by
      rw [show A * B - B * A = (A - 1) * (B - 1) - (B - 1) * (A - 1) by noncomm_ring, a1, a2, sub_zero])
  have h1s : ∀ {ι : Type} [DecidableEq ι] {A : Matrix ι ι (AE F E)} {c : AF F}, c • (A - 1) = 0 →
      (1 - c) • (A - 1) = A - 1 := fun h => by rw [sub_smul, one_smul, h, sub_zero]
  have hOffL : gOff σ X S ≤ triv_pk σ X.J (aS F S) := (Subgroup.closure_le _).2 fun g ⟨h1, h2⟩ =>
    Matrix.ext fun i j => GlobalTheory.SWOpFin.tens_eq_zero_of_comp
      (fun v => by
        rw [Matrix.smul_apply, GlobalTheory.AwayFix.Chart.compFin_smul_away]
        by_cases hv : v ∈ S
        · have := congrFun₂ (h2 v hv) i j; rw [Matrix.map_apply] at this
          simp [this, Matrix.one_apply, apply_ite (compFin F E v)]
        · rw [evFin_aS_not_pk hv, zero_smul])
      (fun w => by
        rw [Matrix.smul_apply, GlobalTheory.AwayFix.Chart.compInf_smul_away]
        have := congrFun₂ (h1 w) i j; rw [Matrix.map_apply] at this
        simp [this, Matrix.one_apply, apply_ite (compInf F E w)])
  have hEvI : ∀ S' : Finset (Pl F), evI F (aS F S') = 1 := fun S' => by
    induction S' using Finset.induction_on with
    | empty => rw [aS, Finset.sum_empty, add_zero, evI_real]
    | insert v T hv ih => rw [aS_insert hv, evI_add, evI_idem, ih, zero_add]
  have hInfL : gInf σ X ≤ triv_pk σ X.J (1 - aS F S) :=
    (Subgroup.closure_le _).2 fun _ hg => hg _ (by rw [evI_sub, evI_one, hEvI S, sub_self])
  have hEmbT : ∀ {c : AF F} {g : UA σ X.J}, g ∈ triv_pk σ X.J c → c • (mat2 (e (g, 1)) - 1) = 0 := fun h => by
    rw [he _ 1, show mat (1 : UA σ X.J) = 1 from rfl, ← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg,
      Matrix.fromBlocks_add, Matrix.fromBlocks_smul, ← sub_eq_add_neg, h]; simp
  have fk : ∀ k ∈ K, aS F S • (mat2 k - 1) = 0 → om₂ k (boxFun Φ (star Φ)) = boxFun Φ (star Φ) := fun k hk h => by
    have step : ∀ T : Finset (Pl F), om₂ (cutG_pk (aS F (S ∪ T)) (aS_mul_self _) k) (boxFun Φ (star Φ)) =
        boxFun Φ (star Φ) := fun T => by
      induction T using Finset.induction_on with
      | empty =>
        rw [show cutG_pk (aS F (S ∪ ∅)) (aS_mul_self _) k = 1 from Subtype.ext (Units.ext (sub_eq_zero.1
          ((cut_sub _).trans (by rw [Finset.union_empty]; exact h)))), map_one]; rfl
      | insert v T _ ih =>
        by_cases hm : v ∈ S ∪ T
        · simpa only [Finset.union_insert, Finset.insert_eq_self.2 hm] using ih
        have e' : cutG_pk (aS F (S ∪ insert v T)) (aS_mul_self _) k =
            cutG_pk (idem F v) (idem_mul_self v) k * cutG_pk (aS F (S ∪ T)) (aS_mul_self _) k :=
              Subtype.ext (Units.ext (by
          change cut (aS F (S ∪ insert v T)) (mat2 k) = cut (idem F v) (mat2 k) * cut (aS F (S ∪ T)) (mat2 k)
          rw [Finset.union_insert, aS_insert hm, cut_add_pk (idem_mul_aS hm)]))
        have i2 : ∀ u, evFin F u (1 - idem F v) ∈ u.adicCompletionIntegers F := fun u => by
          rw [map_sub, map_one]; exact sub_mem (one_mem _) (idem_int v u)
        rw [e', map_mul, mul_apply_eq_comp, ih, fx v (fun h' => hm (Finset.mem_union_left _ h')) _
          (cutG_mem_pk hK _ (idem_int v) i2 hk)]
        change At (evFin F v) (cut (idem F v) (mat2 k) - 1); rw [cut_sub]; exact at_idem v _
    have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
    have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
    have t1 : ∀ A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E),
        Tendsto (fun T : Finset (Pl F) => cut (aS F (S ∪ T)) A) atTop (𝓝 A) := fun A => by
      have c : Continuous fun x : AF F => cut x A := by
        unfold cut; refine continuous_matrix fun i j => ?_; simp only [Matrix.add_apply, Matrix.smul_apply]; fun_prop
      have t0 : Tendsto (fun T : Finset (Pl F) => aS F (S ∪ T)) atTop (𝓝 1) :=
        tendsto_aS.comp (tendsto_atTop_mono (fun _ => Finset.subset_union_right) tendsto_id)
      have h1 := (c.tendsto 1).comp t0
      rwa [show cut (1 : AF F) A = A by simp [cut]] at h1
    have tk : Tendsto (fun T : Finset (Pl F) => cutG_pk (aS F (S ∪ T)) (aS_mul_self _) k) atTop (𝓝 k) :=
      tendsto_subtype_rng.2 (Units.isEmbedding_embedProduct.tendsto_nhds_iff.2
        ((t1 (mat2 k)).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp (t1 (mat2 k⁻¹)))))
    exact funext fun x => tendsto_nhds_unique (((d1.weil.2.1.cont _ (ev_adm x) _ hbox).tendsto k).comp tk)
      (tendsto_const_nhds.congr fun T => (congrFun (step T) x).symm)
  have key : ∀ c ∈ gOff σ X S, ∀ p t k, IsPar p t → k ∈ K → aS F S • (mat2 k - 1) = 0 → e (c, 1) = p * k →
      ∀ y ∈ triv_pk σ X.J (1 - aS F S), coef om ν Φ (y * c) = (χW (Matrix.GeneralLinearGroup.det t) : ℂ) *
        ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ ((d : ℂ) / 2) * coef om ν Φ y :=
      fun c hc' p t k hp hk hk0 hx y hy => by
    have cm : y * c = c * y := Subtype.ext (Units.ext (hcomm (h1s (hOffL hc')) hy).symm)
    have ck : k * e (y, 1) = e (y, 1) * k := Subtype.ext (Units.ext (hcomm (h1s hk0) (hEmbT hy)))
    have e2 : e (y * c, 1) = p * (e (y, 1) * k) := by
      rw [cm, show ((c * y, 1) : UA σ X.J × UA σ X.J) = (c, 1) * (y, 1) by simp, map_mul, hx, mul_assoc, ck]
    refine mul_left_cancel₀ c1 ?_; rw [mul_left_comm, ← cf, ← cf, e2]
    have := L p t (e (y, 1) * k) hp; beta_reduce at this
    rw [this, map_mul, mul_apply_eq_comp, fk k hk hk0]
  let stG : Subgroup (UA σ X.J) :=
    { carrier := {g | om (g, 1) Φ = Φ}
      one_mem' := by rw [Set.mem_ofPred_eq, show ((1, 1) : UA σ X.J × UA σ W.J) = 1 from rfl, map_one]; rfl
      mul_mem' := fun {g h} hg hh => by
        rw [Set.mem_ofPred_eq] at *
        rw [show ((g * h, 1) : UA σ X.J × UA σ W.J) = (g, 1) * (h, 1) by simp, map_mul, mul_apply_eq_comp, hh, hg]
      inv_mem' := fun {g} hg => by
        rw [Set.mem_ofPred_eq] at *; conv_lhs => rw [← hg]
        rw [← mul_apply_eq_comp, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, mul_one,
          show ((1, 1) : UA σ X.J × UA σ W.J) = 1 from rfl, map_one]; rfl }
  have st : ⨆ v ∈ S, H v ≤ stG :=
    iSup₂_le fun v hv g hg => (e1 v _ 1 (by rw [one_smul]; exact (hbump v hv).2.2.2.2.2.1 g hg)).trans (one_smul _ _)
  have hH : ⨆ v ∈ S, H v ≤ triv_pk σ X.J (1 - aS F S) := iSup₂_le fun v hv =>
    (hbump v hv).2.2.1.trans ((Subgroup.closure_le _).2 fun _ hg => hg _ (by
      rw [map_sub, map_one, evFin_aS_pk hv, sub_self]))
  refine ⟨by rw [coef, show ((1, 1) : UA σ X.J × UA σ W.J) = 1 from rfl, map_one]; exact sq_ne ν hν m m0,
    fun x hx b hb c hc' => ⟨fun hbn => ?_, ?_⟩⟩
  · obtain ⟨-, -, -, -, -, -, -, hdec, -⟩ := decomp_k T F E σ B n X P.base P.herm S
    obtain ⟨q, q1, q2, q3⟩ := hdec b hb
    obtain ⟨v, hv, hq⟩ : ∃ v ∈ S, q v ∉ ⨆ v ∈ S, H v := by by_contra hh; push Not at hh; exact hbn (q3 _ hh)
    obtain ⟨u, z, z', hu, hz, r1, r2⟩ := (hbump v hv).2.2.2.2.2.2 (q v) (q1 v)
      fun h => hq (Subgroup.mem_iSup_of_mem v (Subgroup.mem_iSup_of_mem hv h))
    have tmul : ∀ {y : UA σ X.J}, y ∈ triv_pk σ X.J (idem F v) → ∀ {u' : Matrix (Fin n) (Fin d) (AE F E)},
        At (evFin F v) u' → mat y * u' = u' := fun {y} hy {u'} hu' => by
      have : (mat y - 1) * u' = 0 := by
        rw [← idem_smul hu', Matrix.mul_smul, ← Matrix.smul_mul, show idem F v • (mat y - 1) = 0 from hy,
          Matrix.zero_mul]
      rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
    have hm : mat (x * b * c) * u = mat (q v) * u := by
      have a1 : At (evFin F v) (mat (q v) * u) := fun t ht => by rw [← Matrix.mul_smul, hu t ht, Matrix.mul_zero]
      have a2 : gInf σ X ≤ triv_pk σ X.J (idem F v) := (Subgroup.closure_le _).2 fun _ hg => hg _ (evI_idem v)
      have a3 : (q v)⁻¹ * b ∈ triv_pk σ X.J (idem F v) := smul_off_pk (q2 v hv)
      have a4 : c ∈ triv_pk σ X.J (idem F v) := by
        have ei : idem F v = idem F v * aS F S := af_ext' (by rw [evI_mul, evI_idem, zero_mul]) fun w => by
          rw [map_mul]
          by_cases hw : w = v
          · rw [hw, evFin_aS_pk hv, mul_one]
          · rw [evFin_idem_ne hw, zero_mul]
        show idem F v • (mat c - 1) = 0; rw [ei, mul_smul, hOffL hc', smul_zero]
      have a5 : mat (x * b * c) = mat x * mat (q v) * mat ((q v)⁻¹ * b) * mat c := by
        rw [show x * b * c = x * q v * ((q v)⁻¹ * b) * c by group]; rfl
      rw [a5, Matrix.mul_assoc, tmul a4 hu, Matrix.mul_assoc, tmul a3 hu, Matrix.mul_assoc, tmul (a2 hx) a1]
    exact Bad.orth_k P hν m m0 hz (e1 v _ _ r1) (e1 v _ _ (by rwa [hm]))
  · have intS : ∀ u, evFin F u (aS F S) ∈ u.adicCompletionIntegers F := fun u => by
      by_cases h : u ∈ S
      · rw [evFin_aS_pk h]; exact one_mem _
      · rw [evFin_aS_not_pk h]; exact zero_mem _
    have i1 : ∀ u, evFin F u (1 - aS F S) ∈ u.adicCompletionIntegers F := fun u => by
      rw [map_sub, map_one]; exact sub_mem (one_mem _) (intS u)
    have i2 : ∀ u, evFin F u (1 - (1 - aS F S)) ∈ u.adicCompletionIntegers F := fun u => by
      rw [sub_sub_cancel]; exact intS u
    have hc0 := hEmbT (hOffL hc')
    obtain ⟨p, t, k, hp, hk, hk0, hx', ht⟩ : ∃ p t k, IsPar p t ∧ k ∈ K ∧ aS F S • (mat2 k - 1) = 0 ∧ e (c, 1) = p * k ∧
        (IntAll c → t = 1) := by
      by_cases hI : IntAll c
      · exact ⟨1, 1, e (c, 1), par_one, Bad.emb_mem_k P.base P.herm h0 hK he hI, hc0, (one_mul _).symm, fun _ => rfl⟩
      · have hid : (1 - aS F S) * (1 - aS F S) = 1 - aS F S := by linear_combination aS_mul_self S
        obtain ⟨p, t, hp, k, hk, hx'⟩ := ha.iwa (e (c, 1))
        refine ⟨cutG_pk (1 - aS F S) hid p, ⟨cut (1 - aS F S) t.1, cut (1 - aS F S) (t⁻¹).1,
            by rw [cut_mul hid, t.mul_inv]; exact cut_one, by rw [cut_mul hid, t.inv_mul]; exact cut_one⟩,
          cutG_pk (1 - aS F S) hid k, ?_, cutG_mem_pk hK hid i1 i2 hk, ?_, ?_, fun h => absurd h hI⟩
        · rw [isPar_iff] at hp ⊢; change cut (1 - aS F S) (mat2 p) * _ = _ * cut (1 - aS F S) t.1
          rw [cut, cut, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
            Matrix.mul_smul, hp, Matrix.one_mul, Matrix.mul_one]
        · have hk' : (1 - aS F S) • (mat2 (cutG_pk (1 - aS F S) hid k) - 1) = mat2 (cutG_pk (1 - aS F S) hid k) - 1 :=
            by
            change (1 - aS F S) • (cut (1 - aS F S) (mat2 k) - 1) = _
            rw [cut_sub, smul_smul, hid]; exact (cut_sub _).symm
          rwa [sub_smul, one_smul, sub_eq_self] at hk'
        · rw [← map_mul, ← hx']; exact Subtype.ext (Units.ext (cut_eq.2 (h1s hc0)).symm)
    refine ⟨(χW (Matrix.GeneralLinearGroup.det t) : ℂ) * ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^
        ((d : ℂ) / 2),
      by rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (_root_.GlobalTheory.ThK.Dbl.absE_pos _), hx',
           ha.val p t hp k hk]; simp,
      fun h => by simp [ht h],
      fun x' hx'' b' hb' => by
        rw [key c hc' p t k hp hk hk0 hx' _ (mul_mem (hInfL hx'') (hH hb')), coef, coef,
          show ((x' * b', 1) : UA σ X.J × UA σ W.J) = (x', 1) * (b', 1) by simp, map_mul, mul_apply_eq_comp, st hb']⟩
end UpperTheory.TP
end

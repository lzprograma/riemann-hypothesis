module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqOneOfTrivialFinitePartOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterPowEqOneFiniteIdelesOfOrderDvdStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSecCharVal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PowClassNumberIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePoints
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeEmbeddingLiftDatumHermitianSpace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMemberDictionaryContextGoodEmbedding
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisationDictionaryCharacterLaws

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct

namespace GlobalTheory.OneCover

open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV GlobalTheory.TupleCover

variable {D : D7}



theorem exists_fun_cover {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {n r : ℕ} (d : DeltaDat Xo c n) (V : HSp D) (hr : V.rank = r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hio : IotaOK Dw V ι) (hpos : 1 ≤ Dw.p + Dw.q)
    (hx₀ : ∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 →
      gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) =
        Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ))
    (hA : d.l₂.A = 1) :
    ∃ (U₂ : Unf d.Xo₂ d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) r) (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r),
      IsUnf U₂ ∧ (∀ k, ModelW V hr (U₂.X k)) ∧
      ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
        (F : FamilyUnif d.Xo₂ (((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)).comp
            (IntermediateField.inclusion d.c₂.le).toRingHom)
          (fun j => relab d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) (e j).1))
        (ik : U₂.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U₂.X k).Λ)
        (th : ∀ k, (U₂.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
        (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictLat U₂ V hr dict₂ ι e F ik φ th x₀ ∧
        ∀ (_ : d.IsLev) (_ : FnAlgClosed (Xo := d.Xo₂) (c := d.c₂)) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
          (_ : ∀ g : GA D V, (∃ w ∈ intAE D, ((Matrix.GeneralLinearGroup.det (finHom V g) :
            (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = d.l₂.M • w) →
            xi (Matrix.GeneralLinearGroup.det (finHom V g)) = 1)
          (_ : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1)
          (m : ℕ) (_ : 0 < m) (_ : ∀ g : GA D V, xi (Matrix.GeneralLinearGroup.det (finHom V g)) ^ m = 1)
          (_ : zeta m ∈ c.F),
          ∃ f : Rul d.Xo₂ d.c₂, ({ d with cδ := f } : DeltaDat Xo c n).IsLev ∧ f ^ m = 1 ∧
            ∀ h γ : GA D V, MarkBy U₂ V hr dict₂ ι F ik φ h γ →
              rdU U₂ f (dict₂ h).1 (dict₂ h).2 =
                1 * ((xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) : ℂ) := by
  obtain ⟨U₂, dict₂, u1, u2, g, e, F, ik, φ, th, v1, v2, v3⟩ :=
    exists_fun_cover_of_val d V hr ι x₀ hio hpos hx₀ hA
  exact ⟨U₂, dict₂, u1, u2, g, e, F, ik, φ, th, v1, v2, fun hlev hcl xi h1 h2 m hm h3 hz =>
    v3 hlev hcl xi h1 h2 m hm h3 fun h =>
      GlobalTheory.NormOneChar.mem_of_pow_eq_one hm hz (by rw [← Units.val_pow_eq_pow_val, h3 h, Units.val_one])⟩

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem halfIs_of_eq {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {t t' : T0}
    (e : R.Q t' = R.Q t) {Mb I : Ideal (𝓞 D.host.E)} (h : HalfIs R t' Mb I) : HalfIs R t Mb I := by
  unfold HalfIs at h ⊢
  rwa [e] at h

theorem xi_pow_eq_one (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (h : ChrEq c χ) (n : ℕ)
    (ho : χ.OrderDvd n) (x : (AE D)ˣ) : c x ^ n = 1 :=
  GlobalTheory.T.heckeChar_eq_one_of_trivial_finitePartOne D (c ^ n) ⟨h.1.1.pow n, fun x => by
    rw [MonoidHom.pow_apply, h.1.2, one_pow]⟩ (GlobalTheory.T.idelicCharacter_pow_eq_one_finiteIdeles_of_orderDvd D c χ h n ho) x

def CoversRep (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (n : ℕ)
    (pd : T0 → ℕ) (I : T0 → Ideal (𝓞 D.host.E)) (l₂ : T0 → Level T.Q.H) (rep : T0 → T0) (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F) : Prop :=
  ∃ (d : T0 → DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n)
    (U : ∀ t, Unf (d t).Xo₂ (d t).c₂ ((inC c').comp ((d t).eF.symm : (d t).c₂.F →+* c'.F)) D.R.r)
    (dict : ∀ t, GA D (Wc D i) → Σ k, Frame ((U t).X k).Ψ D.R.r)
    (f : ∀ t, Rul (d (rep t)).Xo₂ (d (rep t)).c₂)
    (xi : T0 → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ),
    (∀ t, (d t).pd = pd t ∧ (d t).I = I t ∧ (d t).l₂ = l₂ t) ∧
    CovPin (T.Q.Xo ((i : ℕ) + 1)) c' (fun t => ({ d (rep t) with cδ := f t } : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n)) ∧
    (∀ t, HalfIs R t T.Q.l.Mb (d (rep t)).I) ∧
    (∀ t, XiIs R i t (xi t)) ∧
    CXiVal (Wc D i) (rank_Wc i) (inC c') (fun t => ({ d (rep t) with cδ := f t } : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n))
      (fun t => U (rep t)) (fun t => dict (rep t)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) (sOv T.toCore c' hle)) xi ∧
    (∀ t k, ModelW (Wc D i) (rank_Wc i) ((U (rep t)).X k))



theorem exists_covers_rep (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) {μ0 : T0} [Finite T0]
    (hT : LawsJ T) (hL : R.toLevCh.Is μ0) (i : Fin D.R.m) (n : ℕ)
    (pd : T0 → ℕ) (I : T0 → Ideal (𝓞 D.host.E)) (l₂ : T0 → Level T.Q.H)
    (hl : ∀ t, IsCoverLevel T.Q.l (pd t) (I t) (l₂ t)) (hH : ∀ t, HalfIs R t T.Q.l.Mb (I t))
    (rep : T0 → T0) (hrep : ∀ t, R.Q (rep t) = R.Q t) :
    ∃ c₁ : Coeff T.Q.l, T.Q.c.F ≤ c₁.F ∧ D.what₂.embLL.toRatAlgHom.fieldRange ≤ c₁.F ∧
      (∀ t x, ((R.xi t x : Circle) : ℂ) ∈ c₁.F) ∧
      ∀ (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F), c₁.F ≤ c'.F → CoversRep T R i n pd I l₂ rep c' hle := by
  obtain ⟨c₁, hc1, hc2, hxi, hcov⟩ := exists_covers_rep_core T R hT hL i n pd I l₂ hl hH rep hrep
  refine ⟨c₁, hc1, hc2, hxi, fun c' hle hc' => ?_⟩
  obtain ⟨d, U, dict, f, xi, h1, h2, h3, h4, h5, h6, -⟩ := hcov c' hle hc'
  exact ⟨d, U, dict, f, xi, h1, h2, h3, h4, h5, h6⟩

end GlobalTheory.OneCover

module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.DegreeFormula.FlagDegFormula
public import Mathlib.RingTheory.WittVector.Isocrystal

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology MvPolynomial Finset

namespace Formalism.BasicNotions.DV

open Formalism.BasicNotions Formalism.DegreeFormula

structure Geo (F : Type) [Field F] [NumberField F] [StarRing F] where

  Var : Type

  dim : Var → ℕ

  Fn : Var → Type
  [fnField : ∀ Y, Field (Fn Y)]
  [fnAlg : ∀ Y, Algebra F (Fn Y)]

  Dv : Var → Type
  [dvGrp : ∀ Y, AddCommGroup (Dv Y)]

  H0 : ∀ Y, Dv Y → Submodule F (Fn Y)

  Cl : Var → Type

  supp : ∀ Y, Dv Y → Cl Y

  inter : ∀ Y, (Fin (dim Y) → Dv Y) → ℤ

  vanishOn : ∀ Y, Dv Y → Fn Y → Cl Y → Prop

  Adl : Var → Type

  ofW : ∀ Y (L : Dv Y) (W : HLat F), (W.V →ₗ[F] Fn Y) → Adl Y

  twist : ∀ Y, Adl Y → (InfinitePlace F → ℝ) → (HeightOneSpectrum (𝓞 F) → ℝ) → Adl Y

  arTop : ∀ Y, Adl Y → ℝ

  arVol : ∀ Y, Adl Y → ℝ

  nefA : ∀ Y, Adl Y → Prop

attribute [instance] Geo.fnField Geo.fnAlg Geo.dvGrp

section Poly
variable (Tau : Type) [Fintype Tau] (N : ℕ)

abbrev Rt : Type := Tau × Fin N

abbrev Vm : Type := (Bool × Rt Tau N) ⊕ (Bool × ℕ)

def tagHT : MvPolynomial (Rt Tau N) ℝ →ₐ[ℝ] MvPolynomial (Vm Tau N) ℝ :=
  rename (fun x => Sum.inl (true, x))

def tagDR : MvPolynomial (Rt Tau N) ℝ →ₐ[ℝ] MvPolynomial (Vm Tau N) ℝ :=
  rename (fun x => Sum.inl (false, x))

end Poly

structure ShimX (Tau : Type) [Fintype Tau] where

  N : ℕ

  j : ℕ
  j_pos : 1 ≤ j
  j_lt : j < N

  lev : Finset ℕ
  lev_prime : ∀ p ∈ lev, p.Prime

  Comp : Type
  [compFin : Fintype Comp]
  [compNe : Nonempty Comp]

  vol : ℝ

  chern : MvPolynomial (Rt Tau N) ℝ →ₗ[ℝ] ℝ

  chern_homog : ∀ (P : MvPolynomial (Rt Tau N) ℝ) (d : ℕ), d ≠ dimFl Tau N → P.IsHomogeneous d →
    chern P = 0

  arDeg : Finset ℕ → ℝ → MvPolynomial (Rt Tau N) ℝ →ₗ[ℝ] ℝ
  arDeg_homog : ∀ S R (P : MvPolynomial (Rt Tau N) ℝ) (d : ℕ), d ≠ dimFl Tau N + 1 →
    P.IsHomogeneous d → arDeg S R P = 0

  arMix : Finset ℕ → ℝ → ℕ → MvPolynomial (Vm Tau N) ℝ →ₗ[ℝ] ℝ
  arMix_HT : ∀ S R p (P : MvPolynomial (Rt Tau N) ℝ),
    arMix S R p (tagHT Tau N P) = arDeg (insert p S) R P
  arMix_DR : ∀ S R p (P : MvPolynomial (Rt Tau N) ℝ),
    arMix S R p (tagDR Tau N P) = arDeg (S.erase p) R P

  CurveHT : ℕ → Type
  degHT : ∀ p, CurveHT p → Rt Tau N → ℝ

  CurveDR : ℕ → Type
  degDR : ∀ p, CurveDR p → Rt Tau N → ℝ

  FibComp : ℕ → Type
  fibInBd : ∀ p, FibComp p → Prop

  Pt : Type

  phiDR : ℕ → Pt → Rt Tau N → ℝ

  phiMod : ℕ → Pt → Rt Tau N → ℝ

  phiFr : ℕ → Pt → Rt Tau N → ℝ

  XC : Type
  rfn : XC → ℝ
  rfn_ge : ∀ z, Real.exp 1 ≤ rfn z
  hLo : XC → ℝ
  hUp : XC → ℝ
  hLo_le : ∀ z, 0 < hLo z ∧ hLo z ≤ hUp z
  connN : XC → ℝ
  curvN : XC → ℝ
  compOf : XC → Comp

  normDetInf : Tau → XC → ℝ

  compPt : Pt → Comp

  normDetT : ℕ → Tau → Pt → ℝ

  normDetH : ℕ → Tau → Pt → ℝ

  htDetT : ℝ → Comp → Tau → ℝ

  ALB : Type
  arSelf : ALB → ℝ
  arSelfC : ALB → Comp → ℝ
  arSelf_sum : ∀ L, arSelf L = ∑ c, arSelfC L c
  geo : ALB → ℝ
  geoC : ALB → Comp → ℝ
  geo_sum : ∀ L, geo L = ∑ c, geoC L c
  arVol : ALB → ℝ
  semipos : ALB → Prop
  nefFib : ALB → Prop
  arNef : ALB → Prop

  Mbar : ℝ → (Tau → Fin N → ℝ) → ℚ → ALB

attribute [instance] ShimX.compFin ShimX.compNe

end Formalism.BasicNotions.DV

namespace Formalism.BasicNotions

open Formalism.BasicNotions.DV

namespace DV

abbrev KW (p : ℕ) [Fact p.Prime] : Type :=
  FractionRing (WittVector p (AlgebraicClosure (ZMod p)))

def sgF (p : ℕ) [Fact p.Prime] : KW p ≃+* KW p :=
  WittVector.FractionRing.frobenius p (AlgebraicClosure (ZMod p))

abbrev Emb (D : D7) (p : ℕ) [Fact p.Prime] : Type := D.host.E →+* KW p

def phiPow (D : D7) {p : ℕ} [Fact p.Prime] (n : ℕ) (τ : Emb D p) : Emb D p :=
  ((sgF p : KW p →+* KW p) ^ n).comp τ

def cEmb (D : D7) {p : ℕ} [Fact p.Prime] (τ : Emb D p) : Emb D p :=
  τ.comp (D.host.conj : D.host.E →+* D.host.E)

structure ITh where

  LB : Type

  Ch : Type
  [ring : CommRing Ch]
  [alg : Algebra ℚ Ch]

  c1 : LB → Ch

  VDiv : Type
  [grp : AddCommGroup VDiv]
  [modQ : Module ℚ VDiv]

  cD : VDiv →ₗ[ℚ] Ch

  capDeg : VDiv →ₗ[ℚ] Ch →ₗ[ℚ] ℚ

  divP : VDiv

  cD_divP : cD divP = 0

  dim : ℕ

attribute [instance] ITh.ring ITh.alg ITh.grp ITh.modQ

structure FPair (Z : ITh) (r : ℕ) where

  x : Fin r → Z.LB

  x' : Fin r → Z.LB

  Dv : Fin r → Z.VDiv

  hx : ∀ i, Z.c1 (x' i) = Z.c1 (x i) - Z.cD (Dv i)

def Gk (Z : ITh) (k : ℕ) (y y' : Z.Ch) : Z.Ch :=
  ∑ a ∈ Finset.range k, y ^ a * y' ^ (k - 1 - a)

def ck {Z : ITh} {r : ℕ} (P : FPair Z r) (k : ℕ) (Q : Z.Ch) : ℚ :=
  ∑ i, Z.capDeg (P.Dv i) (Gk Z k (Z.c1 (P.x i)) (Z.c1 (P.x' i)) * Q)

structure Mdl (D : D7) (p : ℕ) [Fact p.Prime] (N : ℕ) (rk : Emb D p → ℕ) where

  Z : ITh

  cov : ℕ
  cov_pos : 0 < cov

  lvl : ℕ

  lie : ∀ τ : Emb D p, FPair Z (rk τ)

  om : ∀ τ : Emb D p, FPair Z (N - rk τ)

  lieW : FPair Z (D.R.f * N)

  omW : FPair Z (D.R.f * N)

  om_dual : ∀ τ : Emb D p, ∃ e : Fin (N - rk τ) ≃ Fin (rk (cEmb D τ)),
    ∀ i, Z.c1 ((om τ).x i) = - Z.c1 ((lie (cEmb D τ)).x (e i))

  dim_eq : Z.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N + 1

  omW_dual : ∃ e : Fin (D.R.f * N) ≃ Fin (D.R.f * N),
    ∀ i, Z.c1 (omW.x i) = - Z.c1 (lieW.x (e i))

def rkOf {D : D7} {p : ℕ} [Fact p.Prime] (Ps : Set (Emb D p)) (N j : ℕ) (τ : Emb D p) : ℕ := by
  classical exact if τ ∈ Ps then j else N - j

section Glob
variable (D : D7)

abbrev EmbC : Type := D.what₂.Tau ⊕ D.what₂.Tau

open Classical in
def ofGG (g : D.R.GG) : EmbC D :=
  if h : g ∈ D.R.Psi then Sum.inl (D.eTau.symm ⟨g, h⟩)
  else if h' : g * D.R.cc ∈ D.R.Psi then
    Sum.inr (D.eTau.symm ⟨g * D.R.cc, h'⟩)
  else Sum.inl (D.eTau.symm 1)

def tauEmb (τ : D.what₂.Tau) : D.host.E →+* ℂ :=
  D.host.emb ((D.eTau τ : D.R.Psi) : D.R.GG)


open Classical in
def frobG (p : ℕ) : D.R.GG :=
  if h : ∃ g : D.R.GG, ∀ (P : Ideal (NumberField.RingOfIntegers D.host.E)) [P.IsPrime]
      [P.LiesOver (Ideal.span {(p : ℤ)})], IsArithFrobAt ℤ (D.host.sigmaOf g) P
  then h.choose else 1

variable (N : ℕ)

def pk (τ : D.what₂.Tau) (k : ℕ) : MvPolynomial (Rt D.what₂.Tau N) ℝ := ∑ i : Fin N, X (τ, i) ^ k

def chTot (k : ℕ) : MvPolynomial (Rt D.what₂.Tau N) ℝ :=
  C ((Nat.factorial k : ℝ)⁻¹) * ∑ τ : D.what₂.Tau, ∑ i : Fin N, (X (τ, i) ^ k + (-X (τ, i)) ^ k)

def collapse : MvPolynomial (Vm D.what₂.Tau N) ℝ →ₐ[ℝ] MvPolynomial (Rt D.what₂.Tau N) ℝ :=
  aeval (fun v => match v with
    | Sum.inl (_, x) => X x
    | Sum.inr (_, k) => chTot D N k)

variable {D N}

variable (D N)

end Glob

def PsiOf (D : D7) {p : ℕ} [Fact p.Prime] (jc : KW p →+* ℂ) : Set (Emb D p) :=
  {τ | ∃ τ0 : D.what₂.Tau, jc.comp τ = tauEmb D τ0}

end DV

def DV.kapW (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : Fin D.R.r) : ℤ :=
  if h : i.1 < (D.R.sigW j).1 then D.what₂.kaBig j τ ⟨i.1, h⟩ + ((D.R.nV / 2 : ℕ) : ℤ)
  else if h' : i.1 - (D.R.sigW j).1 < (D.R.sigW j).2 then
    D.what₂.kaSmall j τ ⟨i.1 - (D.R.sigW j).1, h'⟩ - ((D.R.nV / 2 : ℕ) : ℤ)
  else 0

def DV.UnramE (D : D7) (p : ℕ) : Prop :=
  ¬ p ∣ (NumberField.discr D.host.E).natAbs

structure DivX (D : D7) : Type 1 where

  geo : DV.Geo D.what₂.LL

  Lev : Type
  levPr : Lev → Finset ℕ

  shv : letI := D.host.cmStar; HSpace D.host.E → Lev → DV.ShimX D.what₂.Tau


  PlP : ∀ (p : ℕ) [Fact p.Prime], Type
  [plpFin : ∀ (p : ℕ) [Fact p.Prime], Fintype (PlP p)]
  wtP : ∀ (p : ℕ) [Fact p.Prime], PlP p → ℝ

  plP : ∀ (p : ℕ) [Fact p.Prime], PlP p ≃ {w : D.what₂.places.Pl // D.what₂.places.resChar w = p}


  jC : ∀ (p : ℕ) [Fact p.Prime], PlP p → (DV.KW p →+* ℂ)

  Mp : letI := D.host.cmStar; ∀ (_S : HSpace D.host.E) (_κ : Lev) (p : ℕ) [Fact p.Prime], PlP p → Type

  vdd : ℕ → D.what₂.Tau → ℝ



  CurveM : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : Lev) (p : ℕ) [Fact p.Prime]
    (la : PlP p), Mp S κ p la → Type
  degM : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : Lev) (p : ℕ) [Fact p.Prime]
    (la : PlP p) (z : Mp S κ p la), CurveM S κ p la z → DV.Rt D.what₂.Tau (shv S κ).N → ℝ

  htMdl : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : Lev) (p : ℕ) [Fact p.Prime]
    (la : PlP p), Mp S κ p la
  htCurve : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : Lev) (p : ℕ) [Fact p.Prime],
    (shv S κ).CurveHT p ≃ Σ la : PlP p, CurveM S κ p la (htMdl S κ p la)

  MjH : ℕ → HLat D.what₂.LL
  MjH_good : ∀ j, (MjH j).Good

  jM : ∀ j, (MjH j).V →ₛₗ[D.what₂.embLL] D.what₂.Mj j
  jM_basis : ∀ j, LinearIndependent ℂ (fun i => jM j ((MjH j).b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jM j ((MjH j).b i))) = ⊤

  jM_lat : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ x, x ∈ (MjH j).L ↔ ∃ c : D.what₂.Mj j → 𝓞 D.what₂.LL,
    jM j x = ∑ v ∈ (D.what₂.MjLat j).gen, D.what₂.embLL ((c v : 𝓞 D.what₂.LL) : D.what₂.LL) • v

  MjLat_sub : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ x ∈ (D.what₂.MjLat j).gen, x ∈ Set.range (jM j)


  Qp : D.what₂.Tup → Finset ℕ

  degreeZero_partial_set_empty : Qp D.what₂.mu0 = ∅

  Qp_muAt : ∀ w, D.what₂.places.resChar w ∉ Qp (D.what₂.muAt w)


  QPl : D.what₂.Tup → Type

  qv : ∀ μ, QPl μ → ℕ




  Comp : ℕ → Type


  Yv : ∀ j, Comp j → geo.Var


  Lw : ∀ j c, (D.what₂.Tau → Fin D.R.r → ℤ) →+ geo.Dv (Yv j c)

  iMj : ∀ j c, (MjH j).V →ₗ[D.what₂.LL] geo.Fn (Yv j c)

  logLam : ℕ → D.what₂.FT → (D.what₂.LL →+* ℂ) → ℝ

  logLam_base : ∀ j σ, logLam j σ D.what₂.embLL = Real.log (D.what₂.lamP D.what₂.mu0 j σ)

  kapR : (D.what₂.LL →+* ℂ) → ℝ


  Surf : Type
  SurfFp : Type

attribute [instance] DivX.plpFin

def DV.HidaSetting (D : D7) (XD : DivX D) (S : letI := D.host.cmStar; HSpace D.host.E) (κ : XD.Lev) : Prop :=
  letI := D.host.cmStar
  2 ≤ S.rank ∧ S.SigOK ∧
  (∀ τ : D.what₂.Tau, S.sig (DV.tauEmb D τ) = ((XD.shv S κ).j, (XD.shv S κ).N - (XD.shv S κ).j)) ∧
  2 < D.R.f * ((XD.shv S κ).N - 1)

end Formalism.BasicNotions

end

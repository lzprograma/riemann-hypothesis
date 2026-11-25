module

public import Formalism.SharpRestriction.LevelLetterCocycles.TwGood

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions
open scoped ENNReal TensorProduct

namespace GlobalTheory.TwistChoice

structure SameGalois {D D' : D7} (N : NData D.R D.host D.what₂) (N' : NData D'.R D'.host D'.what₂) : Prop where
  R : D.R = D'.R
  host : HEq D.host D'.host
  loc : D.loc = D'.loc
  Om : HEq (@NData.Om _ _ _ N) (@NData.Om _ _ _ N')
  instOm : HEq (@NData.instOm _ _ _ N) (@NData.instOm _ _ _ N')
  algOm : HEq (@NData.algOm _ _ _ N) (@NData.algOm _ _ _ N')
  plOm : HEq (@NData.plOm _ _ _ N) (@NData.plOm _ _ _ N')
  PlG : HEq (@NData.PlG _ _ _ N) (@NData.PlG _ _ _ N')

structure TwistDataAgreeAcrossCoefficients {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    (X : NTw D.R D.host D.what₂ D.LL0 N) (X' : NTw D'.R D'.host D'.what₂ D'.LL0 N') : Prop where
  cc : HEq X.cc X'.cc
  Tw : HEq X.Tw X'.Tw
  l : HEq X.l X'.l
  O0 : HEq X.O0 X'.O0
  crO0 : HEq X.crO0 X'.crO0
  algO0 : HEq X.algO0 X'.algO0
  topO0 : HEq X.topO0 X'.topO0
  O : HEq X.O X'.O
  crO : HEq X.crO X'.crO
  algO : HEq X.algO X'.algO
  Ok : HEq X.Ok X'.Ok
  crOk : HEq X.crOk X'.crOk
  algOk : HEq X.algOk X'.algOk
  zk : HEq X.zk X'.zk
  pD : HEq X.pD X'.pD
  chi1 : HEq X.chi1 X'.chi1
  Sig : HEq X.Sig X'.Sig
  finSig : HEq X.finSig X'.finSig
  jS : HEq X.jS X'.jS
  side : HEq X.side X'.side
  rhoS : HEq X.rhoS X'.rhoS
  S0 : HEq X.S0 X'.S0
  hEig : HEq X.hEig X'.hEig
  abelian₂ : HEq X.abelian₂ X'.abelian₂
  sideL : HEq X.sideL X'.sideL
  RCG : HEq X.RCG X'.RCG
  grpRCG : HEq X.grpRCG X'.grpRCG
  finRCG : HEq X.finRCG X'.finRCG
  art : HEq X.art X'.art
  th : HEq X.th X'.th

structure SameForms {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    (Y : NExp D.R D.host D.what₂ D.LL0 N X) (Y' : NExp D'.R D'.host D'.what₂ D'.LL0 N' X') : Prop where
  Fm : HEq Y.Fm Y'.Fm
  acgFm : HEq Y.acgFm Y'.acgFm
  modFmK : HEq Y.modFmK Y'.modFmK
  modFmO : HEq Y.modFmO Y'.modFmO
  actG : HEq Y.actG Y'.actG
  U : HEq Y.U Y'.U
  psiU : HEq Y.psiU Y'.psiU
  eAlg : HEq Y.eAlg Y'.eAlg
  Dat : HEq Y.Dat Y'.Dat
  th : HEq Y.th Y'.th
  lev : HEq Y.lev Y'.lev
  thPsi : HEq Y.thPsi Y'.thPsi
  MtV : HEq Y.MtV Y'.MtV
  acgMt : HEq Y.acgMt Y'.acgMt
  modMtK : HEq Y.modMtK Y'.modMtK
  modMtO : HEq Y.modMtO Y'.modMtO
  MtLat : HEq Y.MtLat Y'.MtLat
  thP : HEq Y.thP Y'.thP
  hkF : HEq Y.hkF Y'.hkF



private abbrev G0gRaw (R : Ranks) (H : Host R) (PlG : Fin 2 → Type) : Type :=
  ∀ kv : (Σ k : Fin 2, PlG k), GL (Fin R.r) (ZMod (H.g kv.1))

private def eGRaw (R : Ranks) (H : Host R) (PlG : Fin 2 → Type)
    {Tw : Type} (O : Tw → Type) [∀ i, CommRing (O i)]
    (Fm : Tw → ℕ → Bool → Type) [∀ i j b, AddCommGroup (Fm i j b)]
    [∀ i j b, Module (FractionRing (O i)) (Fm i j b)]
    (actG : ∀ i j b, G0gRaw R H PlG →* (Fm i j b ≃ₗ[FractionRing (O i)] Fm i j b))
    (eAlg : ∀ i, Bool → MonoidAlgebra (FractionRing (O i)) (G0gRaw R H PlG))
    (i : Tw) (j : ℕ) (b : Bool) : Module.End (FractionRing (O i)) (Fm i j b) :=
  MonoidAlgebra.lift (FractionRing (O i)) (Module.End (FractionRing (O i)) (Fm i j b)) (G0gRaw R H PlG)
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (actG i j b)) (eAlg i b)

private def eORaw (R : Ranks) (H : Host R) (PlG : Fin 2 → Type)
    {Tw : Type} (O : Tw → Type) [∀ i, CommRing (O i)]
    (Fm : Tw → ℕ → Bool → Type) [∀ i j b, AddCommGroup (Fm i j b)]
    [∀ i j b, Module (FractionRing (O i)) (Fm i j b)] [∀ i j b, Module (O i) (Fm i j b)]
    [∀ i j b, IsScalarTower (O i) (FractionRing (O i)) (Fm i j b)]
    (actG : ∀ i j b, G0gRaw R H PlG →* (Fm i j b ≃ₗ[FractionRing (O i)] Fm i j b))
    (eAlg : ∀ i, Bool → MonoidAlgebra (FractionRing (O i)) (G0gRaw R H PlG))
    (i : Tw) (j : ℕ) (b : Bool) : Module.End (O i) (Fm i j b) :=
  (eGRaw R H PlG O Fm actG eAlg i j b).restrictScalars (O i)

private def Fm0Raw (R : Ranks) (H : Host R) (PlG : Fin 2 → Type)
    {Tw : Type} (O : Tw → Type) [∀ i, CommRing (O i)]
    (Fm : Tw → ℕ → Bool → Type) [∀ i j b, AddCommGroup (Fm i j b)]
    [∀ i j b, Module (FractionRing (O i)) (Fm i j b)]
    (actG : ∀ i j b, G0gRaw R H PlG →* (Fm i j b ≃ₗ[FractionRing (O i)] Fm i j b))
    (U : Subgroup (G0gRaw R H PlG))
    (psiU : ∀ i, Bool → U →* (FractionRing (O i))ˣ)
    (i : Tw) (j : ℕ) (b : Bool) : Submodule (FractionRing (O i)) (Fm i j b) :=
  ⨅ u : U, LinearMap.ker ((actG i j b u).toLinearMap -
    ((psiU i b u : (FractionRing (O i))ˣ) : FractionRing (O i)) • LinearMap.id)

private def V0Raw (R : Ranks) (H : Host R) (PlG : Fin 2 → Type)
    {Tw : Type} (O : Tw → Type) [∀ i, CommRing (O i)]
    (Fm : Tw → ℕ → Bool → Type) [∀ i j b, AddCommGroup (Fm i j b)]
    [∀ i j b, Module (FractionRing (O i)) (Fm i j b)]
    (actG : ∀ i j b, G0gRaw R H PlG →* (Fm i j b ≃ₗ[FractionRing (O i)] Fm i j b))
    (U : Subgroup (G0gRaw R H PlG))
    (psiU : ∀ i, Bool → U →* (FractionRing (O i))ˣ)
    (eAlg : ∀ i, Bool → MonoidAlgebra (FractionRing (O i)) (G0gRaw R H PlG))
    (i : Tw) (j : ℕ) (b : Bool) : Submodule (FractionRing (O i)) (Fm i j b) :=
  (Fm0Raw R H PlG O Fm actG U psiU i j b).map (eGRaw R H PlG O Fm actG eAlg i j b)

private def ThRaw {Tw : Type} (O : Tw → Type) [∀ i, CommRing (O i)]
    (Fm : Tw → ℕ → Bool → Type) [∀ i j b, AddCommGroup (Fm i j b)] [∀ i j b, Module (O i) (Fm i j b)]
    (Dat : Tw → ℕ → Bool → Type) (thF : ∀ i j b, Dat i j b → Fm i j b)
    (i : Tw) (j : ℕ) (b : Bool) (Sg : Set (Dat i j b)) : Submodule (O i) (Fm i j b) :=
  Submodule.span (O i) (thF i j b '' Sg)

private def goodTwRaw
    (R : Ranks) (H : Host R) (loc : LocTheory)
    (Om : Type) [Field Om] [Algebra H.E Om]
    (plOm : Formalism.GaloisCohomology.Places H.E Om) (PlG : Fin 2 → Type)
    (cc : Om ≃+* Om)
    (Tw : Type) (l : Tw → ℕ) [∀ i, Fact (l i).Prime]
    (O0 : Tw → Type) [∀ i, CommRing (O0 i)] [∀ i, Algebra ℤ_[l i] (O0 i)] [∀ i, TopologicalSpace (O0 i)]
    (O : Tw → Type) [∀ i, CommRing (O i)] [∀ i, IsDomain (O i)] [∀ i, IsDiscreteValuationRing (O i)]
    [∀ i, Algebra (O0 i) (O i)]
    (Ok : Tw → ℕ → Type) [∀ i k, CommRing (Ok i k)] [∀ i k, IsDomain (Ok i k)]
    [∀ i k, IsDiscreteValuationRing (Ok i k)] [∀ i k, Algebra (O i) (Ok i k)]
    (Ok_inj : ∀ i k, Function.Injective (algebraMap (O i) (Ok i k)))
    (zk : ∀ i k, (Ok i k)ˣ)
    (pD : Tw → Finset (HeightOneSpectrum (𝓞 H.E)))
    (chi1 : ∀ i, ℕ → Bool → (G H.E Om →* (O0 i)ˣ))
    (Sig : Tw → Type) [∀ i, Fintype (Sig i)]
    (jS : ∀ i, Sig i → ℕ) (side : ∀ i, Sig i → Bool)
    (rhoS : ∀ i, Sig i → (G H.E Om →* GL (Fin R.r) (O0 i)))
    (S0 : Tw → Finset (HeightOneSpectrum (𝓞 H.E)))
    (hEig : ∀ i, Sig i → ℕ → HeightOneSpectrum (𝓞 H.E) → O i)
    (ab : Tw → Type) (sideL : ∀ i, ab i → Bool)
    (RCG : Tw → Finset (HeightOneSpectrum (𝓞 H.E)) → Type)
    [∀ i Q, CommGroup (RCG i Q)] [∀ i Q, Fintype (RCG i Q)]
    (art : ∀ i Q, G H.E Om →* RCG i Q)
    (thX : ∀ i Q, ab i → RCG i Q → FractionRing (O i))
    (Fm : Tw → ℕ → Bool → Type) [∀ i j b, AddCommGroup (Fm i j b)]
    [∀ i j b, Module (FractionRing (O i)) (Fm i j b)] [∀ i j b, Module (O i) (Fm i j b)]
    [∀ i j b, IsScalarTower (O i) (FractionRing (O i)) (Fm i j b)]
    (actG : ∀ i j b, G0gRaw R H PlG →* (Fm i j b ≃ₗ[FractionRing (O i)] Fm i j b))
    (U : Subgroup (G0gRaw R H PlG)) (psiU : ∀ i, Bool → U →* (FractionRing (O i))ˣ)
    (eAlg : ∀ i, Bool → MonoidAlgebra (FractionRing (O i)) (G0gRaw R H PlG))
    (Dat : Tw → ℕ → Bool → Type) (thF : ∀ i j b, Dat i j b → Fm i j b)
    (lev : ∀ i j b, Dat i j b → Finset (PlE H))
    (thPsi : ∀ i j b k, Finset (PlE H) → (G H.E Om →* (Ok i k)ˣ) →
      Dat i j b → Set (Ok i k ⊗[O i] Fm i j b))
    (MtV : ∀ i, ℕ → Bool → ∀ k, Finset (PlE H) → (G H.E Om →* (Ok i k)ˣ) → Type)
    [∀ i j b k Q ψ, AddCommGroup (MtV i j b k Q ψ)]
    [∀ i j b k Q ψ, Module (Ok i k) (MtV i j b k Q ψ)]
    (MtLat : ∀ i j b k Q ψ, Submodule (Ok i k) (MtV i j b k Q ψ))
    (thP : ∀ i j b k Q ψ, MtV i j b k Q ψ →ₗ[Ok i k] (Ok i k ⊗[O i] Fm i j b))
    (hkF : ∀ i j b, ℕ → PlE H → Module.End (FractionRing (O i)) (Fm i j b))
    (br : ∀ (i : Tw) (v : HeightOneSpectrum (𝓞 H.E)), v ∈ placesOver H.E (l i) →
      LocBridge (l i) H.E Om (Dec (F := H.E) (plOm.1 v)) (O0 i))
    (Dat0 : ∀ i j b, Set (Dat i j b))
    (N0 : Tw → ℕ) (i : Tw) (eps' : ℝ)
    (S : ∀ (j : ℕ) (b : Bool), Finset (Dat i j b))
    (A Q : Finset (PlE H)) (k' : ℕ) (ψ' : RCG i Q →* (Ok i k')ˣ) : Prop :=
  open Classical in
  let levs := (Finset.Icc 1 R.m).biUnion fun j =>
    (Finset.univ : Finset Bool).biUnion fun b => (S j b).biUnion (lev i j b)
  let eO (j : ℕ) (b : Bool) := eORaw R H PlG O Fm actG eAlg i j b
  let V0 (j : ℕ) (b : Bool) := V0Raw R H PlG O Fm actG U psiU eAlg i j b
  let eTh (j : ℕ) (b : Bool) (Sg : Set (Dat i j b)) : Submodule (O i) (Fm i j b) :=
    (ThRaw O Fm Dat thF i j b Sg).map (eO j b)
  let eThPsi (j : ℕ) (b : Bool) (k : ℕ) (Q0 : Finset (PlE H)) (ψ : G H.E Om →* (Ok i k)ˣ)
      (Sg : Set (Dat i j b)) : Submodule (Ok i k) (Ok i k ⊗[O i] Fm i j b) :=
    (Submodule.span (Ok i k) (⋃ a ∈ Sg, thPsi i j b k Q0 ψ a)).map ((eO j b).baseChange (Ok i k))
  let eThPMt (j : ℕ) (b : Bool) (k : ℕ) (Q0 : Finset (PlE H)) (ψ : G H.E Om →* (Ok i k)ˣ) :
      Submodule (Ok i k) (Ok i k ⊗[O i] Fm i j b) :=
    ((MtLat i j b k Q0 ψ).map (thP i j b k Q0 ψ)).map ((eO j b).baseChange (Ok i k))
  let phiK (k : ℕ) : O0 i →+* Ok i k :=
    (algebraMap (O i) (Ok i k)).comp (algebraMap (O0 i) (O i))
  let goodS (s : Sig i) : Prop :=
    ∃ x : Fm i (jS i s) (side i s), x ≠ 0 ∧
      eGRaw R H PlG O Fm actG eAlg i (jS i s) (side i s) x = x ∧
      ∀ k P, 1 ≤ k → k ≤ R.r → IsSplitPl H P → P ∉ S0 i →
        hkF i (jS i s) (side i s) k P x =
          algebraMap (O i) (FractionRing (O i)) (hEig i s k P) • x
  let SigG : Finset (Sig i) := Finset.univ.filter goodS
  let Trep (s : Sig i) (k : ℕ) (ψ : G H.E Om →* (Ok i k)ˣ) :
      Representation (Ok i k) (G H.E Om) (Fin R.r → KmodO (Ok i k)) :=
    BlochKatoReduction.twRep (phiK k) (rhoS i s) (chi1 i (jS i s) (side i s)) ψ
  let Tgl (s : Sig i) : G H.E Om →* GL (Fin R.r) (O0 i) :=
    BlochKatoReduction.twGL (rhoS i s) (chi1 i (jS i s) (side i s))
  let bk (s : Sig i) (k : ℕ) (ψ : G H.E Om →* (Ok i k)ˣ) (v : HeightOneSpectrum (𝓞 H.E)) :
      Submodule (Ok i k) (H1 ((Trep s k ψ).comp (Dec (F := H.E) (plOm.1 v)).subtype)) :=
    if hv : v ∈ placesOver H.E (l i) then
      Submodule.span (Ok i k) {x | ∃ (z : Z1 ((Trep s k ψ).comp (Dec (F := H.E) (plOm.1 v)).subtype))
        (c : ↥(Loc.GK (br i v hv).Kw) → Fin R.r → ↥(br i v hv).LL.1)
        (y : ↥(Dec (F := H.E) (plOm.1 v)) → Fin R.r → FractionRing (Ok i k)),
        c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles ((loc (l i)).PD (br i v hv).Kw)
          ((br i v hv).rep ((Tgl s).comp (Dec (F := H.E) (plOm.1 v)).subtype)) ∧
        (∀ g a, (∃ n d : O0 i, (d ≠ 0 ∧ (br i v hv).toLL d * c ((br i v hv).e g) a = (br i v hv).toLL n) ∧
          algebraMap (Ok i k) (FractionRing (Ok i k)) (phiK k d) * y g a =
            algebraMap (Ok i k) (FractionRing (Ok i k)) (phiK k n))) ∧
        (∀ g a, (z : ↥(Dec (F := H.E) (plOm.1 v)) → Fin R.r → KmodO (Ok i k)) g a =
          Submodule.Quotient.mk (y g a)) ∧
        x = Submodule.Quotient.mk z}
    else ⊥
  let Spl : Set (HeightOneSpectrum (𝓞 H.E)) :=
    ((⋃ k, placesOver H.E (H.g k)) ∪ ↑(pD i)) \ placesOver H.E (l i)
  let sLen (s : Sig i) (k : ℕ) (Q0 : Finset (HeightOneSpectrum (𝓞 H.E)))
      (ψ : G H.E Om →* (Ok i k)ˣ) : ℝ≥0∞ :=
    BlochKatoReduction.Gen.lenN (Ok i k) (l i)
      (Formalism.GaloisCohomology.SelAll (Trep s k ψ) plOm
        (Formalism.GaloisCohomology.bkCond (Trep s k ψ) plOm (l i) (Spl ∪ ↑Q0) (bk s k ψ)))
  let kMap (k : ℕ) : FractionRing (O i) →+* FractionRing (Ok i k) :=
    IsFractionRing.lift (g := (algebraMap (Ok i k) (FractionRing (Ok i k))).comp (algebraMap (O i) (Ok i k)))
      ((IsFractionRing.injective (Ok i k) (FractionRing (Ok i k))).comp (Ok_inj i k))
  let thEval (Q0 : Finset (HeightOneSpectrum (𝓞 H.E))) (lam : ab i) (k : ℕ)
      (ψ : RCG i Q0 →* (Ok i k)ˣ) : FractionRing (Ok i k) :=
    ∑ δ, kMap k (thX i Q0 lam δ) *
      algebraMap (Ok i k) (FractionRing (Ok i k)) ((ψ δ : (Ok i k)ˣ) : Ok i k)
  let nu : ℕ := KStar.Tree.nuOf (l i) (cycZ (F := H.E) (Ω := Om) (l i)) (R.t * R.r)
  ((∀ P ∈ Q, IsSplitPl H P ∧ P.asIdeal.inertiaDeg ℤ = 1 ∧ eWL H.E P = 1) ∧
    Disjoint Q (S0 i ∪ (levs ∪ A)) ∧ 1 ≤ k' ∧
    IsOpen ((ψ'.comp (art i Q)).ker : Set (G H.E Om)) ∧
    AntiHom cc (ψ'.comp (art i Q)) ∧
    (∀ g, ψ'.comp (art i Q) g ∈ Subgroup.zpowers (zk i k')) ∧
    RamExactly (ψ'.comp (art i Q)) ↑Q ∧
    (∀ v ∈ placesOver H.E (l i), ∀ A' : ValuationSubring Om, IsPlaceOver A' v →
      ∀ σ ∈ Dec (F := H.E) A', (ψ'.comp (art i Q)) σ = 1)) ∧
  (∃ epsB : ℕ → Bool → ℝ, (∀ j b, 0 ≤ epsB j b) ∧
    ∑ j ∈ Finset.Icc 1 R.m, ∑ b : Bool, epsB j b ≤ eps' ∧
    ∀ j ∈ Finset.Icc 1 R.m, ∀ b : Bool,
      ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra (Ok i k') O']
        [Algebra (O i) O'] [IsScalarTower (O i) (Ok i k') O'],
        Function.Injective (algebraMap (Ok i k') O') → Module.Finite (Ok i k') O' →
        ∀ M : Submodule O' (O' ⊗[O i] Fm i j b),
          IntegralHeckeForms.IsLatIn M (((V0 j b).restrictScalars (O i)).baseChange O') →
          IntegralHeckeForms.sIdx (l i) M (Submodule.span O'
              ((LinearMap.rTensor (Fm i j b) (IsScalarTower.toAlgHom (O i) (Ok i k') O').toLinearMap) ''
                (eThPsi j b k' Q (BlochKatoReduction.Gen.psiAt b (ψ'.comp (art i Q))) (Dat0 i j b) :
                  Set (Ok i k' ⊗[O i] Fm i j b)))) ≤
            IntegralHeckeForms.sIdx (l i) M ((eTh j b (Dat0 i j b)).baseChange O') + epsB j b) ∧
  (∀ j ∈ Finset.Icc 1 R.m, ∀ b : Bool,
    IntegralHeckeForms.IsLatIn (eThPsi j b k' Q (BlochKatoReduction.Gen.psiAt b (ψ'.comp (art i Q))) (Dat0 i j b))
      (((V0 j b).restrictScalars (O i)).baseChange (Ok i k')) ∧
    eThPsi j b k' Q (BlochKatoReduction.Gen.psiAt b (ψ'.comp (art i Q))) (Dat0 i j b) ≤
      eThPMt j b k' Q (BlochKatoReduction.Gen.psiAt b (ψ'.comp (art i Q)))) ∧
  (∃ epsT : Sig i → ℝ, (∀ s, 0 ≤ epsT s) ∧ ∑ s ∈ SigG, epsT s ≤ eps' ∧
    ∀ s, goodS s → sLen s k' Q (BlochKatoReduction.Gen.psiAt (side i s) (ψ'.comp (art i Q))) ≤
      ENNReal.ofReal ((nu : ℝ) + epsT s)) ∧
  (∀ lam : ab i, thEval Q lam k' (BlochKatoReduction.Gen.psiAt (sideL i lam) ψ') ≠ 0 ∧
    -(N0 i : ℝ) ≤ BlochKatoReduction.Gen.vK (Ok i k') (l i)
      (thEval Q lam k' (BlochKatoReduction.Gen.psiAt (sideL i lam) ψ')) ∧
    BlochKatoReduction.Gen.vK (Ok i k') (l i)
      (thEval Q lam k' (BlochKatoReduction.Gen.psiAt (sideL i lam) ψ')) ≤
      BlochKatoReduction.Gen.vK (O i) (l i) (∑ δ, thX i ∅ lam δ) + eps') ∧
  (R.t : ℝ) * ∑ P ∈ Q, sInf {x : ℝ | ∃ σ ∈ Ine (F := H.E) (plOm.1 P),
    (ψ'.comp (art i Q)) σ ≠ 1 ∧ x = BlochKatoReduction.Gen.nval (Ok i k') (l i)
      (((ψ'.comp (art i Q)) σ : Ok i k') - 1)} ≤ eps'

private theorem goodTwRaw_congr
    {R R' : Ranks} (hR : R = R') {H : Host R} {H' : Host R'} (hH : HEq H H')
    {loc loc' : LocTheory} (hloc : loc = loc') {Om Om' : Type} (hOm : Om = Om')
    [instOm : Field Om] [instOm' : Field Om'] (hinstOm : HEq instOm instOm')
    [algOm : Algebra H.E Om] [algOm' : Algebra H'.E Om'] (halgOm : HEq algOm algOm')
    {plOm : Formalism.GaloisCohomology.Places H.E Om} {plOm' : Formalism.GaloisCohomology.Places H'.E Om'} (hplOm : HEq plOm plOm')
    {PlG PlG' : Fin 2 → Type} (hPlG : HEq PlG PlG') {cc : Om ≃+* Om} {cc' : Om' ≃+* Om'} (hcc : HEq cc cc')
    {Tw Tw' : Type} (hTw : Tw = Tw') {l : Tw → ℕ} {l' : Tw' → ℕ} (hl : HEq l l')
    [lPrime : ∀ i, Fact (l i).Prime] [lPrime' : ∀ i, Fact (l' i).Prime]
    {O0 : Tw → Type} {O0' : Tw' → Type} (hO0 : HEq O0 O0')
    [crO0 : ∀ i, CommRing (O0 i)] [crO0' : ∀ i, CommRing (O0' i)] (hcrO0 : HEq crO0 crO0')
    [algO0 : ∀ i, Algebra ℤ_[l i] (O0 i)] [algO0' : ∀ i, Algebra ℤ_[l' i] (O0' i)] (halgO0 : HEq algO0 algO0')
    [topO0 : ∀ i, TopologicalSpace (O0 i)] [topO0' : ∀ i, TopologicalSpace (O0' i)] (htopO0 : HEq topO0 topO0')
    {O : Tw → Type} {O' : Tw' → Type} (hO : HEq O O')
    [crO : ∀ i, CommRing (O i)] [crO' : ∀ i, CommRing (O' i)] (hcrO : HEq crO crO')
    [domO : ∀ i, IsDomain (O i)] [domO' : ∀ i, IsDomain (O' i)]
    [dvrO : ∀ i, IsDiscreteValuationRing (O i)] [dvrO' : ∀ i, IsDiscreteValuationRing (O' i)]
    [algO : ∀ i, Algebra (O0 i) (O i)] [algO' : ∀ i, Algebra (O0' i) (O' i)] (halgO : HEq algO algO')
    {Ok : Tw → ℕ → Type} {Ok' : Tw' → ℕ → Type} (hOk : HEq Ok Ok')
    [crOk : ∀ i k, CommRing (Ok i k)] [crOk' : ∀ i k, CommRing (Ok' i k)] (hcrOk : HEq crOk crOk')
    [domOk : ∀ i k, IsDomain (Ok i k)] [domOk' : ∀ i k, IsDomain (Ok' i k)]
    [dvrOk : ∀ i k, IsDiscreteValuationRing (Ok i k)] [dvrOk' : ∀ i k, IsDiscreteValuationRing (Ok' i k)]
    [algOk : ∀ i k, Algebra (O i) (Ok i k)] [algOk' : ∀ i k, Algebra (O' i) (Ok' i k)] (halgOk : HEq algOk algOk')
    {Ok_inj : ∀ i k, Function.Injective (algebraMap (O i) (Ok i k))}
    {Ok_inj' : ∀ i k, Function.Injective (algebraMap (O' i) (Ok' i k))}
    {zk : ∀ i k, (Ok i k)ˣ} {zk' : ∀ i k, (Ok' i k)ˣ} (hzk : HEq zk zk')
    {pD : Tw → Finset (HeightOneSpectrum (𝓞 H.E))} {pD' : Tw' → Finset (HeightOneSpectrum (𝓞 H'.E))} (hpD : HEq pD pD')
    {chi1 : ∀ i, ℕ → Bool → (G H.E Om →* (O0 i)ˣ)} {chi1' : ∀ i, ℕ → Bool → (G H'.E Om' →* (O0' i)ˣ)} (hchi1 : HEq chi1 chi1')
    {Sig : Tw → Type} {Sig' : Tw' → Type} (hSig : HEq Sig Sig')
    [finSig : ∀ i, Fintype (Sig i)] [finSig' : ∀ i, Fintype (Sig' i)] (hfinSig : HEq finSig finSig')
    {jS : ∀ i, Sig i → ℕ} {jS' : ∀ i, Sig' i → ℕ} (hjS : HEq jS jS')
    {side : ∀ i, Sig i → Bool} {side' : ∀ i, Sig' i → Bool} (hside : HEq side side')
    {rhoS : ∀ i, Sig i → (G H.E Om →* GL (Fin R.r) (O0 i))}
    {rhoS' : ∀ i, Sig' i → (G H'.E Om' →* GL (Fin R'.r) (O0' i))} (hrhoS : HEq rhoS rhoS')
    {S0 : Tw → Finset (HeightOneSpectrum (𝓞 H.E))} {S0' : Tw' → Finset (HeightOneSpectrum (𝓞 H'.E))} (hS0 : HEq S0 S0')
    {hEig : ∀ i, Sig i → ℕ → HeightOneSpectrum (𝓞 H.E) → O i}
    {hEig' : ∀ i, Sig' i → ℕ → HeightOneSpectrum (𝓞 H'.E) → O' i} (hhEig : HEq hEig hEig')
    {ab : Tw → Type} {ab' : Tw' → Type} (hab : HEq ab ab')
    {sideL : ∀ i, ab i → Bool} {sideL' : ∀ i, ab' i → Bool} (hsideL : HEq sideL sideL')
    {RCG : Tw → Finset (HeightOneSpectrum (𝓞 H.E)) → Type}
    {RCG' : Tw' → Finset (HeightOneSpectrum (𝓞 H'.E)) → Type} (hRCG : HEq RCG RCG')
    [grpRCG : ∀ i Q, CommGroup (RCG i Q)] [grpRCG' : ∀ i Q, CommGroup (RCG' i Q)] (hgrpRCG : HEq grpRCG grpRCG')
    [finRCG : ∀ i Q, Fintype (RCG i Q)] [finRCG' : ∀ i Q, Fintype (RCG' i Q)] (hfinRCG : HEq finRCG finRCG')
    {art : ∀ i Q, G H.E Om →* RCG i Q} {art' : ∀ i Q, G H'.E Om' →* RCG' i Q} (hart : HEq art art')
    {thX : ∀ i Q, ab i → RCG i Q → FractionRing (O i)} {thX' : ∀ i Q, ab' i → RCG' i Q → FractionRing (O' i)} (hthX : HEq thX thX')
    {Fm : Tw → ℕ → Bool → Type} {Fm' : Tw' → ℕ → Bool → Type} (hFm : HEq Fm Fm')
    [acgFm : ∀ i j b, AddCommGroup (Fm i j b)] [acgFm' : ∀ i j b, AddCommGroup (Fm' i j b)] (hacgFm : HEq acgFm acgFm')
    [modFmK : ∀ i j b, Module (FractionRing (O i)) (Fm i j b)]
    [modFmK' : ∀ i j b, Module (FractionRing (O' i)) (Fm' i j b)] (hmodFmK : HEq modFmK modFmK')
    [modFmO : ∀ i j b, Module (O i) (Fm i j b)] [modFmO' : ∀ i j b, Module (O' i) (Fm' i j b)] (hmodFmO : HEq modFmO modFmO')
    [towFm : ∀ i j b, IsScalarTower (O i) (FractionRing (O i)) (Fm i j b)]
    [towFm' : ∀ i j b, IsScalarTower (O' i) (FractionRing (O' i)) (Fm' i j b)]
    {actG : ∀ i j b, G0gRaw R H PlG →* (Fm i j b ≃ₗ[FractionRing (O i)] Fm i j b)}
    {actG' : ∀ i j b, G0gRaw R' H' PlG' →* (Fm' i j b ≃ₗ[FractionRing (O' i)] Fm' i j b)} (hactG : HEq actG actG')
    {U : Subgroup (G0gRaw R H PlG)} {U' : Subgroup (G0gRaw R' H' PlG')} (hU : HEq U U')
    {psiU : ∀ i, Bool → U →* (FractionRing (O i))ˣ} {psiU' : ∀ i, Bool → U' →* (FractionRing (O' i))ˣ} (hpsiU : HEq psiU psiU')
    {eAlg : ∀ i, Bool → MonoidAlgebra (FractionRing (O i)) (G0gRaw R H PlG)}
    {eAlg' : ∀ i, Bool → MonoidAlgebra (FractionRing (O' i)) (G0gRaw R' H' PlG')} (heAlg : HEq eAlg eAlg')
    {Dat : Tw → ℕ → Bool → Type} {Dat' : Tw' → ℕ → Bool → Type} (hDat : HEq Dat Dat')
    {thF : ∀ i j b, Dat i j b → Fm i j b} {thF' : ∀ i j b, Dat' i j b → Fm' i j b} (hthF : HEq thF thF')
    {lev : ∀ i j b, Dat i j b → Finset (PlE H)} {lev' : ∀ i j b, Dat' i j b → Finset (PlE H')} (hlev : HEq lev lev')
    {thPsi : ∀ i j b k, Finset (PlE H) → (G H.E Om →* (Ok i k)ˣ) → Dat i j b → Set (Ok i k ⊗[O i] Fm i j b)}
    {thPsi' : ∀ i j b k, Finset (PlE H') → (G H'.E Om' →* (Ok' i k)ˣ) → Dat' i j b → Set (Ok' i k ⊗[O' i] Fm' i j b)}
    (hthPsi : HEq thPsi thPsi')
    {MtV : ∀ i, ℕ → Bool → ∀ k, Finset (PlE H) → (G H.E Om →* (Ok i k)ˣ) → Type}
    {MtV' : ∀ i, ℕ → Bool → ∀ k, Finset (PlE H') → (G H'.E Om' →* (Ok' i k)ˣ) → Type} (hMtV : HEq MtV MtV')
    [acgMt : ∀ i j b k Q ψ, AddCommGroup (MtV i j b k Q ψ)]
    [acgMt' : ∀ i j b k Q ψ, AddCommGroup (MtV' i j b k Q ψ)] (hacgMt : HEq acgMt acgMt')
    [modMtO : ∀ i j b k Q ψ, Module (Ok i k) (MtV i j b k Q ψ)]
    [modMtO' : ∀ i j b k Q ψ, Module (Ok' i k) (MtV' i j b k Q ψ)] (hmodMtO : HEq modMtO modMtO')
    {MtLat : ∀ i j b k Q ψ, Submodule (Ok i k) (MtV i j b k Q ψ)}
    {MtLat' : ∀ i j b k Q ψ, Submodule (Ok' i k) (MtV' i j b k Q ψ)} (hMtLat : HEq MtLat MtLat')
    {thP : ∀ i j b k Q ψ, MtV i j b k Q ψ →ₗ[Ok i k] (Ok i k ⊗[O i] Fm i j b)}
    {thP' : ∀ i j b k Q ψ, MtV' i j b k Q ψ →ₗ[Ok' i k] (Ok' i k ⊗[O' i] Fm' i j b)} (hthP : HEq thP thP')
    {hkF : ∀ i j b, ℕ → PlE H → Module.End (FractionRing (O i)) (Fm i j b)}
    {hkF' : ∀ i j b, ℕ → PlE H' → Module.End (FractionRing (O' i)) (Fm' i j b)} (hhkF : HEq hkF hkF')
    {br : ∀ (i : Tw) (v : HeightOneSpectrum (𝓞 H.E)), v ∈ placesOver H.E (l i) →
      LocBridge (l i) H.E Om (Dec (F := H.E) (plOm.1 v)) (O0 i)}
    {br' : ∀ (i : Tw') (v : HeightOneSpectrum (𝓞 H'.E)), v ∈ placesOver H'.E (l' i) →
      LocBridge (l' i) H'.E Om' (Dec (F := H'.E) (plOm'.1 v)) (O0' i)} (hbr : HEq br br')
    {Dat0 : ∀ i j b, Set (Dat i j b)} {Dat0' : ∀ i j b, Set (Dat' i j b)} (hDat0 : HEq Dat0 Dat0')
    {N0 : Tw → ℕ} {N0' : Tw' → ℕ} (hN0 : HEq N0 N0') {i : Tw} {i' : Tw'} (hi : HEq i i') (eps' : ℝ)
    {S : ∀ (j : ℕ) (b : Bool), Finset (Dat i j b)} {S' : ∀ (j : ℕ) (b : Bool), Finset (Dat' i' j b)} (hS : HEq S S')
    {A Q : Finset (PlE H)} {A' Q' : Finset (PlE H')} (hA : HEq A A') (hQ : HEq Q Q') (k' : ℕ)
    {ψ' : RCG i Q →* (Ok i k')ˣ} {ψ'' : RCG' i' Q' →* (Ok' i' k')ˣ} (hψ : HEq ψ' ψ'')
    (h : goodTwRaw R H loc Om plOm PlG cc Tw l O0 O Ok Ok_inj zk pD chi1 Sig jS side rhoS S0 hEig ab sideL RCG art thX Fm actG U psiU eAlg Dat thF lev thPsi MtV MtLat thP hkF br Dat0 N0 i eps' S A Q k' ψ') :
    goodTwRaw R' H' loc' Om' plOm' PlG' cc' Tw' l' O0' O' Ok' Ok_inj' zk' pD' chi1' Sig' jS' side' rhoS' S0' hEig' ab' sideL' RCG' art' thX' Fm' actG' U' psiU' eAlg' Dat' thF' lev' thPsi' MtV' MtLat' thP' hkF' br' Dat0' N0' i' eps' S' A' Q' k' ψ'' := by
  subst hR; subst hH; subst hloc; subst hOm; subst hinstOm; subst halgOm; subst hplOm; subst hPlG; subst hcc; subst hTw; subst hl
  cases (Subsingleton.elim lPrime lPrime')
  subst hO0; subst hcrO0; subst halgO0; subst htopO0; subst hO; subst hcrO
  cases (Subsingleton.elim domO domO'); cases (Subsingleton.elim dvrO dvrO')
  subst halgO; subst hOk; subst hcrOk
  cases (Subsingleton.elim domOk domOk'); cases (Subsingleton.elim dvrOk dvrOk')
  subst halgOk; cases (Subsingleton.elim Ok_inj Ok_inj')
  subst hzk; subst hpD; subst hchi1; subst hSig; subst hfinSig; subst hjS; subst hside; subst hrhoS
  subst hS0; subst hhEig; subst hab; subst hsideL; subst hRCG; subst hgrpRCG; subst hfinRCG; subst hart; subst hthX
  subst hFm; subst hacgFm; subst hmodFmK; subst hmodFmO; cases (Subsingleton.elim towFm towFm')
  subst hactG; subst hU; subst hpsiU; subst heAlg; subst hDat; subst hthF; subst hlev; subst hthPsi
  subst hMtV; subst hacgMt; subst hmodMtO; subst hMtLat; subst hthP; subst hhkF
  subst hbr; subst hDat0; subst hN0; subst hi; subst hS; subst hA; subst hQ; subst hψ; exact h

theorem goodTw_transfer {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    {Y : NExp D.R D.host D.what₂ D.LL0 N X} {Y' : NExp D'.R D'.host D'.what₂ D'.LL0 N' X'}
    (h1 : SameGalois N N') (h2 : TwistDataAgreeAcrossCoefficients X X') (h3 : SameForms Y Y')
    {B : BlochKatoReduction.Gen.BKPh X} {B' : BlochKatoReduction.Gen.BKPh X'} (hB : HEq B.br B'.br) (hY : B.ex = Y) (hY' : B'.ex = Y')
    {E : IntegralHeckeForms.ExpDat Y} {E' : IntegralHeckeForms.ExpDat Y'} (hE : HEq E.Dat0 E'.Dat0) {N0 : X.Tw → ℕ} {N0' : X'.Tw → ℕ} (hN : HEq N0 N0')
    {i : X.Tw} {i' : X'.Tw} (hi : HEq i i') (e : ℝ)
    {S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b)} {S' : ∀ (j : ℕ) (b : Bool), Finset (Y'.Dat i' j b)} (hS : HEq S S')
    {A Q : Finset (PlE D.host)} {A' Q' : Finset (PlE D'.host)} (hA : HEq A A') (hQ : HEq Q Q') (k : ℕ)
    {ψ : X.RCG i Q →* (X.Ok i k)ˣ} {ψ' : X'.RCG i' Q' →* (X'.Ok i' k)ˣ} (hψ : HEq ψ ψ')
    (h : IntegralHeckeForms.GoodTw Y B E N0 i e S A Q k ψ) : IntegralHeckeForms.GoodTw Y' B' E' N0' i' e S' A' Q' k ψ' := by
  obtain ⟨br, Y₁⟩ := B
  obtain ⟨br', Y₁'⟩ := B'
  dsimp only at hB hY hY'
  subst Y₁; subst Y₁'
  exact goodTwRaw_congr h1.R h1.host h1.loc
    (eq_of_heq h1.Om) h1.instOm h1.algOm h1.plOm h1.PlG h2.cc
    (eq_of_heq h2.Tw) h2.l
    h2.O0 h2.crO0 h2.algO0 h2.topO0
    h2.O h2.crO h2.algO
    h2.Ok h2.crOk h2.algOk (Ok_inj := X.Ok_inj) (Ok_inj' := X'.Ok_inj)
    h2.zk h2.pD h2.chi1 h2.Sig h2.finSig h2.jS h2.side h2.rhoS h2.S0 h2.hEig
    h2.abelian₂ h2.sideL h2.RCG h2.grpRCG h2.finRCG h2.art h2.th
    h3.Fm h3.acgFm h3.modFmK h3.modFmO
    h3.actG h3.U h3.psiU h3.eAlg h3.Dat h3.th h3.lev h3.thPsi
    h3.MtV h3.acgMt h3.modMtO h3.MtLat h3.thP h3.hkF
    hB hE hN hi e hS hA hQ k hψ h

private def fullRkBasisRaw
    (R : Ranks) (H : Host R) (PlG : Fin 2 → Type)
    (Tw : Type) (O : Tw → Type) [∀ i, CommRing (O i)]
    (Fm : Tw → ℕ → Bool → Type) [∀ i j b, AddCommGroup (Fm i j b)]
    [∀ i j b, Module (FractionRing (O i)) (Fm i j b)] [∀ i j b, Module (O i) (Fm i j b)]
    [∀ i j b, IsScalarTower (O i) (FractionRing (O i)) (Fm i j b)]
    (actG : ∀ i j b, G0gRaw R H PlG →* (Fm i j b ≃ₗ[FractionRing (O i)] Fm i j b))
    (U : Subgroup (G0gRaw R H PlG)) (psiU : ∀ i, Bool → U →* (FractionRing (O i))ˣ)
    (eAlg : ∀ i, Bool → MonoidAlgebra (FractionRing (O i)) (G0gRaw R H PlG))
    (Dat : Tw → ℕ → Bool → Type) (thF : ∀ i j b, Dat i j b → Fm i j b)
    (Dat0 : ∀ i j b, Set (Dat i j b))
    (i : Tw) (j : ℕ) (b : Bool) (S : Finset (Dat i j b)) : Prop :=
  let c : O i := ((∏ k : Fin 2, (Nat.card (GL (Fin R.r) (ZMod (H.g k)))) ^ R.f : ℕ) : O i)
  let A : Module.End (O i) (Fm i j b) := c • eORaw R H PlG O Fm actG eAlg i j b
  let V0 := V0Raw R H PlG O Fm actG U psiU eAlg i j b
  let Th := ThRaw O Fm Dat thF i j b (Dat0 i j b)
  (Dat0 i j b ⊆ Dat0 i j b ∧
    (∀ x ∈ Th.map A, x ∈ V0) ∧
    Submodule.span (FractionRing (O i)) ((Th.map A : Submodule (O i) (Fm i j b)) : Set (Fm i j b)) = V0) ∧
  ((↑S ⊆ Dat0 i j b) ∧
    LinearIndependent (O i) (fun a : ↥S => A (thF i j b a)) ∧
    Submodule.span (O i) ((fun a => A (thF i j b a)) '' ↑S) = Th.map A)

private theorem fullRkBasisRaw_congr
    {R R' : Ranks} (hR : R = R')
    {H : Host R} {H' : Host R'} (hH : HEq H H')
    {PlG PlG' : Fin 2 → Type} (hPlG : HEq PlG PlG')
    {Tw Tw' : Type} (hTw : Tw = Tw')
    {O : Tw → Type} {O' : Tw' → Type} (hO : HEq O O')
    [crO : ∀ i, CommRing (O i)] [crO' : ∀ i, CommRing (O' i)] (hcrO : HEq crO crO')
    {Fm : Tw → ℕ → Bool → Type} {Fm' : Tw' → ℕ → Bool → Type} (hFm : HEq Fm Fm')
    [acgFm : ∀ i j b, AddCommGroup (Fm i j b)] [acgFm' : ∀ i j b, AddCommGroup (Fm' i j b)] (hacgFm : HEq acgFm acgFm')
    [modFmK : ∀ i j b, Module (FractionRing (O i)) (Fm i j b)]
    [modFmK' : ∀ i j b, Module (FractionRing (O' i)) (Fm' i j b)] (hmodFmK : HEq modFmK modFmK')
    [modFmO : ∀ i j b, Module (O i) (Fm i j b)]
    [modFmO' : ∀ i j b, Module (O' i) (Fm' i j b)] (hmodFmO : HEq modFmO modFmO')
    [towFm : ∀ i j b, IsScalarTower (O i) (FractionRing (O i)) (Fm i j b)]
    [towFm' : ∀ i j b, IsScalarTower (O' i) (FractionRing (O' i)) (Fm' i j b)]
    {actG : ∀ i j b, G0gRaw R H PlG →* (Fm i j b ≃ₗ[FractionRing (O i)] Fm i j b)}
    {actG' : ∀ i j b, G0gRaw R' H' PlG' →* (Fm' i j b ≃ₗ[FractionRing (O' i)] Fm' i j b)} (hactG : HEq actG actG')
    {U : Subgroup (G0gRaw R H PlG)} {U' : Subgroup (G0gRaw R' H' PlG')} (hU : HEq U U')
    {psiU : ∀ i, Bool → U →* (FractionRing (O i))ˣ}
    {psiU' : ∀ i, Bool → U' →* (FractionRing (O' i))ˣ} (hpsiU : HEq psiU psiU')
    {eAlg : ∀ i, Bool → MonoidAlgebra (FractionRing (O i)) (G0gRaw R H PlG)}
    {eAlg' : ∀ i, Bool → MonoidAlgebra (FractionRing (O' i)) (G0gRaw R' H' PlG')} (heAlg : HEq eAlg eAlg')
    {Dat : Tw → ℕ → Bool → Type} {Dat' : Tw' → ℕ → Bool → Type} (hDat : HEq Dat Dat')
    {thF : ∀ i j b, Dat i j b → Fm i j b} {thF' : ∀ i j b, Dat' i j b → Fm' i j b} (hthF : HEq thF thF')
    {Dat0 : ∀ i j b, Set (Dat i j b)} {Dat0' : ∀ i j b, Set (Dat' i j b)} (hDat0 : HEq Dat0 Dat0')
    {i : Tw} {i' : Tw'} (hi : HEq i i') (j : ℕ) (b : Bool)
    {S : Finset (Dat i j b)} {S' : Finset (Dat' i' j b)} (hS : HEq S S')
    (h : fullRkBasisRaw R H PlG Tw O Fm actG U psiU eAlg Dat thF Dat0 i j b S) :
    fullRkBasisRaw R' H' PlG' Tw' O' Fm' actG' U' psiU' eAlg' Dat' thF' Dat0' i' j b S' := by
  subst hR; subst hH; subst hPlG; subst hTw; subst hO; subst hcrO
  subst hFm; subst hacgFm; subst hmodFmK; subst hmodFmO
  have htowFm : towFm = towFm' := Subsingleton.elim _ _; subst htowFm
  subst hactG; subst hU; subst hpsiU; subst heAlg; subst hDat; subst hthF; subst hDat0; subst hi; subst hS
  exact h

theorem fullRk_basisOf_transfer {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    {Y : NExp D.R D.host D.what₂ D.LL0 N X} {Y' : NExp D'.R D'.host D'.what₂ D'.LL0 N' X'}
    (h1 : SameGalois N N') (h2 : TwistDataAgreeAcrossCoefficients X X') (h3 : SameForms Y Y')
    {E : IntegralHeckeForms.ExpDat Y} {E' : IntegralHeckeForms.ExpDat Y'} (hE : HEq E.Dat0 E'.Dat0)
    {i : X.Tw} {i' : X'.Tw} (hi : HEq i i') (j : ℕ) (b : Bool)
    {S : Finset (Y.Dat i j b)} {S' : Finset (Y'.Dat i' j b)} (hS : HEq S S')
    (h : IntegralHeckeForms.FullRk Y E i j b (IntegralHeckeForms.SgJ Y E i j b) ∧ IntegralHeckeForms.BasisOf Y i j b (IntegralHeckeForms.SgJ Y E i j b) S) :
    IntegralHeckeForms.FullRk Y' E' i' j b (IntegralHeckeForms.SgJ Y' E' i' j b) ∧ IntegralHeckeForms.BasisOf Y' i' j b (IntegralHeckeForms.SgJ Y' E' i' j b) S' := by
  delta IntegralHeckeForms.FullRk IntegralHeckeForms.BasisOf IntegralHeckeForms.AO at h ⊢
  rw [N.restN_card_levelGroup_eq] at h
  rw [N'.restN_card_levelGroup_eq]
  exact fullRkBasisRaw_congr h1.R h1.host h1.PlG (eq_of_heq h2.Tw) h2.O h2.crO
    h3.Fm h3.acgFm h3.modFmK h3.modFmO
    h3.actG h3.U h3.psiU h3.eAlg h3.Dat h3.th hE hi j b hS h

private theorem same_basic_raw
    {R R' : Ranks} (hR : R = R')
    {H : Host R} {H' : Host R'} (hH : HEq H H')
    {Tw Tw' : Type} (hTw : Tw = Tw')
    {l : Tw → ℕ} {l' : Tw' → ℕ} (hl : HEq l l')
    {O0 : Tw → Type} {O0' : Tw' → Type} (hO0 : HEq O0 O0')
    [crO0 : ∀ i, CommRing (O0 i)] [crO0' : ∀ i, CommRing (O0' i)] (hcrO0 : HEq crO0 crO0')
    [domO0 : ∀ i, IsDomain (O0 i)] [domO0' : ∀ i, IsDomain (O0' i)]
    [dvrO0 : ∀ i, IsDiscreteValuationRing (O0 i)] [dvrO0' : ∀ i, IsDiscreteValuationRing (O0' i)]
    {Ok : Tw → ℕ → Type} {Ok' : Tw' → ℕ → Type} (hOk : HEq Ok Ok')
    [crOk : ∀ i k, CommRing (Ok i k)] [crOk' : ∀ i k, CommRing (Ok' i k)] (hcrOk : HEq crOk crOk')
    {RCG : Tw → Finset (PlE H) → Type} {RCG' : Tw' → Finset (PlE H') → Type} (hRCG : HEq RCG RCG')
    [grpRCG : ∀ i Q, CommGroup (RCG i Q)] [grpRCG' : ∀ i Q, CommGroup (RCG' i Q)] (hgrpRCG : HEq grpRCG grpRCG')
    {Dat : Tw → ℕ → Bool → Type} {Dat' : Tw' → ℕ → Bool → Type} (hDat : HEq Dat Dat') :
    Tw = Tw' ∧
    (Σ (i : Tw) (Q : Finset (PlE H)) (k : ℕ), RCG i Q →* (Ok i k)ˣ) =
      (Σ (i : Tw') (Q : Finset (PlE H')) (k : ℕ), RCG' i Q →* (Ok' i k)ˣ) ∧
    (∀ i j b, Finset (Dat i j b)) = (∀ i j b, Finset (Dat' i j b)) ∧
    (∀ (p : Σ (i : Tw) (Q : Finset (PlE H)) (k : ℕ), RCG i Q →* (Ok i k)ˣ)
      (p' : Σ (i : Tw') (Q : Finset (PlE H')) (k : ℕ), RCG' i Q →* (Ok' i k)ˣ), HEq p p' →
      HEq p.1 p'.1 ∧ HEq p.2.1 p'.2.1 ∧ p.2.2.1 = p'.2.2.1 ∧ HEq p.2.2.2 p'.2.2.2) ∧
    ∀ (i : Tw) (i' : Tw'), HEq i i' → l i = l' i' ∧
      (∀ (S : ∀ i j b, Finset (Dat i j b)) (S' : ∀ i j b, Finset (Dat' i j b)), HEq S S' →
        HEq (S i) (S' i') ∧ ∀ j b, HEq (S i j b) (S' i' j b)) ∧
      ∀ (a : FractionRing (O0 i)) (a' : FractionRing (O0' i')), HEq a a' →
        ((∃ y ∈ IsLocalRing.maximalIdeal (O0 i), algebraMap (O0 i) (FractionRing (O0 i)) y = a) ↔
          ∃ y ∈ IsLocalRing.maximalIdeal (O0' i'), algebraMap (O0' i') (FractionRing (O0' i')) y = a') := by
  subst hR; subst hH; subst hTw; subst hl; subst hO0; subst hcrO0
  have hdomO0 : domO0 = domO0' := Subsingleton.elim _ _; subst hdomO0
  have hdvrO0 : dvrO0 = dvrO0' := Subsingleton.elim _ _; subst hdvrO0
  subst hOk; subst hcrOk; subst hRCG; subst hgrpRCG; subst hDat
  refine ⟨rfl, rfl, rfl, fun p p' hp => ?_, fun i i' hi => ?_⟩
  · subst hp
    exact ⟨HEq.rfl, HEq.rfl, rfl, HEq.rfl⟩
  · subst hi
    refine ⟨rfl, fun S S' hS => ?_, fun a a' ha => ?_⟩
    · subst hS
      exact ⟨HEq.rfl, fun _ _ => HEq.rfl⟩
    · subst ha
      exact Iff.rfl

theorem same_basic {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    {Y : NExp D.R D.host D.what₂ D.LL0 N X} {Y' : NExp D'.R D'.host D'.what₂ D'.LL0 N' X'}
    (h1 : SameGalois N N') (h2 : TwistDataAgreeAcrossCoefficients X X') (h3 : SameForms Y Y') :
    X.Tw = X'.Tw ∧
    (Σ (i : X.Tw) (Q : Finset (PlE D.host)) (k : ℕ), X.RCG i Q →* (X.Ok i k)ˣ) =
      (Σ (i : X'.Tw) (Q : Finset (PlE D'.host)) (k : ℕ), X'.RCG i Q →* (X'.Ok i k)ˣ) ∧
    (∀ i j b, Finset (Y.Dat i j b)) = (∀ i j b, Finset (Y'.Dat i j b)) ∧
    (∀ (p : Σ (i : X.Tw) (Q : Finset (PlE D.host)) (k : ℕ), X.RCG i Q →* (X.Ok i k)ˣ)
      (p' : Σ (i : X'.Tw) (Q : Finset (PlE D'.host)) (k : ℕ), X'.RCG i Q →* (X'.Ok i k)ˣ), HEq p p' →
      HEq p.1 p'.1 ∧ HEq p.2.1 p'.2.1 ∧ p.2.2.1 = p'.2.2.1 ∧ HEq p.2.2.2 p'.2.2.2) ∧
    ∀ (i : X.Tw) (i' : X'.Tw), HEq i i' → X.l i = X'.l i' ∧
      (∀ (S : ∀ i j b, Finset (Y.Dat i j b)) (S' : ∀ i j b, Finset (Y'.Dat i j b)), HEq S S' →
        HEq (S i) (S' i') ∧ ∀ j b, HEq (S i j b) (S' i' j b)) ∧
      ∀ (a : FractionRing (X.O0 i)) (a' : FractionRing (X'.O0 i')), HEq a a' →
        ((∃ y ∈ IsLocalRing.maximalIdeal (X.O0 i), algebraMap (X.O0 i) (FractionRing (X.O0 i)) y = a) ↔
          ∃ y ∈ IsLocalRing.maximalIdeal (X'.O0 i'), algebraMap (X'.O0 i') (FractionRing (X'.O0 i')) y = a') :=
  same_basic_raw h1.R h1.host (eq_of_heq h2.Tw) h2.l h2.O0 h2.crO0 h2.Ok h2.crOk h2.RCG h2.grpRCG h3.Dat

structure SameExport (D D' : D7) : Prop where
  gal : SameGalois D.nd D'.nd
  set : TwistDataAgreeAcrossCoefficients D.ntw D'.ntw
  frm : SameForms D.nexp D'.nexp
  br : HEq D.ntwbr D'.ntwbr
  av : avPrimes D = avPrimes D'

theorem SameExport.refl (D : D7) : SameExport D D :=
  ⟨by constructor <;> rfl, by constructor <;> rfl, by constructor <;> rfl, HEq.rfl, rfl⟩

theorem SameExport.trans {D D' D'' : D7} (h : SameExport D D') (h' : SameExport D' D'') : SameExport D D'' :=
  ⟨⟨h.gal.R.trans h'.gal.R, h.gal.host.trans h'.gal.host, h.gal.loc.trans h'.gal.loc, h.gal.Om.trans h'.gal.Om, h.gal.instOm.trans h'.gal.instOm, h.gal.algOm.trans h'.gal.algOm, h.gal.plOm.trans h'.gal.plOm, h.gal.PlG.trans h'.gal.PlG⟩,
    ⟨h.set.cc.trans h'.set.cc, h.set.Tw.trans h'.set.Tw, h.set.l.trans h'.set.l, h.set.O0.trans h'.set.O0, h.set.crO0.trans h'.set.crO0, h.set.algO0.trans h'.set.algO0, h.set.topO0.trans h'.set.topO0, h.set.O.trans h'.set.O, h.set.crO.trans h'.set.crO, h.set.algO.trans h'.set.algO, h.set.Ok.trans h'.set.Ok, h.set.crOk.trans h'.set.crOk, h.set.algOk.trans h'.set.algOk, h.set.zk.trans h'.set.zk, h.set.pD.trans h'.set.pD, h.set.chi1.trans h'.set.chi1, h.set.Sig.trans h'.set.Sig, h.set.finSig.trans h'.set.finSig, h.set.jS.trans h'.set.jS, h.set.side.trans h'.set.side, h.set.rhoS.trans h'.set.rhoS, h.set.S0.trans h'.set.S0, h.set.hEig.trans h'.set.hEig, h.set.abelian₂.trans h'.set.abelian₂, h.set.sideL.trans h'.set.sideL, h.set.RCG.trans h'.set.RCG, h.set.grpRCG.trans h'.set.grpRCG, h.set.finRCG.trans h'.set.finRCG, h.set.art.trans h'.set.art, h.set.th.trans h'.set.th⟩,
    ⟨h.frm.Fm.trans h'.frm.Fm, h.frm.acgFm.trans h'.frm.acgFm, h.frm.modFmK.trans h'.frm.modFmK, h.frm.modFmO.trans h'.frm.modFmO, h.frm.actG.trans h'.frm.actG, h.frm.U.trans h'.frm.U, h.frm.psiU.trans h'.frm.psiU, h.frm.eAlg.trans h'.frm.eAlg, h.frm.Dat.trans h'.frm.Dat, h.frm.th.trans h'.frm.th, h.frm.lev.trans h'.frm.lev, h.frm.thPsi.trans h'.frm.thPsi, h.frm.MtV.trans h'.frm.MtV, h.frm.acgMt.trans h'.frm.acgMt, h.frm.modMtK.trans h'.frm.modMtK, h.frm.modMtO.trans h'.frm.modMtO, h.frm.MtLat.trans h'.frm.MtLat, h.frm.thP.trans h'.frm.thP, h.frm.hkF.trans h'.frm.hkF⟩,
    h.br.trans h'.br, h.av.trans h'.av⟩

theorem heq_places {R R' : Ranks} (hR : R = R') {H : Host R} {H' : Host R'} (hH : HEq H H') {A : Finset (PlE H)}
    {A' : Finset (PlE H')} {s : Finset ℕ} (h : ∀ v, v ∈ A ↔ ∃ p ∈ s, v ∈ placesOver H.E p)
    (h' : ∀ v, v ∈ A' ↔ ∃ p ∈ s, v ∈ placesOver H'.E p) : HEq A A' := by
  subst hR
  subst hH
  exact heq_of_eq (Finset.ext fun v => (h v).trans (h' v).symm)

theorem SameExport.avRec {D D' : D7} (h : SameExport D D') : HEq (AvRec D) (AvRec D') :=
  heq_places h.gal.R h.gal.host mem_avRec (by rw [h.av]; exact mem_avRec)

theorem SameExport.good {D D' : D7} (h : SameExport D D') {I : TwIn D} {I' : TwIn D'} (hE : HEq I.E.Dat0 I'.E.Dat0)
    (hN : HEq I.N0 I'.N0) (hS : HEq I.S I'.S) {p : TwPack D} {p' : TwPack D'} (hp : HEq p p')
    (hg : I.Ok p.1 ∧ IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) I.E I.N0 p.1 (twEps D p.1) (I.S p.1) (AvRec D) p.2.1 p.2.2.1 p.2.2.2) :
    I'.Ok p'.1 ∧ IntegralHeckeForms.GoodTw D'.nexp (BlochKatoReduction.bk0 D') I'.E I'.N0 p'.1 (twEps D' p'.1) (I'.S p'.1) (AvRec D') p'.2.1 p'.2.2.1 p'.2.2.2 := by
  obtain ⟨-, -, -, h1, h2⟩ := same_basic h.gal h.set h.frm
  obtain ⟨h3, h4, h5, h6⟩ := h1 p p' hp
  obtain ⟨h7, h8, -⟩ := h2 _ _ h3
  obtain ⟨i, Q, k, ψ⟩ := p
  obtain ⟨i', Q', k', ψ'⟩ := p'
  dsimp only at h3 h4 h5 h6 h7 h8 hg ⊢
  subst h5
  have hm : D'.R.m = D.R.m := by rw [h.gal.R]
  have h9 := fun j (hj : j ∈ Finset.Icc 1 D'.R.m) b => fullRk_basisOf_transfer h.gal h.set h.frm hE h3 j b ((h8 _ _ hS).2 j b)
    ⟨hg.1.1 j (hm ▸ hj) b, hg.1.2 j (hm ▸ hj) b⟩
  have he : twEps D' i' = twEps D i := by rw [twEps, twEps, h7]
  rw [he]
  exact ⟨⟨fun j hj b => (h9 j hj b).1, fun j hj b => (h9 j hj b).2⟩,
    goodTw_transfer h.gal h.set h.frm (B := BlochKatoReduction.bk0 D) (B' := BlochKatoReduction.bk0 D') h.br rfl rfl hE hN h3 _ (h8 _ _ hS).1 h.avRec h4 k h6 hg.2⟩

end GlobalTheory.TwistChoice

end

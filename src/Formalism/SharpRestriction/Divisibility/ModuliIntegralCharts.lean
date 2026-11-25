module

public import Formalism.LocalRingCardinality.DataDIV

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts

open Formalism.BasicNotions NumberField

structure CF (p : ℕ) where
  C : Type
  [fld : NontriviallyNormedField C]
  [ultra : IsUltrametricDist C]
  [ac : IsAlgClosed C]
  [cpl : CompleteSpace C]
  [ch0 : CharZero C]
  norm_p : ‖(p : C)‖ = (p : ℝ)⁻¹

attribute [instance] CF.fld CF.ultra CF.ac CF.cpl CF.ch0

def Ospan {C V : Type} [NormedField C] [AddCommGroup V] [Module C V] (S : Set V) : AddSubgroup V :=
  AddSubgroup.closure {v | ∃ a : C, ‖a‖ ≤ 1 ∧ ∃ s ∈ S, v = a • s}

section Forms

variable {E : Type} [Field E] [NumberField E]

def SymB (cj : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] :
    Submodule ℝ (Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) where
  carrier := {β | (∀ a b, β a b = β b a) ∧
    ∀ (c c' : 𝓞 E), (c' : E) = cj (c : E) → ∀ a b, β (c • a) b = β a (c' • b)}
  add_mem' := by
    rintro β γ ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨fun a b => ?_, fun c c' h a b => ?_⟩
    · simp [h1 a b, h3 a b]
    · simp [h2 c c' h a b, h4 c c' h a b]
  zero_mem' := by simp
  smul_mem' := by
    rintro t β ⟨h1, h2⟩
    refine ⟨fun a b => ?_, fun c c' h a b => ?_⟩
    · simp [h1 a b]
    · simp [h2 c c' h a b]

def phiC (cj : E → E) {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y] (b : SymB cj Y) : ℝ :=
  sInf {x | ∃ l : SymB cj Y →ₗ[ℝ] ℝ,
    (∀ β : SymB cj Y, (∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l β = z) ∧
    (∀ β : SymB cj Y, (∀ a, 0 ≤ (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) → β ≠ 0 → 0 < l β) ∧ x = l b}

end Forms

abbrev PsiT (D : Formalism.BasicNotions.D7) : Type := ↥(D.R.Psi)

structure Loc (D : Formalism.BasicNotions.D7) (r j p : ℕ) where

  Mdl : Type

  Xm : Mdl

  YY : Mdl

  Xn : ℕ → Mdl

  Pt : Mdl → Type

  fld : ∀ {Z : Mdl}, Pt Z → CF p

  Ylat : ∀ {Z : Mdl}, Pt Z → Type
  [ylAdd : ∀ {Z : Mdl} (y : Pt Z), AddCommGroup (Ylat y)]
  [ylMod : ∀ {Z : Mdl} (y : Pt Z), Module (𝓞 D.host.E) (Ylat y)]
  [ylFree : ∀ {Z : Mdl} (y : Pt Z), Module.Free ℤ (Ylat y)]
  [ylFin : ∀ {Z : Mdl} (y : Pt Z), Module.Finite ℤ (Ylat y)]

  be : ∀ {Z : Mdl} (y : Pt Z), Ylat y →ₗ[ℤ] Ylat y →ₗ[ℤ] ℝ
  be_symm : ∀ {Z : Mdl} (y : Pt Z) (a b : Ylat y), be y a b = be y b a
  be_bal : ∀ {Z : Mdl} (y : Pt Z) (c c' : 𝓞 D.host.E), (c' : D.host.E) = D.host.conj (c : D.host.E) →
    ∀ a b : Ylat y, be y (c • a) b = be y a (c' • b)

  be_posDef : ∀ {Z : Mdl} (y : Pt Z), ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ (Ylat y)),
    ∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ k, c i * c k * be y (b i) (b k)

  yl_rank : ∀ {Z : Mdl} (y : Pt Z), ∃ ρ : ℕ, Module.finrank ℤ (Ylat y) = 2 * D.R.f * ρ ∧
    (1 ≤ j → j + 1 ≤ r → ρ ≤ j ∧ ρ + j ≤ r)

  Gen : Mdl → Type

  abAt : ∀ {Z : Mdl}, Gen Z → Prop

  Sh : Mdl → Type

  IsInv : ∀ {Z : Mdl}, Sh Z → Prop

  IsLocFree : ∀ {Z : Mdl}, Sh Z → Prop

  Sec : ∀ {Z : Mdl}, Sh Z → Type
  [secAdd : ∀ {Z : Mdl} (F : Sh Z), AddCommGroup (Sec F)]

  H0 : ∀ {Z : Mdl} (F : Sh Z), AddSubgroup (Sec F)

  nrm : ∀ {Z : Mdl} (F : Sh Z), Sec F → Pt Z → ℝ
  nrm_nonneg : ∀ {Z : Mdl} (F : Sh Z) (f : Sec F) (y : Pt Z), 0 ≤ nrm F f y

  norm_le_one_of_mem_sections : ∀ {Z : Mdl} (F : Sh Z) (f : Sec F), f ∈ H0 F → ∀ y, nrm F f y ≤ 1

  GIso : ∀ {Z : Mdl}, Sh Z → Sh Z → Type

  vrat : ∀ {Z : Mdl} {F₁ F₂ : Sh Z}, GIso F₁ F₂ → Pt Z → ℝ

  Lb : (PsiT D → ℕ → ℤ) → Sh YY
  Lb_inv : ∀ l, IsInv (Lb l)

  nrmRef : ∀ l, Sec (Lb l) → Pt YY → ℝ

  DVP : Type

  dvRho : DVP → ℕ

  Ext : DVP → Type

  Chart : Mdl → (y : DVP) → Ext y → Type

  chAt : ∀ {Z y e}, Chart Z y e → Prop

  chOpen : ∀ {Z y e}, Chart Z y e → Prop

  chAbExact : ∀ {Z y e}, Chart Z y e → Prop

  chModU : ∀ {Z y e}, Chart Z y e → Prop

  chConst : ∀ {Z y e}, Chart Z y e → Prop

  PL : Type

  phiAt : PL → ∀ {Z : Mdl}, Pt Z → ℝ

  phiAt_zero : ∀ (φ : PL) {Z : Mdl} (y : Pt Z), Subsingleton (Ylat y) → phiAt φ y = 0

  divGe : ∀ {Z : Mdl} (F : Sh Z), Sec F → ℚ → PL → Prop

  FJd : Type

  Chr : FJd → Type

  fjN : ∀ l, Sec (Lb l) → (t : FJd) → Chr t → ℝ

  Unim : Type

  LBG : Unim → Type

  LBGq : Unim → Type
  resQ : ∀ {La}, LBG La → LBGq La

  PPq : ∀ La, LBGq La

  symmG : ∀ {La}, LBG La → Prop
  rigG : ∀ {La}, LBG La → Prop

  LBGt : ∀ (y : Pt Xm), Unim → Type
  LBB : ∀ (y : Pt Xm), Unim → Type
  resGt : ∀ {La}, LBG La → ∀ y, LBGt y La
  prPull : ∀ {y La}, LBB y La → LBGt y La

  principal : ∀ {y La}, LBB y La → Prop

  psiV : ∀ {Z : Mdl} (y : Pt Z), Ylat y → ℝ

  piPP : Sh Xm

  keySh : ℕ → Sh Xm

  latStd : ℕ → Unim

  At : Pt Xm → Unim → ℕ → Type
  [atAdd : ∀ y La n, AddCommGroup (At y La n)]
  [atFin : ∀ y La n, Fintype (At y La n)]

  at_tors : ∀ y La n (x : At y La n), n • x = 0
  at_card : ∀ y nW n, 0 < n → Fintype.card (At y (latStd nW) n) = n ^ (2 * (D.R.f * r * nW))

  Th : Pt Xm → Unim → ℕ → Type
  [thGrp : ∀ y La n, Group (Th y La n)]
  ovr : ∀ y La n, Th y La n →* Multiplicative (At y La n)
  ovr_surj : ∀ y La n, Function.Surjective (ovr y La n)
  scal : ∀ y La n, ((fld y).C)ˣ →* Th y La n
  scal_inj : ∀ y La n, Function.Injective (scal y La n)
  scal_central : ∀ y La n a g, scal y La n a * g = g * scal y La n a
  ker_ovr : ∀ y La n g, ovr y La n g = 1 ↔ ∃ a, scal y La n a = g

  dl : ∀ y La n, Th y La n ≃* Th y La n
  dl_ovr : ∀ y La n g, ovr y La n (dl y La n g) = (ovr y La n g)⁻¹
  dl_scal : ∀ y La n a, dl y La n (scal y La n a) = scal y La n a
  dl_dl : ∀ y La n g, dl y La n (dl y La n g) = g

  Sn : Pt Xm → Unim → ℕ → Type
  [snAdd : ∀ y La n, AddCommGroup (Sn y La n)]
  [snMod : ∀ y La n, Module (fld y).C (Sn y La n)]
  act : ∀ y La n, Th y La n →* Module.End (fld y).C (Sn y La n)
  act_scal : ∀ y La n a s, act y La n (scal y La n a) s = (a : (fld y).C) • s

  vth : ∀ y La n, Sn y La n

  Jet : Pt Xm → Unim → ℕ → ℕ → Type
  [jAdd : ∀ y La n DF, AddCommGroup (Jet y La n DF)]
  [jMod : ∀ y La n DF, Module (fld y).C (Jet y La n DF)]
  intJet : ∀ y La n DF, AddSubgroup (Jet y La n DF)
  jet : ∀ y La n DF, Sn y La n →ₗ[(fld y).C] Jet y La n DF

  LieGt : Pt Xm → PsiT D × Bool → Type
  LieB : Pt Xm → PsiT D × Bool → Type
  LieT : Pt Xm → PsiT D × Bool → Type
  [lgAdd : ∀ y σ, AddCommGroup (LieGt y σ)]
  [lbAdd : ∀ y σ, AddCommGroup (LieB y σ)]
  [ltAdd : ∀ y σ, AddCommGroup (LieT y σ)]
  resB : ∀ y σ, LieGt y σ →+ LieB y σ
  incT : ∀ y σ, LieT y σ →+ LieGt y σ

  kapGt : ∀ y σ, LieGt y σ → LieGt y σ → (fld y).C
  kapB : ∀ y σ, LieB y σ → LieB y σ → (fld y).C

  Harm : Pt Xm → Type
  SecP : Pt Xm → Type
  evA : ∀ y, Harm y → SecP y → (fld y).C
  evGt : ∀ y, Harm y → SecP y → (fld y).C

  Tp : ∀ {Z : Mdl}, Pt Z → Type
  [tpAdd : ∀ {Z : Mdl} (y : Pt Z), AddCommGroup (Tp y)]

  OmV : ∀ {Z : Mdl}, Pt Z → Type
  [omAdd : ∀ {Z : Mdl} (y : Pt Z), AddCommGroup (OmV y)]
  [omMod : ∀ {Z : Mdl} (y : Pt Z), Module (fld y).C (OmV y)]
  om : ∀ {Z : Mdl} (y : Pt Z), AddSubgroup (OmV y)

  ht : ∀ {Z : Mdl} (y : Pt Z), Tp y →+ OmV y

  IsHTBlowup : Mdl → Mdl → Prop

  eOmP : ∀ Z : Mdl, Bool → PsiT D → Sh Z

  SES : Mdl → Type
  ExactMod : ∀ {Z : Mdl}, SES Z → ℕ → Prop

  htSES : ∀ Z : Mdl, PsiT D → SES Z

  nefHT : Mdl → (PsiT D → ℕ → ℝ) → Prop

  nefQ : (PsiT D → ℕ → ℝ) → Prop

  descK : Mdl → (PsiT D → ℕ → ℤ) → Prop

  bdryLoci : Mdl → Prop

  BT : ℕ → Type
  extA : ∀ {n}, BT n → Prop
  compat : ∀ {n}, BT n → BT (n + 1) → Prop

  Crv : Type

  eDeg : Crv → ℤ
  Pm : Crv → ℤ
  Pm_nonneg : ∀ c, 0 ≤ Pm c

  degLie : Crv → PsiT D → Bool → ℤ

  degLdR : Crv → (PsiT D → ℕ → ℝ) → ℝ

attribute [instance] Loc.ylAdd Loc.ylMod Loc.ylFree Loc.ylFin Loc.secAdd Loc.atAdd Loc.atFin Loc.thGrp Loc.snAdd
  Loc.snMod Loc.jAdd Loc.jMod Loc.lgAdd
  Loc.lbAdd Loc.ltAdd Loc.tpAdd Loc.omAdd Loc.omMod

section LocDefs

variable {D : Formalism.BasicNotions.D7}

namespace Loc

variable {r j p : ℕ} (L : Loc D r j p)

theorem be_expand {Z : L.Mdl} (y : L.Pt Z) {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ (L.Ylat y))
    (u v : L.Ylat y) : L.be y u v =
      ∑ i, ∑ k, ((b.repr u i : ℤ) : ℝ) * ((b.repr v k : ℤ) : ℝ) * L.be y (b i) (b k) := by
  conv_lhs => rw [← b.sum_repr u, ← b.sum_repr v]

  simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, zsmul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

theorem be_pos {Z : L.Mdl} (y : L.Pt Z) (a : L.Ylat y) (ha : a ≠ 0) : 0 < L.be y a a := by
  obtain ⟨ι, _, b, h⟩ := L.be_posDef y
  rw [L.be_expand y b a a]
  refine h (fun i => ((b.repr a i : ℤ) : ℝ)) fun h0 => ha (b.repr.injective (Finsupp.ext fun i => ?_))
  simpa using congrFun h0 i

private theorem sum4 {A B C E : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype E] (F : A → B → C → E → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e = ∑ c, ∑ e, ∑ a, ∑ b, F a b c e :=
  calc _ = ∑ a, ∑ c, ∑ b, ∑ e, F a b c e := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ e, F a b c e := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ e, ∑ b, F a b c e :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem be_posDef_basis {Z : L.Mdl} (y : L.Pt Z) {κ : Type} [Fintype κ]
    (b' : Module.Basis κ ℤ (L.Ylat y)) (c' : κ → ℝ) (hc : c' ≠ 0) :
    0 < ∑ m, ∑ n, c' m * c' n * L.be y (b' m) (b' n) := by
  classical
  obtain ⟨ι, _, b, h⟩ := L.be_posDef y
  have hne : (fun i => ∑ m, c' m * ((b.repr (b' m) i : ℤ) : ℝ)) ≠ 0 := by
    intro h0
    apply hc
    funext m0
    have hd : ∀ m, ∑ i, ((b.repr (b' m) i : ℤ) : ℝ) * ((b'.repr (b i) m0 : ℤ) : ℝ) = if m = m0 then 1 else 0 := by
      intro m
      have h1 := congrArg (fun v => b'.repr v m0) (b.sum_repr (b' m))

      simp only [map_sum, map_zsmul, Finsupp.finsetSum_apply, Finsupp.smul_apply, Module.Basis.repr_self,
      Finsupp.single_apply, smul_eq_mul] at h1
      have h2 := congrArg (fun z : ℤ => (z : ℝ)) h1
      push_cast at h2
      simpa using h2
    have key : ∑ i, (∑ m, c' m * ((b.repr (b' m) i : ℤ) : ℝ)) * ((b'.repr (b i) m0 : ℤ) : ℝ) = c' m0 := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [mul_assoc, ← Finset.mul_sum, hd]
      simp
    rw [← key]
    exact Finset.sum_eq_zero fun i _ => by rw [congrFun h0 i]; simp
  refine lt_of_lt_of_eq (h _ hne) ?_
  simp only [Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  refine (sum4 _).trans ?_
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  rw [L.be_expand y b (b' m) (b' n), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem gram_posDef {Z : L.Mdl} (y : L.Pt Z) {κ : Type} [Fintype κ] (b' : Module.Basis κ ℤ (L.Ylat y)) :
    (Matrix.of fun m n => L.be y (b' m) (b' n)).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (Matrix.IsHermitian.ext fun m n => by simp [L.be_symm y])
    fun c hc => lt_of_lt_of_eq (L.be_posDef_basis y b' c hc) ?_
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum, Pi.star_apply, star_trivial]
  exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by ring

def good {Z : L.Mdl} (y : L.Pt Z) : Prop := Subsingleton (L.Ylat y)

def beS {Z : L.Mdl} (y : L.Pt Z) : SymB (fun x : D.host.E => D.host.conj x) (L.Ylat y) :=
  ⟨L.be y, L.be_symm y, fun c c' h a b => L.be_bal y c c' h a b⟩

def phiCy {Z : L.Mdl} (y : L.Pt Z) : ℝ := phiC (fun x : D.host.E => D.host.conj x) (L.beS y)

def dP {Z : L.Mdl} (y : L.Pt Z) : ℕ := Module.finrank ℤ (L.Ylat y)

theorem dP_le (h1 : 1 ≤ j) (h2 : j + 1 ≤ r) {Z : L.Mdl} (y : L.Pt Z) : L.dP y ≤ 2 * D.R.f * min j (r - j) := by
  obtain ⟨ρ, h, hb⟩ := L.yl_rank y
  obtain ⟨h3, h4⟩ := hb h1 h2
  rw [dP, h]
  exact Nat.mul_le_mul_left _ (le_min h3 (by omega))

def cJ {Z : L.Mdl} (y : L.Pt Z) (n DF : ℕ) : ℝ :=
  ((L.dP y : ℝ) ^ 5 * (D.R.f : ℝ) ^ 2 * D.host.rdE ^ 2 / 2) * (DF : ℝ) ^ 2 / (n : ℝ)

def SymLift (y : L.Pt L.Xm) (La : L.Unim) (n : ℕ) (sg : L.At y La n → L.Th y La n) : Prop :=
  ∀ x, L.ovr y La n (sg x) = Multiplicative.ofAdd x ∧ L.dl y La n (sg x) = (sg x)⁻¹ ∧ sg x ^ n = 1

def secJet (y : L.Pt L.Xm) (La : L.Unim) (n DF : ℕ) (sg : L.At y La n → L.Th y La n) :
    Set (L.Jet y La n DF) :=
  Set.range fun x => L.jet y La n DF (L.act y La n (sg x) (L.vth y La n))

end Loc

def NHyp (D : Formalism.BasicNotions.D7) (p n : ℕ) : Prop :=
  Odd n ∧ Nat.Coprime n p ∧
    ((∃ mm : ℕ, n = mm ^ 2) ∨ ∃ π : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧
      (π : D.host.E) * D.host.conj (π : D.host.E) = (n : D.host.E))

end LocDefs

section Ext

def bs {D : D7} {r j p : ℕ} (L : Loc D r j p) : Option ℕ → L.Mdl
  | none => L.Xm
  | some n => L.Xn n

structure ExtA (D : D7) {r j p : ℕ} (L : Loc D r j p) where

  FlagData : L.Mdl → Type

  flagCl : ∀ Z, FlagData Z → L.Mdl

  allFlags : FlagData L.Xm

  Idl : L.Mdl → Type

  blowUp : ∀ Z, Idl Z → L.Mdl

  Corr : L.Mdl → L.Mdl → Type

  IvD : Option ℕ → Type

  ZP : L.Mdl → Type

  spz : ∀ {Z}, ZP Z → ZP Z → Prop

  abP : ∀ {Z}, ZP Z → Prop

  inQ : ∀ {Z}, ZP Z → Prop

  isGenP : ∀ {Z}, ZP Z → Prop

  gpt : ∀ {Z}, L.Gen Z → ZP Z
  genNe : ∀ Z, Nonempty (L.Gen Z)

  redK : ∀ Z, L.DVP → ZP Z

  genK : ∀ {Z}, L.Gen Z → L.DVP
  imgM : ∀ {Z y e}, L.Chart Z y e → ZP Z
  imgU : ∀ {Z y e}, L.Chart Z y e → ZP Z
  RFam : ∀ y, L.Ext y → Type

  ptK : ∀ Z, L.DVP → L.Pt Z
  vpi : ∀ {y}, L.Ext y → ℝ
  yEta : ∀ {Z}, L.Gen Z → L.Pt Z
  homSh : ∀ {Z}, L.Sh Z → L.Sh Z → L.Sh Z
  isoSec : ∀ {Z} {F₁ F₂ : L.Sh Z}, L.GIso F₁ F₂ → L.Sec (homSh F₁ F₂)
  isoSymm : ∀ {Z} {F₁ F₂ : L.Sh Z}, L.GIso F₁ F₂ → L.GIso F₂ F₁
  LieV : L.Pt L.YY → Type
  [lvAdd : ∀ y, AddCommGroup (LieV y)]
  [lvMod : ∀ y, Module (L.fld y).C (LieV y)]
  lieL : ∀ y, AddSubgroup (LieV y)
  eig : ∀ y, PsiT D × Bool → Submodule (L.fld y).C (LieV y)
  Wst : ∀ y, PsiT D × Bool → ℕ → Submodule (L.fld y).C (LieV y)
  taut : ∀ y, PsiT D × Bool → ℕ → AddSubgroup (LieV y)
  nrmIn : ∀ l, L.Sec (L.Lb l) → ∀ y : L.Pt L.YY, (PsiT D × Bool → ℕ → AddSubgroup (LieV y)) → ℝ

  TC : ∀ {Z}, L.Pt Z → Type
  [tcAdd : ∀ {Z} (y : L.Pt Z), AddCommGroup (TC y)]
  [tcMod : ∀ {Z} (y : L.Pt Z), Module (L.fld y).C (TC y)]
  iT : ∀ {Z} (y : L.Pt Z), L.Tp y →+ TC y
  htC : ∀ {Z} (y : L.Pt Z), TC y →ₗ[(L.fld y).C] L.OmV y
  HTn : ℕ → Type

  htEval : ∀ {n}, HTn n → ∀ y : L.Pt (L.Xn n), L.Tp y →+ L.OmV y

  htIdl : ∀ {n}, HTn n → Idl (L.Xn n)

  omPat : ∀ {Z} (y : L.Pt Z), AddSubgroup (L.OmV y)

  BPt : L.Mdl → Type
  bfld : ∀ {Z}, BPt Z → CF p
  OmB : ∀ {Z}, BPt Z → Type
  [obAdd : ∀ {Z} (y : BPt Z), AddCommGroup (OmB y)]
  [obMod : ∀ {Z} (y : BPt Z), Module (bfld y).C (OmB y)]
  YsP : L.Mdl → Type
  ysBd : ∀ {Z}, YsP Z → Prop

  FlP : Type
  hFl : ∀ {Z}, YsP Z → FlP
  FlCl : Type
  flMem : FlP → FlCl → Prop
  flDim : FlCl → ℕ

  Sum1 : Type
  locus : Sum1 → FlCl

  CrvS : L.Mdl → Type

  degGr : ∀ {Z}, CrvS Z → PsiT D → ℕ → ℤ

  CrvQ : Type

  degGrQ : CrvQ → PsiT D → ℕ → ℤ

  degGrD : L.Crv → PsiT D → ℕ → ℤ
attribute [instance] ExtA.lvAdd ExtA.lvMod ExtA.tcAdd ExtA.tcMod ExtA.obAdd ExtA.obMod

end Ext

structure Prov (D : Formalism.BasicNotions.D7) where

  Dat : Type
  rk : Dat → ℕ
  jj : Dat → ℕ
  jj_range : ∀ w, 1 ≤ jj w ∧ jj w + 1 ≤ rk w

  loc : ∀ (w : Dat) (p : ℕ), Loc D (rk w) (jj w) p

  ex : ∀ (w : Dat) (p : ℕ), ExtA D (loc w p)

  NgC : ℕ → Type
  NgC_ne : ∀ g, Nonempty (NgC g)

  KF : ℕ → ℕ → Type

  kfNorm : ∀ {g c : ℕ}, KF g c → NgC g → ℝ

  pbKF : ∀ (w : Dat) (p : ℕ) {c : ℕ}, KF (D.R.f * rk w) c → (loc w p).Sec ((loc w p).keySh c)

  levIn : Dat → ℕ → Prop

  Xg : Dat → Type

  bc : ∀ {w} (p : ℕ), Xg w → (loc w p).Mdl

  DivX : ∀ {w}, Xg w → Type

  effD : ∀ {w} {Z : Xg w}, DivX Z → Prop
  noVertD : ∀ {w} {Z : Xg w}, DivX Z → Prop
  posBdD : ∀ {w} {Z : Xg w}, DivX Z → Prop

  ampleOnAbelianBase : ∀ {w} (Z : Xg w), ℕ → DivX Z → Prop

  Met : Dat → Type
  nefFib : ∀ {w}, Met w → Prop
  ampleGen : ∀ {w}, Met w → Prop
  limRA : ∀ {w}, Met w → Prop

variable {D : Formalism.BasicNotions.D7}

def LinkConditions (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop :=
  ∀ w p, p.Prime → ∀ n DF nW : ℕ, NHyp D p n → 3 * DF + 2 ≤ n →
    ∀ y : (X.loc w p).Pt (X.loc w p).Xm,
      (∃ sg, (X.loc w p).SymLift y ((X.loc w p).latStd nW) n sg) ∧
      ∀ sg, (X.loc w p).SymLift y ((X.loc w p).latStd nW) n sg →
      ∃ t : ((X.loc w p).fld y).C,
        (p : ℝ) ^ (-((X.loc w p).cJ y n DF * (X.loc w p).phiCy y)) ≤ ‖t‖ ∧
        ∀ v ∈ (X.loc w p).intJet y ((X.loc w p).latStd nW) n DF,
          t • v ∈ Ospan (C := ((X.loc w p).fld y).C)
            ((X.loc w p).secJet y ((X.loc w p).latStd nW) n DF sg)

end Formalism.MainNotions.ModuliIntegralCharts

end

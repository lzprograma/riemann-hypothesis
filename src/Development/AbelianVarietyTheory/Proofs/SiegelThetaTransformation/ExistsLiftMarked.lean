module

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnFibLift
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrMoveTransfer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitive
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitiveOfLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLiftOfProjective
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToFibPtAndCompFibre
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.Dict GlobalTheory.ClsVal
open scoped ComplexConjugate Classical

namespace GlobalTheory.Dict.MarkLift

section Algebra

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {r : ℕ}

theorem smul_mem_nsmul (l : Geo.Tor.Level H) {s t : 𝓞 E} (hs : s ∈ l.Mb) (ht : t ∈ Mfr l) {N : Type} [AddCommGroup N]
    [Module (𝓞 E) N] (a : N) : ∃ b : 𝓞 E, (s * t) • a = l.M • b • a := by
  have h : s * t ∈ Ideal.span {(l.M : 𝓞 E)} := l.prod ▸ Ideal.mul_mem_mul hs ht
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h
  exact ⟨b, by rw [← hb, ← Nat.cast_smul_eq_nsmul (𝓞 E), smul_smul, mul_comm]⟩

theorem modN_of_mem_bar (l : Geo.Tor.Level H) {t : 𝓞 E} (ht : t ∈ Mfr l) {a : Dw.La}
    (ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) : ∃ b, t • a = l.M • b := by
  refine Submodule.smul_induction_on ha (fun s hs x _ => ?_) ?_
  · obtain ⟨b, hb⟩ := smul_mem_nsmul l hs ht x
    exact ⟨_, by rw [smul_smul, mul_comm, hb]⟩
  · rintro x y ⟨b, hb⟩ ⟨b', hb'⟩
    exact ⟨b + b', by rw [smul_add, smul_add, hb, hb']⟩

theorem modN_of_mem_half (l : Geo.Tor.Level H) {s : 𝓞 E} (hs : s ∈ l.Mb) {N : Type} [AddCommGroup N]
    [Module (𝓞 E) N] {P : Submodule (𝓞 E) N} {a : N} (ha : a ∈ Mfr l • P) : ∃ b ∈ P, s • a = l.M • b := by
  refine Submodule.smul_induction_on ha (fun t ht x hx => ?_) ?_
  · obtain ⟨b, hb⟩ := smul_mem_nsmul l hs ht x
    exact ⟨_, P.smul_mem b hx, by rw [smul_smul, hb]⟩
  · rintro x y ⟨b, h, hb⟩ ⟨b', h', hb'⟩
    exact ⟨b + b', P.add_mem h h', by rw [smul_add, smul_add, hb, hb']⟩

def mults (M : ℕ) (L : Lt E r) : Submodule (𝓞 E) (Fin r → E) := L.map ((M : 𝓞 E) • LinearMap.id)

theorem mem_mults {M : ℕ} {L : Lt E r} {v : Fin r → E} : v ∈ mults M L ↔ ∃ u ∈ L, v = M • u := by
  simp only [mults, Submodule.mem_map, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul]
  exact exists_congr fun u => and_congr_right fun _ => eq_comm

theorem exists_emb {l : Geo.Tor.Level H} {L : Lt E r} {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (h : IsMark l L mk)
    {u v : 𝓞 E} (hu : u ∈ l.Mb) (hv : v ∈ Mfr l) (huv : u + v = 1) :
    ∃ φ : LaMod Dw l →ₗ[𝓞 E] ((Fin r → E) ⧸ mults l.M L), Function.Injective φ ∧
      LinearMap.range φ = (Mfr l • L).map (mults l.M L).mkQ ∧
      ∀ a, φ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (mk (v • a)) := by
  let ψ : Dw.La →ₗ[𝓞 E] ((Fin r → E) ⧸ mults l.M L) := (mults l.M L).mkQ ∘ₗ mk ∘ₗ (v • LinearMap.id)
  have hψ : ∀ a, ψ a = Submodule.Quotient.mk (mk (v • a)) := fun _ => rfl
  have hker : LinearMap.ker ψ = l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
    ext a
    rw [LinearMap.mem_ker, hψ, Submodule.Quotient.mk_eq_zero, mem_mults]
    constructor
    · intro h1
      have h2 := LevelFibre.mem_of_modN l (h.inj _ (Submodule.smul_mem_smul hv trivial) h1)
      have : a = u • a + v • a := by rw [← add_smul, huv, one_smul]
      rw [this]
      exact Submodule.add_mem _ (Submodule.smul_mem_smul hu trivial) h2
    · intro h1
      obtain ⟨b, hb⟩ := modN_of_mem_bar l hv h1
      exact ⟨mk b, h.mem b, by rw [hb, map_nsmul]⟩
  refine ⟨Submodule.liftQ _ ψ hker.ge, ?_, ?_, fun a => hψ a⟩
  · rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hker.le
  · rw [Submodule.range_liftQ]
    ext w
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨mk (v • a), by rw [map_smul]; exact Submodule.smul_mem_smul hv (h.mem a), rfl⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨a, ha, t, ht, rfl⟩ := h.surj w hw
      obtain ⟨b, -, hb⟩ := modN_of_mem_half l hu ha
      refine ⟨a, (Submodule.Quotient.eq _).2 (mem_mults.2 ⟨-(mk b + t), L.neg_mem (L.add_mem (h.mem b) ht), ?_⟩)⟩
      have : a = u • a + v • a := by rw [← add_smul, huv, one_smul]
      have e : mk a = l.M • mk b + mk (v • a) := by rw [← map_nsmul, ← hb, ← map_add (f := _), ← this]
      show mk (v • a) - (mk a + l.M • t) = _
      rw [e, smul_neg, smul_add]
      abel

theorem exists_aut {l l₂ : Geo.Tor.Level H} (hd : l.Dvd l₂) {L : Lt E r} {mk mk₂ mk₃ : Dw.La →ₗ[𝓞 E] (Fin r → E)}
    (h : IsMark l L mk) (h₂ : IsMark l₂ L mk₂) (h₃ : IsMark l₂ L mk₃) (o₂ : MarkOver l l₂ L mk mk₂)
    (o₃ : MarkOver l l₂ L mk mk₃) :
    ∃ k : LaMod Dw l₂ ≃ₗ[𝓞 E] LaMod Dw l₂, (∀ a, liftLa k a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) ∧
      ∀ a ∈ Mfr l₂ • (⊤ : Submodule (𝓞 E) Dw.La), ∃ t ∈ L, mk₃ (liftLa k a) = mk₂ a + l₂.M • t := by
  obtain ⟨u, hu, v, hv, huv⟩ := LevelFibre.level_split l₂
  obtain ⟨φ₂, i₂, r₂, e₂⟩ := exists_emb h₂ hu hv huv
  obtain ⟨φ₃, i₃, r₃, e₃⟩ := exists_emb h₃ hu hv huv
  let k : LaMod Dw l₂ ≃ₗ[𝓞 E] LaMod Dw l₂ := (LinearEquiv.ofInjective φ₂ i₂).trans
    ((LinearEquiv.ofEq _ _ (r₂.trans r₃.symm)).trans (LinearEquiv.ofInjective φ₃ i₃).symm)
  have hk : ∀ q, φ₃ (k q) = φ₂ q := fun q => by
    simp [k]
  have key : ∀ a, ∃ t ∈ L, mk₃ (v • liftLa k a) - mk₂ (v • a) = l₂.M • t := fun a => by
    rw [← mem_mults, ← Submodule.Quotient.eq, ← e₂, ← e₃, ← hk]
    exact congrArg φ₃ (liftLa_spec k a)
  have hs : ∀ a : Dw.La, a = u • a + v • a := fun a => by rw [← add_smul, huv, one_smul]
  refine ⟨k, fun a => ?_, fun a ha => ?_⟩
  · obtain ⟨t, ht, e⟩ := key a
    obtain ⟨t₂, ht₂, f₂⟩ := o₂ (v • a) (Submodule.smul_mem_smul hv trivial)
    obtain ⟨t₃, ht₃, f₃⟩ := o₃ (v • liftLa k a) (Submodule.smul_mem_smul hv trivial)
    obtain ⟨m, hm⟩ := hd.1
    have h1 := LevelFibre.mem_of_modN l (h.inj (v • (liftLa k a - a))
      (Submodule.smul_mem_smul (Ideal.map_mono hd.2.1 hv) trivial)
      ⟨m • t + t₂ - t₃, L.sub_mem (L.add_mem (nsmul_mem ht m) ht₂) ht₃, by
        rw [smul_sub, map_sub, smul_sub, smul_add, smul_smul, ← hm, ← e, f₂, f₃]
        abel⟩)
    rw [hs (liftLa k a - a)]
    exact Submodule.add_mem _ (Submodule.smul_mem_smul (hd.2.1 hu) trivial) h1
  · obtain ⟨t, ht, e⟩ := key a
    have ha' : liftLa k a ∈ Mfr l₂ • (⊤ : Submodule (𝓞 E) Dw.La) := by
      have := Submodule.mem_map_of_mem (f := liftLa k) ha
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    obtain ⟨b, -, hb⟩ := modN_of_mem_half l₂ hu ha
    obtain ⟨b', -, hb'⟩ := modN_of_mem_half l₂ hu ha'
    refine ⟨t + mk₃ b' - mk₂ b, L.sub_mem (L.add_mem ht (h₃.mem _)) (h₂.mem _), ?_⟩
    have g₂ : mk₂ a = l₂.M • mk₂ b + mk₂ (v • a) := by rw [← map_nsmul, ← hb, ← map_add (f := _), ← hs]
    have g₃ : mk₃ (liftLa k a) = l₂.M • mk₃ b' + mk₃ (v • liftLa k a) := by rw [← map_nsmul, ← hb', ← map_add (f := _), ← hs]
    rw [g₂, g₃, smul_sub, smul_add, ← e]
    abel

end Algebra

section Geometry

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l₂ : Geo.Tor.Level H}
  {Xo : Moduli D l} {Xo₂ : Moduli D l₂}

theorem rho_eq (hpq : D.p ≠ D.q) {r : Xo₂.X ⟶ Xo.X} (m : SABMap Xo₂.univ.t Xo.univ.t r) {x : Sp ℂ ⟶ Xo₂.X}
    {β : KA l →+* ℂ} {β₂ : KA l₂ →+* ℂ} (h : (x ≫ r) ≫ Xo.s = Geo.Tor.spMap β) (h₂ : x ≫ Xo₂.s = Geo.Tor.spMap β₂) :
    β (baseKA l).ρ = β₂ (baseKA l₂).ρ := by
  by_contra hne
  obtain ⟨o, ⟨p⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s ((x ≫ r) ≫ Xo.s) (x ≫ r)
    rfl rfl (by rw [LevelFibre.spMap_id', Category.comp_id]) Xo.univ
  have d₁ := (Xo.univ.geom ℂ (x ≫ r) β h).1
  have d₂ := (Xo₂.univ.geom ℂ x β₂ h₂).1
  have uniq : ∀ τ n n', LieMult Xo.univ.t.act (x ≫ r) τ n → LieMult Xo₂.univ.t.act x τ n' → n = n' := by
    intro τ n n' a b
    rw [LiePull.lieMult_pull _ _ _ _ _ r m.φ Xo.univ.t.act Xo₂.univ.t.act m.cart m.act] at b
    have t : ∀ k, LieMult Xo.univ.t.act (x ≫ r) τ k → LieMult o.t.act (𝟙 _) τ k := fun k hk => by
      rw [LiePull.lieMult_pull _ _ _ _ _ (x ≫ r) p.toSABMap.φ Xo.univ.t.act o.t.act p.cart p.act, Category.id_comp]
      exact hk
    obtain ⟨v⟩ := (GlobalTheory.Serre.Lie.lieMult_id_iff o.t.act τ n).mp (t _ a)
    obtain ⟨v'⟩ := (GlobalTheory.Serre.Lie.lieMult_id_iff o.t.act τ n').mp (t _ b)
    simpa using (Module.finrank_eq_card_basis v).symm.trans (Module.finrank_eq_card_basis v')
  let τ : 𝓞 E →+* ℂ := ((IsAlgClosed.lift : E →ₐ[ℚ] ℂ) : E →+* ℂ).comp (algebraMap (𝓞 E) E)
  have s₀ : τ H.rt ^ 2 = -(H.d : ℂ) := by rw [← map_pow, H.rt_sq]; simp
  have s₁ : β (baseKA l).ρ ^ 2 = -(H.d : ℂ) := by rw [← map_pow, (baseKA l).ρ_sq]; simp
  have s₂ : β₂ (baseKA l₂).ρ ^ 2 = -(H.d : ℂ) := by rw [← map_pow, (baseKA l₂).ρ_sq]; simp
  by_cases ht : τ H.rt = β (baseKA l).ρ
  · exact hpq (uniq τ _ _ ((d₁ τ).1 ht) ((d₂ τ).2 (ht ▸ hne)))
  · have a := (sq_eq_sq_iff_eq_or_eq_neg.mp (s₀.trans s₁.symm)).resolve_left ht
    have b := (sq_eq_sq_iff_eq_or_eq_neg.mp (s₁.trans s₂.symm)).resolve_left hne
    exact hpq (uniq τ _ _ ((d₁ τ).2 ht) ((d₂ τ).1 (by rw [a, b, neg_neg]))).symm

theorem emb_ext (hA : l.A = 1) {β β' : KA l →+* ℂ} (h : β (baseKA l).ρ = β' (baseKA l).ρ) : β = β' := by
  have hz : zeta l.A = 1 := by rw [hA, zeta]; simp [Complex.exp_two_pi_mul_I]
  have := IntermediateField.algHom_ext_of_eq_adjoin ℚ (S := KA l) (s := {H.rt0, zeta l.A}) rfl
    (φ₁ := β.toRatAlgHom) (φ₂ := β'.toRatAlgHom) (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with (rfl | rfl)
      · exact h
      · have e : ∀ hx, (⟨zeta l.A, hx⟩ : KA l) = 1 := fun hx => Subtype.ext hz
        rw [e]
        exact β.map_one.trans β'.map_one.symm)
  exact RingHom.ext fun a => DFunLike.congr_fun this a


open OverMove in
theorem move_fibre {r : Xo₂.X ⟶ Xo.X} {m : SABMap Xo₂.univ.t Xo.univ.t r} (hm : Lev m) {ρ : Xo₂.X ⟶ Xo₂.X}
    {ν : SABMap Xo₂.univ.t Xo₂.univ.t ρ} {f : D.La →ₗ[𝓞 E] D.La} (hν : IsLevMove ρ ν f LinearMap.id)
    (hf : ∀ a, f a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) {x : Sp ℂ ⟶ Xo₂.X} {z : Sp ℂ ⟶ Xo.X} (hz : x ≫ r = z)
    (hs : ((x ≫ ρ) ≫ r) ≫ Xo.s = z ≫ Xo.s) :
    (x ≫ ρ) ≫ r = z ∧
      ∀ a, ((x ≫ ρ) ≫ (Xo₂.univ.eta a).left) ≫ m.φ = (x ≫ (Xo₂.univ.eta (f a)).left) ≫ m.φ := by
  obtain ⟨o, ⟨p⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (z ≫ Xo.s) z rfl rfl
    (by rw [LevelFibre.spMap_id', Category.comp_id]) Xo.univ
  obtain ⟨n, hn, F⟩ := exists_fib p hm hz
  obtain ⟨n₂, hn₂⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν n
  have hn₂' : n₂.φ = n.φ ≫ ν.φ := hn₂
  have hfix : ∀ a, (Xo₂.univ.eta (f a) ^ (l₂.M / l.M)).left = (Xo₂.univ.eta a ^ (l₂.M / l.M)).left := fun a => by
    apply m.cart.1.hom_ext
    · refine (hm.1 _).trans (Eq.trans ?_ (hm.1 _).symm)
      rw [← sub_add_cancel (f a) a, Xo.univ.eta_add, Xo.univ.eta_ker _ (hf a), _root_.one_mul]
    · rw [LevelFibre.sec_w, LevelFibre.sec_w]
  have F₂ : Fib o n₂ := ⟨fun a => by
      rw [hn₂', ← Category.assoc, F.1, ← hfix, Category.assoc x, pow_left_comp ν (hν.2.1 a), hfix, Category.assoc],
    fun a => by
      rw [hn₂', ← Category.assoc, F.2, Category.assoc x, pow_left_comp ν (σ := Xo₂.univ.etaA a) (hν.2.2 a), Category.assoc]⟩
  obtain ⟨q, hq⟩ := exists_objMap F₂ hm
  have e : (x ≫ ρ) ≫ r = z := (Xo.rep (Sp ℂ) (z ≫ Xo.s) inferInstance o).unique ⟨hs, ⟨q⟩⟩ ⟨rfl, ⟨p⟩⟩
  refine ⟨e, fun a => ?_⟩
  obtain ⟨q', hq'⟩ := LevelFibre.sab_cast e q.toSABMap
  have e₂ : q'.φ = p.toSABMap.φ := _root_.GlobalTheory.obj_rigid_of_laws firstFiveLaws.1 obj_isAbelianScheme_dim_rigidified_sym E H D l
    _ _ _ _ _ _ _ _ Xo.univ o _ (Or.inl inferInstance) q' p.toSABMap fun a =>
      ⟨_, by rw [hq']; exact (q.eta a).trans (by rw [e]), p.eta a⟩
  rw [hq', hq, hn₂', ← hn] at e₂
  obtain ⟨s, hs⟩ : ∃ s : Sp ℂ ⟶ o.t.G.left, s ≫ n.φ = x ≫ (Xo₂.univ.eta (f a)).left :=
    ⟨_, n.cart.1.lift_fst _ (𝟙 _) (by rw [Category.assoc, LevelFibre.sec_w]; simp)⟩
  rw [Category.assoc x ρ, ← hν.2.1, ← Category.assoc x, ← hs, Category.assoc, Category.assoc, Category.assoc,
    ← Category.assoc n.φ, e₂]

end Geometry


open GlobalTheory.Dict.Lift in
theorem anFib_lift_ex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [Algebra c.F ℂ] [Algebra d.c₂.F ℂ], (∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t) → d.IsLev → ∀ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ y₂ : FrPt d.Xo₂ d.c₂ ℂ, FrOver d y₂ y → ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), A.Marked mk → ∃ A₂ : AnFib X bas idx e x L y₂, (∀ z, (A₂.ex z).left ≫ d.m.φ = (A.ex z).left) ∧ (∀ θ, A.Reads 1 y.s θ → A₂.Reads 1 y₂.s θ) ∧ ∃ mk₂ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark d.l₂ L mk₂ ∧ A₂.Marked mk₂ ∧ MarkOver l d.l₂ L mk mk₂ :=
  GlobalTheory.Dict.Lift.anFib_lift_ex

theorem exists_lift_marked : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [Algebra c.F ℂ] [Algebra d.c₂.F ℂ], (∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t) → d.IsLev → l.A = 1 → d.l₂.A = 1 → (Dw.p = Dw.q → ∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ Geo.Tor.spMap (IntermediateField.inclusion h).toRingHom) → ∀ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ mk mk₂ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → A.Marked mk → IsMark d.l₂ L mk₂ → MarkOver l d.l₂ L mk mk₂ → ∃ (y₂ : FrPt d.Xo₂ d.c₂ ℂ) (A₂ : AnFib X bas idx e x L y₂), FrOver d y₂ y ∧ A₂.Marked mk₂ ∧ ∀ θ, A.Reads 1 y.s θ → A₂.Reads 1 y₂.s θ := by
  intro E _ _ _ H Dw l Xo c n d _ _ hk hlev hA hA₂ hK r g X bas idx e x L y A hsym hx hL mk mk₂ hm hmk hm₂ ho₂
  obtain ⟨y₃, h₃⟩ := hlev.2.2.2.2.2.2.1 ℂ hk y
  obtain ⟨A₃, ex₃, rd₃, mk₃, hm₃, hmk₃, ho₃⟩ := anFib_lift_ex E H Dw l Xo c n d hk hlev r g X bas idx e x L y A hsym
    hx hL y₃ h₃ mk hmk
  rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with h0 | hpq
  · haveI := Dw.fin
    haveI := Dw.proj
    haveI : Subsingleton Dw.La := Module.finrank_zero_iff.1 (Dw.rank.trans h0)
    have : mk₂ = mk₃ := LinearMap.ext fun a => by rw [Subsingleton.elim a 0, map_zero, map_zero]
    exact ⟨y₃, A₃, h₃, this ▸ hmk₃, rd₃⟩
  obtain ⟨hd, hM, -, -, -, hE, -⟩ := id hlev
  obtain ⟨k, hk₁, hk₂⟩ := exists_aut hd hm hm₂ hm₃ ho₂ ho₃
  obtain ⟨ρ, ν, -, hν⟩ := LevelActionLaws.exists_move hpq (by rw [hA₂]; exact Nat.coprime_one_left _) d.Xo₂ k
  have hpd : d.pd = d.l₂.M / l.M := by
    rw [hM, Nat.mul_div_cancel_left _ (lt_of_lt_of_le (by norm_num) l.three_le)]
  have L₁ : OverMove.Lev d.m := ⟨hpd ▸ hE.1, hE.2⟩
  have hx₂ : (y₃.x ≫ ρ) ≫ d.Xo₂.s = sOf d.c₂ ℂ := by rw [Category.assoc, hν.1, y₃.x_over]
  have hs : ((y₃.x ≫ ρ) ≫ d.r) ≫ Xo.s = y.x ≫ Xo.s := by
    by_cases hpq' : Dw.p = Dw.q
    · have hle : KA l ≤ KA d.l₂ := by rw [KA, KA, hA, hA₂]
      rw [← h₃.1, Category.assoc _ d.r, Category.assoc _ d.r, hK hpq' hle, ← Category.assoc, ← Category.assoc y₃.x,
        hx₂, y₃.x_over]
    · obtain ⟨β, hβ⟩ := LevelFibre.exists_spMap (((y₃.x ≫ ρ) ≫ d.r) ≫ Xo.s)
      have a₁ := rho_eq hpq' d.m hβ hx₂
      have a₂ := rho_eq hpq' d.m (x := y₃.x) (by rw [h₃.1]; exact y.x_over) y₃.x_over
      rw [hβ, emb_ext hA (a₁.trans a₂.symm)]
      exact y.x_over.symm
  obtain ⟨hb, hη⟩ := move_fibre L₁ hν hk₁ h₃.1 hs
  obtain ⟨y₂, hy₂, h₂⟩ := (frames_lift_to_cover firstFiveLaws.1 E H Dw l Xo c n d).1 ℂ hk y _ hb hx₂
  obtain ⟨A₂, ex₂, rd₂, -⟩ := anFib_lift_ex E H Dw l Xo c n d hk hlev r g X bas idx e x L y A hsym
    hx hL y₂ h₂ mk hmk
  refine ⟨y₂, A₂, h₂, fun a ha => ?_, rd₂⟩
  have ha' : liftLa k a ∈ Mfr d.l₂ • (⊤ : Submodule (𝓞 E) Dw.La) := by
    have := Submodule.mem_map_of_mem (f := liftLa k) ha
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  obtain ⟨t, ht, e₁⟩ := hk₂ a ha
  have hM0 : (d.l₂.M : E) ≠ 0 := Nat.cast_ne_zero.2 (LevelFibre.level_pos d.l₂).ne'
  have e₂ : A.ex (pv X idx x ((d.l₂.M : E)⁻¹ • mk₃ (liftLa k a))) = A.ex (pv X idx x ((d.l₂.M : E)⁻¹ • mk₂ a)) := by
    rw [e₁, smul_add, ← Nat.cast_smul_eq_nsmul E, smul_smul, inv_mul_cancel₀ hM0, one_smul, pv, per_add]
    exact (A.ex_add (pv X idx x _) (pv X idx x t)).trans (by rw [(A.ex_ker _).2 ⟨t, ht, rfl⟩, _root_.mul_one])
  apply Over.OverMorphism.ext
  apply d.m.cart.1.hom_ext
  · refine Eq.trans ?_ (ex₂ _).symm
    rw [← e₂, ← ex₃, ← hmk₃ _ ha', levPt, levPt, LevelFibre.unit_left, LevelFibre.unit_left]
    exact (congrArg (fun w => (w ≫ (d.Xo₂.univ.eta a).left) ≫ d.m.φ) hy₂).trans (hη a)
  · rw [Over.w, Over.w]

end GlobalTheory.Dict.MarkLift

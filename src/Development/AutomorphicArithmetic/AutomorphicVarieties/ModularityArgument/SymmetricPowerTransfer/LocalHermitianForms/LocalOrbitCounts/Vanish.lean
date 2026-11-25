module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LcountNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Descent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SqrtO
import Mathlib.Algebra.QuadraticAlgebra.IsQuadraticExtension
import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.LinearAlgebra.FreeModule.PID

@[expose] public section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc Matrix

private theorem vanish_det {O K : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (B : Matrix (Fin 3) (Fin 3) K) (hB : B.det ≠ 0) (S : Submodule O (Fin 3 → K)) (hfg : S.FG)
    (hd : ∀ y, y ∈ S ↔ ∀ x ∈ S, x ⬝ᵥ B *ᵥ y ∈ (algebraMap O K).range) :
    ∃ (u : Oˣ) (s : K), s ≠ 0 ∧ B.det = algebraMap O K u * s ^ 2 := by
  classical
  have finj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have : Module.Finite O S := Module.Finite.iff_fg.mpr hfg
  have : Module.Free O S := Module.free_of_finite_type_torsion_free'
  let b₀ := Module.Free.chooseBasis O S
  let v₀ : _ → Fin 3 → K := fun i => b₀ i
  have hSv₀ : Submodule.span O (Set.range v₀) = S := by
    rw [show Set.range v₀ = S.subtype '' Set.range b₀ by rw [← Set.range_comp]; rfl, Submodule.span_image, b₀.span_eq, Submodule.map_subtype_top]
  have mem_of_basis (z : Fin 3 → K) (h : ∀ i, v₀ i ⬝ᵥ B *ᵥ z ∈ (algebraMap O K).range) : z ∈ S :=
    (hd z).2 fun x hx => Submodule.span_induction (p := fun x _ => x ⬝ᵥ B *ᵥ z ∈ (algebraMap O K).range)
      (by rintro _ ⟨i, rfl⟩; exact h i) (by simp) (fun _ _ _ _ h1 h2 => by rw [add_dotProduct]; exact add_mem h1 h2)
      (fun r _ _ h1 => by rw [smul_dotProduct, Algebra.smul_def]; exact mul_mem ⟨r, rfl⟩ h1) (hSv₀.symm ▸ hx)
  have hliK : LinearIndependent K v₀ :=
    (LinearIndependent.iff_fractionRing O K).1 (b₀.linearIndependent.map' S.subtype (Submodule.ker_subtype S))
  have hspK : ⊤ ≤ Submodule.span K (Set.range v₀) := fun y _ => by
    obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O) (Finset.univ.image fun i => v₀ i ⬝ᵥ B *ᵥ y)
    have hay : (c : O) • y ∈ S := mem_of_basis _ fun i =>
      let ⟨r, hr⟩ := hc _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)); ⟨r, by rw [hr, Matrix.mulVec_smul, dotProduct_smul]⟩
    have hc0 : algebraMap O K (c : O) ≠ 0 := (map_ne_zero_iff _ finj).2 (nonZeroDivisors.ne_zero c.2)
    rw [show y = (algebraMap O K (c : O))⁻¹ • (c : O) • y by rw [← algebraMap_smul K (c : O) y, smul_smul, inv_mul_cancel₀ hc0, one_smul]]
    exact Submodule.smul_mem _ _ (Submodule.span_le_restrictScalars O K _ (hSv₀.symm ▸ hay))
  let e := Fintype.equivFinOfCardEq (by rw [← Module.finrank_eq_card_basis (Module.Basis.mk hliK hspK), Module.finrank_fin_fun])
  let b : Module.Basis (Fin 3) O S := b₀.reindex e
  let V : Matrix (Fin 3) (Fin 3) K := Matrix.of fun r j => (b j : Fin 3 → K) r
  have hVu : IsUnit V := (Matrix.linearIndependent_col_iff_isUnit (A := V)).1 <| by
    rw [show V.col = v₀ ∘ e.symm from funext fun j => funext fun r => by simp [V, b]; rfl]; exact hliK.comp e.symm e.symm.injective
  have hVd : V.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det V).1 hVu).ne_zero
  have mul_ent (W : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) : (V.transpose * B * W) i j = (b i : Fin 3 → K) ⬝ᵥ B *ᵥ fun r => W r j := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum, V, Matrix.of_apply]
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  choose g hg using fun i j => mul_ent V i j ▸ (hd (b j)).1 (b j).2 (b i) (b i).2
  let Gi : Matrix (Fin 3) (Fin 3) O := Matrix.of g
  have hGi : (algebraMap O K).mapMatrix Gi = V.transpose * B * V := Matrix.ext fun i j => by simp [Gi, hg]
  let Y := (V.transpose * B)⁻¹
  have hMY : V.transpose * B * Y = 1 := Matrix.mul_nonsing_inv _ (Ne.isUnit (by rw [Matrix.det_mul, Matrix.det_transpose]; exact mul_ne_zero hVd hB))
  have hyS (j : Fin 3) : (fun r => Y r j) ∈ S := mem_of_basis _ fun i => by
    rw [show v₀ i ⬝ᵥ B *ᵥ (fun r => Y r j) = (V.transpose * B * Y) (e i) j by simpa [b] using (mul_ent Y (e i) j).symm, hMY, Matrix.one_apply]
    split_ifs <;> [exact ⟨1, map_one _⟩; exact ⟨0, map_zero _⟩]
  let C : Matrix (Fin 3) (Fin 3) O := Matrix.of fun k j => b.repr ⟨_, hyS j⟩ k
  have hYC : Y = V * (algebraMap O K).mapMatrix C := Matrix.ext fun r j => by
    have h := congrArg (fun z : S => (z : Fin 3 → K) r) (b.sum_repr ⟨_, hyS j⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Algebra.smul_def] at h
    simpa [Matrix.mul_apply, C, V, mul_comm] using h.symm
  have hGu : IsUnit Gi.det := isUnit_iff_exists_inv.2 ⟨C.det, finj (by
    rw [map_mul, RingHom.map_det, RingHom.map_det, ← Matrix.det_mul, hGi, Matrix.mul_assoc (V.transpose * B), ← hYC, hMY, Matrix.det_one, map_one])⟩
  refine ⟨hGu.unit, V.det⁻¹, inv_ne_zero hVd, ?_⟩
  have h1 : algebraMap O K (hGu.unit : O) = V.det * B.det * V.det := by
    rw [IsUnit.unit_spec, RingHom.map_det, hGi, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  rw [h1]; field_simp

private theorem vanish_unit {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    {Δ : K} (hl : IsLoc O Δ) (hΔ : ¬ IsSquare Δ) (l : Lsq K Δ) (hl0 : l ≠ 0) :
    ∃ (k : K) (u : (integralClosure O (Lsq K Δ))ˣ), k ≠ 0 ∧ l = algebraMap K _ k * (u : Lsq K Δ) := by
  classical
  have := hl.frac
  obtain ⟨ε, s, hs0, hΔs⟩ := hl.even
  have hdesc : Δ * s⁻¹ ^ 2 = algebraMap O K ε := by rw [hΔs]; field_simp
  have D x := (descent O K Δ hl s⁻¹ ε hdesc x).1
  have unitN (A B : O) (hAB : IsUnit A ∨ IsUnit B) : IsUnit (A ^ 2 - (ε : O) * B ^ 2) := by
    by_contra hn
    have hm : A ^ 2 - (ε : O) * B ^ 2 ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hn)
    have hB : IsUnit B := hAB.elim (fun hA => by_contra fun hB => IsLocalRing.notMem_maximalIdeal.2 (hA.pow 2) <| by
      have hA2 := Ideal.add_mem _ hm (Ideal.mul_mem_left _ (ε : O) (Ideal.pow_mem_of_mem _ ((IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hB)) 2 (by norm_num)))
      rwa [sub_add_cancel] at hA2) id
    have hA : IsUnit A := hAB.elim id fun hB => by_contra fun hA => IsLocalRing.notMem_maximalIdeal.2 (ε.isUnit.mul (hB.pow 2)) <| by
      have hB2 := Ideal.sub_mem _ (Ideal.pow_mem_of_mem _ ((IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hA)) 2 (by norm_num)) hm
      rwa [sub_sub_cancel] at hB2
    obtain ⟨r, hr, -⟩ := sqrtO O K Δ hl (ε : O) (A * ↑hB.unit⁻¹) (hA.mul (Units.isUnit _)) (by
      rw [show (ε : O) - (A * ↑hB.unit⁻¹) ^ 2 = -(↑hB.unit⁻¹ : O) ^ 2 * (A ^ 2 - (ε : O) * B ^ 2) by
        linear_combination (-(ε : O) * (B * ↑hB.unit⁻¹ + 1)) * hB.mul_val_inv]
      exact Ideal.mul_mem_left _ _ hm)
    exact hΔ ⟨algebraMap O K r * s, by rw [hΔs, ← hr, map_pow]; ring⟩
  have mk (A B : O) (hAB : IsUnit A ∨ IsUnit B) (k : K) (hk : k ≠ 0)
      (hre : l.re = k * algebraMap O K A) (him : l.im = k * (s⁻¹ * algebraMap O K B)) :
      ∃ (k : K) (u : (integralClosure O (Lsq K Δ))ˣ), k ≠ 0 ∧ l = algebraMap K _ k * (u : Lsq K Δ) := by
    obtain ⟨w, hw⟩ := unitN A B hAB
    let u : Lsq K Δ := ⟨algebraMap O K A, s⁻¹ * algebraMap O K B⟩
    let u' : Lsq K Δ := ⟨algebraMap O K (A * ↑w⁻¹), s⁻¹ * algebraMap O K (-B * ↑w⁻¹)⟩
    have huu : u * u' = 1 := by
      have hwK : algebraMap O K (↑w) * algebraMap O K (↑w⁻¹ : O) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
      have hwv : algebraMap O K ↑w = (algebraMap O K A) ^ 2 - Δ * (s⁻¹ * algebraMap O K B) ^ 2 := by
        rw [hw, map_sub, map_mul, map_pow, map_pow, ← hdesc]; ring
      ext <;> simp only [u, u', QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, map_mul, map_neg]
      · linear_combination (-(algebraMap O K (↑w⁻¹ : O))) * hwv + hwK
      · ring
    exact ⟨k, ⟨⟨u, (D _).2 ⟨⟨A, rfl⟩, B, rfl⟩⟩, ⟨u', (D _).2 ⟨⟨_, rfl⟩, _, rfl⟩⟩,
      Subtype.ext huu, Subtype.ext (by show u' * u = 1; rw [mul_comm]; exact huu)⟩, hk, by ext <;> simp [u, hre, him]⟩
  by_cases hc : l.re ≠ 0 ∧ IsLocalization.IsInteger O (l.im * s / l.re)
  · obtain ⟨ha, B, hB⟩ := hc; exact mk 1 B (.inl isUnit_one) l.re ha (by simp) (by rw [hB]; field_simp)
  · have hβ : l.im * s ≠ 0 := fun h0 => hc ⟨fun hre0 => hl0 (QuadraticAlgebra.ext hre0 ((mul_eq_zero.mp h0).resolve_right hs0)), 0, by simp [h0]⟩
    obtain ⟨A, hA⟩ : IsLocalization.IsInteger O (l.re / (l.im * s)) := by
      by_cases ha : l.re = 0
      · exact ⟨0, by simp [ha]⟩
      · exact (ValuationRing.isInteger_or_isInteger O (l.im * s / l.re)).elim (fun h => absurd ⟨ha, h⟩ hc) (by simp [inv_div])
    exact mk A 1 (.inr isUnit_one) (l.im * s) hβ (by have := left_ne_zero_of_mul hβ; rw [hA]; field_simp) (by simp only [map_one, mul_one]; field_simp)

theorem UpperTheory.V.Z.Sym.Loc.vanish :
    UpperTheory.V.Z.Sym.Loc.Vanish := by
  intro O K _ _ _ _ _ Δ τ hL c d m hD hc
  obtain ⟨S, hS⟩ : ∃ S, IsFix O c d m S := by
    by_contra hno; push Not at hno; apply hc; unfold lcount wcount; exact finsum_eq_zero_of_forall_eq_zero fun o => by simp [hno]
  have sigL_mul (x y : EL Δ τ) : sigL (x * y) = sigL x * sigL y := by
    have hτ : star (algebraMap K (Lsq K Δ) τ) = algebraMap K (Lsq K Δ) τ := by ext <;> simp
    apply QuadraticAlgebra.ext <;> [simp [sigL, star_mul', star_add, star_neg]; simp [sigL, star_mul', star_add, hτ]]
  have sigL_idem (x : EL Δ τ) : sigL (sigL x) = x := by ext <;> simp [sigL]
  have hsem (y : Sp Δ τ) : semi d (semi d y) = (y.1, ofE Δ ω * y.2) := by simp only [semi, star_star, sigL_mul, sigL_idem, ← mul_assoc, hD.d_norm]
  have hτ2 : τ - 2 ≠ 0 := fun h => hD.reg (by rw [sub_eq_zero.1 h]; norm_num)
  have := hL.frac
  obtain ⟨s, hs⟩ := hS.fg
  let M : Submodule O (Sp Δ τ) := Submodule.span O (s : Set (Sp Δ τ))
  have memM (y : Sp Δ τ) : y ∈ S ↔ y ∈ M := by rw [hs]; rfl
  have inS (y : Sp Δ τ) (hy : y ∈ S) : semi d y ∈ S := by have := Set.mem_image_of_mem (semi d) hy; rwa [hS.stab] at this
  have preS (y : Sp Δ τ) (hy : y ∈ S) : ∃ z ∈ S, semi d z = y := by rwa [← hS.stab] at hy
  have hω1 : (ofE Δ ω : EL Δ τ) = ⟨0, 1⟩ := by ext <;> simp [ofE]
  have hω2 : ofE Δ ω * ofE Δ ω = algebraMap K (EL Δ τ) τ * ofE Δ ω - 1 := by
    rw [hω1, show algebraMap K (EL Δ τ) τ = ⟨algebraMap K (Lsq K Δ) τ, 0⟩ from rfl]; ext <;> simp
  have hV (y : Sp Δ τ) (hy : y ∈ S) : ((0 : Lsq K Δ), algebraMap K (EL Δ τ) (τ - 2) * y.2) ∈ S := by
    obtain ⟨z1, hz1, rfl⟩ := preS y hy; obtain ⟨z, hz, rfl⟩ := preS z1 hz1
    have key : ((0 : Lsq K Δ), algebraMap K (EL Δ τ) (τ - 2) * (semi d (semi d z)).2) =
        semi d (semi d (semi d (semi d z))) + z - (semi d (semi d z) + semi d (semi d z)) := by
      simp only [hsem]; exact Prod.ext (by simp) (by simp only [Prod.snd_add, Prod.snd_sub, map_sub, map_ofNat]; linear_combination (-z.2) * hω2)
    rw [key, memM]
    exact M.sub_mem (M.add_mem ((memM _).1 (inS _ (inS _ hy))) ((memM _).1 hz)) (M.add_mem ((memM _).1 hy) ((memM _).1 hy))
  have hex : ∃ y ∈ S, y.2 ≠ 0 := by
    by_contra hno; push Not at hno
    exact one_ne_zero (hno ((0 : Lsq K Δ), (1 : EL Δ τ)) ((hS.dual _).2 fun x hx => by simp [herm, hno x hx]; exact isIntegral_zero))
  have hint : IsIntegral O (τ - 2) := by
    obtain ⟨y, hy, hy2⟩ := hex
    refine isIntegral_of_smul_mem_submodule (M ⊓ LinearMap.ker (LinearMap.fst O (Lsq K Δ) (EL Δ τ)))
      (fun hbot => ?_) (Submodule.FG.of_le ⟨s, rfl⟩ inf_le_left) (τ - 2) fun n ⟨hn1, hn2⟩ => ?_
    · have hmem : ((0 : Lsq K Δ), algebraMap K (EL Δ τ) (τ - 2) * y.2) ∈ M ⊓ LinearMap.ker (LinearMap.fst O (Lsq K Δ) (EL Δ τ)) :=
        ⟨(memM _).1 (hV y hy), by simp⟩
      rw [hbot, Submodule.mem_bot] at hmem
      exact hy2 (((isUnit_iff_ne_zero.2 hτ2).map (algebraMap K (EL Δ τ))).mul_right_eq_zero.1 (congrArg Prod.snd hmem))
    · have hn0 : n.1 = 0 := by simpa using hn2
      rw [show (τ - 2) • n = ((0 : Lsq K Δ), algebraMap K (EL Δ τ) (τ - 2) * n.2) from
        Prod.ext (by rw [Prod.smul_fst, hn0, smul_zero]) (by rw [Prod.smul_snd, Algebra.smul_def])]
      exact ⟨(memM _).1 (hV n ((memM _).2 hn1)), by simp⟩
  obtain ⟨o, ho⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hωs : ofE Δ ω * star (ofE Δ ω) = (1 : EL Δ τ) := by rw [hω1]; ext <;> simp
  have hωu : IsUnit (ofE Δ ω : EL Δ τ) := ⟨⟨_, _, hωs, by rw [mul_comm]; exact hωs⟩, rfl⟩
  let ν : EL Δ τ := m * star (sigL d)
  have hνs : star ν = ν * ofE Δ ω := by
    have hsm : sigL m = star m := by simpa using congrArg star hD.m_star
    rw [show ν = m * star (sigL d) from rfl, star_mul', star_star, ← hsm, hD.m_sig, ← hD.d_norm]; ring
  have hp : ν.re = -ν.im - algebraMap K (Lsq K Δ) τ * ν.im := by
    have := congrArg QuadraticAlgebra.re hνs; rw [hω1] at this; simp at this; linear_combination this
  have hN : QuadraticAlgebra.norm ν = ν.im ^ 2 * (2 + algebraMap K (Lsq K Δ) τ) := by rw [QuadraticAlgebra.norm_def, hp]; ring
  have hNu : IsUnit (ν.im ^ 2 * (2 + algebraMap K (Lsq K Δ) τ)) :=
    hN ▸ (hD.m_unit.mul (isUnit_of_mul_isUnit_right (hD.d_norm ▸ hωu)).star).map QuadraticAlgebra.norm
  let t : Lsq K Δ := (2 + algebraMap K (Lsq K Δ) τ) * ν.im
  have htu : IsUnit t := (isUnit_of_mul_isUnit_right hNu).mul ((isUnit_pow_iff two_ne_zero).1 (isUnit_of_mul_isUnit_left hNu))
  let Φ : Sp Δ τ ≃ₗ[O] (Fin 3 → Lsq K Δ) :=
    { toFun := fun x => ![x.1, x.2.re, x.2.im], invFun := fun v => (v 0, ⟨v 1, v 2⟩)
      left_inv := fun _ => rfl, right_inv := fun v => funext fun i => by fin_cases i <;> rfl
      map_add' := fun _ _ => funext fun i => by fin_cases i <;> simp, map_smul' := fun _ _ => funext fun i => by fin_cases i <;> simp }
  let B : Matrix (Fin 3) (Fin 3) (Lsq K Δ) :=
    !![algebraMap K (Lsq K Δ) c, 0, 0;
      0, 2 * ν.re + algebraMap K (Lsq K Δ) τ * ν.im, algebraMap K (Lsq K Δ) τ * ν.re + 2 * ν.im;
      0, algebraMap K (Lsq K Δ) τ * ν.re + (algebraMap K (Lsq K Δ) τ ^ 2 - 2) * ν.im, 2 * ν.re + algebraMap K (Lsq K Δ) τ * ν.im]
  have hid (x y : Sp Δ τ) : Φ x ⬝ᵥ B *ᵥ Φ y = herm c m x (semi d y) := by
    have e1 : herm c m x (semi d y) = algebraMap K (Lsq K Δ) c * x.1 * y.1 + QuadraticAlgebra.trace (ν * x.2 * star y.2) := by
      simp only [herm, semi, star_star, sigL_mul, sigL_idem, star_mul', ν]; congr 2; ring
    change ![x.1, x.2.re, x.2.im] ⬝ᵥ B *ᵥ ![y.1, y.2.re, y.2.im] = _
    rw [e1, QuadraticAlgebra.trace_def]; simp [B, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring
  set x₀ : K := c * (2 - τ)
  have hx0 : x₀ ≠ 0 := mul_ne_zero hD.c_ne fun h => hτ2 (by linear_combination -h)
  have hdet : B.det = algebraMap K (Lsq K Δ) x₀ * t ^ 2 := by
    rw [Matrix.det_fin_three]; simp only [B, t, x₀, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.tail_cons,
      map_mul, map_sub, map_ofNat, hp]; ring
  have hsemiS (y : Sp Δ τ) : y ∈ S ↔ semi d y ∈ S := ⟨inS y, fun h => by
    obtain ⟨z, hz, hzy⟩ := preS _ h; have h2 := congrArg (semi d) hzy; rw [hsem, hsem] at h2
    exact Prod.ext (Prod.mk.inj h2).1 (hωu.mul_left_cancel (Prod.mk.inj h2).2) ▸ hz⟩
  let S₀ := M.map Φ.toLinearMap
  have hfg₀ : S₀.FG := Submodule.FG.map Φ.toLinearMap ⟨s, rfl⟩
  have hdual' (v : Fin 3 → Lsq K Δ) : v ∈ S₀ ↔ ∀ x ∈ S₀, IsInt O (x ⬝ᵥ B *ᵥ v) := by
    simp only [S₀, Submodule.mem_map_equiv, ← memM]; rw [hsemiS, hS.dual]
    refine ⟨fun h x hx => by simpa [← hid] using h (Φ.symm x) hx, fun h x hx => ?_⟩
    have h1 := h (Φ x) (by simpa using hx); rwa [← Φ.apply_symm_apply v, hid] at h1
  refine ⟨⟨o + 2, by rw [map_add, ho, map_ofNat]; ring⟩, ?_⟩
  by_cases hsq : IsSquare Δ
  · have h2 : (2 : K) ≠ 0 := by have := (hL.two.map (algebraMap O K)).ne_zero; rwa [map_ofNat] at this
    obtain ⟨u₀, s₀, hs₀, hus₀⟩ := hL.even; obtain ⟨δ, hδ⟩ := hsq
    have hδ0 : δ ≠ 0 := by rintro rfl; exact mul_ne_zero (u₀.isUnit.map (algebraMap O K)).ne_zero (pow_ne_zero _ hs₀) (by rw [← hus₀, hδ, mul_zero])
    let φ₁ : Lsq K Δ →ₐ[K] K := QuadraticAlgebra.lift ⟨δ, by simp [hδ]⟩
    let φ₂ : Lsq K Δ →ₐ[K] K := QuadraticAlgebra.lift ⟨-δ, by simp [hδ]⟩
    have hφ₁ (z : Lsq K Δ) : φ₁ z = z.re + δ * z.im := by simp [φ₁, QuadraticAlgebra.lift]; ring
    have hφ₂ (z : Lsq K Δ) : φ₂ z = z.re + -δ * z.im := by simp [φ₂, QuadraticAlgebra.lift]; ring
    let e : Lsq K Δ := ⟨1 / 2, 1 / (2 * δ)⟩
    have e1 : φ₁ e = 1 := by rw [hφ₁]; simp [e]; field_simp; ring
    have e2 : φ₂ e = 0 := by rw [hφ₂]; simp [e]; field_simp; ring
    have eint : IsIntegral O e := ⟨Polynomial.X ^ 2 - Polynomial.X,
      (Polynomial.monic_X_pow 2).sub_of_left (by rw [Polynomial.degree_X, Polynomial.degree_X_pow]; norm_num),
      by simp [sq, show e * e = e by ext <;> simp [e, hδ] <;> field_simp <;> ring]⟩
    have intcrit (z : Lsq K Δ) : φ₁ z ∈ (algebraMap O K).range → φ₂ z ∈ (algebraMap O K).range → IsIntegral O z := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      rw [show z = algebraMap K _ (φ₁ z) * e + algebraMap K _ (φ₂ z) * (1 - e) by rw [hφ₁, hφ₂]; ext <;> simp [e] <;> field_simp <;> ring,
        ← ha, ← hb, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
      exact (isIntegral_algebraMap.mul eint).add (isIntegral_algebraMap.mul (isIntegral_one.sub eint))
    have tr (φ : Lsq K Δ →ₐ[K] K) (v w : Fin 3 → Lsq K Δ) : φ (v ⬝ᵥ B *ᵥ w) = (φ ∘ v) ⬝ᵥ (B.map φ) *ᵥ (φ ∘ w) := by
      have h1 := RingHom.map_dotProduct (φ : Lsq K Δ →+* K) v (B *ᵥ w)
      rwa [show ((φ : Lsq K Δ →+* K) ∘ (B *ᵥ w)) = (B.map φ) *ᵥ (φ ∘ w) from funext fun i => RingHom.map_mulVec (φ : Lsq K Δ →+* K) B w i] at h1
    have hφt : φ₁ t ≠ 0 := (htu.map φ₁).ne_zero
    have hdet₁ : (B.map φ₁).det = x₀ * (φ₁ t) ^ 2 := by simpa [hdet] using (RingHom.map_det (φ₁ : Lsq K Δ →+* K) B).symm
    let F : (Fin 3 → Lsq K Δ) →ₗ[O] (Fin 3 → K) := (φ₁.restrictScalars O).toLinearMap.compLeft (Fin 3)
    obtain ⟨u, s', hs', hus⟩ := vanish_det (O := O) (K := K) (B.map φ₁)
      (by rw [hdet₁]; exact mul_ne_zero hx0 (pow_ne_zero _ hφt)) (S₀.map F) (hfg₀.map F) fun y' =>
      ⟨by rintro ⟨y, hy, rfl⟩ _ ⟨x₁, hx₁, rfl⟩
          have h1 : φ₁ (x₁ ⬝ᵥ B *ᵥ y) ∈ (algebraMap O K).range := RingHom.mem_range.2 (IsIntegrallyClosed.isIntegral_iff.1 (((hdual' y).1 hy x₁ hx₁).map φ₁))
          rwa [tr] at h1,
       fun h => ⟨fun i => algebraMap K _ (y' i) * e, (hdual' _).2 fun x₁ hx₁ => intcrit _
         (by rw [tr, show (φ₁ ∘ fun i => algebraMap K (Lsq K Δ) (y' i) * e) = y' from funext fun i => by simp [e1]]; exact h _ ⟨x₁, hx₁, rfl⟩)
         (by rw [tr, show (φ₂ ∘ fun i => algebraMap K (Lsq K Δ) (y' i) * e) = 0 from funext fun i => by simp [e2]]; simp), funext fun i => by simp [F, e1]⟩⟩
    exact ⟨u, s' / φ₁ t, div_ne_zero hs' hφt, by rw [hdet₁] at hus; field_simp; linear_combination hus⟩
  · have : Fact (∀ r : K, r ^ 2 ≠ Δ + 0 * r) := ⟨fun r hr => hsq ⟨r, by rw [← sq]; simpa using hr.symm⟩⟩
    let _ : Field (Lsq K Δ) := inferInstanceAs (Field (QuadraticAlgebra K Δ 0))
    have hK (k : K) (hk : IsIntegral O (algebraMap K (Lsq K Δ) k)) : ∃ a : O, algebraMap O K a = k :=
      IsIntegrallyClosed.isIntegral_iff.1 (isIntegral_algebraMap_iff.1 hk)
    have : IsFractionRing (integralClosure O (Lsq K Δ)) (Lsq K Δ) := integralClosure.isFractionRing_of_finite_extension K (Lsq K Δ)
    have : IsPrincipalIdealRing (integralClosure O (Lsq K Δ)) := ⟨fun I => by
      obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (I.comap (algebraMap O (integralClosure O (Lsq K Δ))))).principal
      refine ⟨⟨algebraMap O (integralClosure O (Lsq K Δ)) g, le_antisymm (fun z hz => ?_) ?_⟩⟩
      · by_cases hz0 : z = 0
        · exact hz0 ▸ Submodule.zero_mem _
        · obtain ⟨k, u, -, hzk⟩ := vanish_unit hL hsq z (fun h => hz0 (Subtype.ext h))
          have hku : algebraMap K (Lsq K Δ) k = ((z * ↑u⁻¹ : integralClosure O (Lsq K Δ)) : Lsq K Δ) := by
            change _ = (z : Lsq K Δ) * (↑u⁻¹ : integralClosure O (Lsq K Δ))
            rw [hzk, mul_assoc, show (u : Lsq K Δ) * (↑u⁻¹ : integralClosure O (Lsq K Δ)) = 1 from congrArg Subtype.val u.mul_inv, mul_one]
          obtain ⟨a, ha⟩ := hK k (by rw [hku]; exact (z * ↑u⁻¹).2)
          have haI : a ∈ I.comap (algebraMap O (integralClosure O (Lsq K Δ))) := by
            rw [Ideal.mem_comap, show algebraMap O (integralClosure O (Lsq K Δ)) a = z * ↑u⁻¹ from
              Subtype.ext (by show algebraMap O (Lsq K Δ) a = ↑(z * ↑u⁻¹); rw [IsScalarTower.algebraMap_apply O K, ha, hku])]
            exact I.mul_mem_right _ hz
          obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 (hg ▸ haI)
          exact Submodule.mem_span_singleton.2 ⟨algebraMap O _ r * u, Subtype.ext <| by
            show (algebraMap O (Lsq K Δ) r * u) * algebraMap O (Lsq K Δ) g = z
            rw [hzk, ← ha, ← hr, smul_eq_mul]; simp only [IsScalarTower.algebraMap_apply O K (Lsq K Δ), map_mul]; ring⟩
      · rw [Submodule.span_singleton_le_iff_mem, ← Ideal.mem_comap, hg]; exact Submodule.mem_span_singleton_self g⟩
    let S' : Submodule (integralClosure O (Lsq K Δ)) (Fin 3 → Lsq K Δ) :=
      { carrier := S₀, add_mem' := S₀.add_mem, zero_mem' := S₀.zero_mem,
        smul_mem' := fun c' y hy => (hdual' _).2 fun w hw => by
          rw [Matrix.mulVec_smul, dotProduct_smul, show c' • (w ⬝ᵥ B *ᵥ y) = (c' : Lsq K Δ) * (w ⬝ᵥ B *ᵥ y) from rfl]
          exact c'.2.mul ((hdual' y).1 hy w hw) }
    obtain ⟨s₀, hs₀⟩ := hfg₀
    have hfg' : S'.FG := ⟨s₀, le_antisymm (Submodule.span_le.2 fun y hy => by show y ∈ S₀; rw [← hs₀]; exact Submodule.subset_span hy)
      fun y hy => Submodule.span_le_restrictScalars O (integralClosure O (Lsq K Δ)) _ (by rw [hs₀]; exact hy)⟩
    have hd' (y : Fin 3 → Lsq K Δ) : y ∈ S' ↔ ∀ w ∈ S', w ⬝ᵥ B *ᵥ y ∈ (algebraMap (integralClosure O (Lsq K Δ)) (Lsq K Δ)).range :=
      (hdual' y).trans <| forall₂_congr fun _ _ => ⟨fun h => ⟨⟨_, h⟩, rfl⟩, fun ⟨z, hz⟩ => hz ▸ z.2⟩
    have ht0 : t ≠ 0 := htu.ne_zero
    obtain ⟨u, s', hs', hdet'⟩ := vanish_det B (by rw [hdet]; exact mul_ne_zero ((map_ne_zero _).2 hx0) (pow_ne_zero _ ht0)) S' hfg' hd'
    obtain ⟨k, v, hk, hqk⟩ := vanish_unit hL hsq (s' * t⁻¹) (mul_ne_zero hs' (inv_ne_zero ht0))
    let w : (integralClosure O (Lsq K Δ))ˣ := u * v ^ 2
    have hkL : algebraMap K (Lsq K Δ) k ≠ 0 := (map_ne_zero _).2 hk
    have e1 : algebraMap K (Lsq K Δ) (x₀ / k ^ 2) = (w : Lsq K Δ) := by
      have e : algebraMap K (Lsq K Δ) x₀ * t ^ 2 = (u : Lsq K Δ) * s' ^ 2 := hdet.symm.trans hdet'
      have h1 : algebraMap K (Lsq K Δ) x₀ = (u : Lsq K Δ) * (s' * t⁻¹) ^ 2 := by field_simp; linear_combination e
      rw [map_div₀, map_pow, h1, hqk]; change _ = (u : Lsq K Δ) * (v : Lsq K Δ) ^ 2; field_simp
    have e2 : algebraMap K (Lsq K Δ) (x₀ / k ^ 2)⁻¹ = ((w⁻¹ : (integralClosure O (Lsq K Δ))ˣ) : Lsq K Δ) := by
      rw [map_inv₀, e1]; exact inv_eq_of_mul_eq_one_right (congrArg Subtype.val w.mul_inv)
    obtain ⟨a, ha⟩ := hK _ (by rw [e1]; exact (w : integralClosure O (Lsq K Δ)).2)
    obtain ⟨b, hb⟩ := hK _ (by rw [e2]; exact (↑w⁻¹ : integralClosure O (Lsq K Δ)).2)
    refine ⟨Units.mkOfMulEqOne a b (IsFractionRing.injective O K (by rw [map_mul, ha, hb, mul_inv_cancel₀ (div_ne_zero hx0 (pow_ne_zero _ hk)), map_one])), k, hk, ?_⟩
    change x₀ = algebraMap O K a * k ^ 2; rw [ha]; field_simp

module

public import Formalism.LocalRingCardinality.DataLatDefs

@[expose] public section

open Formalism.MainNotions.G NumberField

noncomputable section

namespace Formalism.BasicNotions

structure TwForms (D : D7) where
  A : ∀ u μ, ColumnsAtT D.R (D.chTw u μ)
  A_T : ∀ u μ, (A u μ).T = (D.mem u).A.T
  fm : ∀ u μ, MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) (D.chTw u μ) (A u μ) (D.PTw u μ)

  e0 : ∀ u μ, ((D.fm u).lat 0).V ≃ₗ[D.what₂.LL] ((fm u μ).lat 0).V
  twist_preserves_base_lattice : ∀ u μ (x : ((D.fm u).lat 0).V), x ∈ ((D.fm u).lat 0).L ↔ e0 u μ x ∈ ((fm u μ).lat 0).L
  embed_mul_block_embedding : ∀ u μ (x : ((D.fm u).lat 0).V), (fm u μ).emb 0 (e0 u μ x) = D.e0Tw u μ ((D.fm u).emb 0 x)

  eMu0 : ∀ u j, j ≤ D.R.m → (((D.fm u).lat j).V ≃ₗ[D.what₂.LL] ((fm u D.what₂.mu0).lat j).V)
  eMu0_lat : ∀ u j (hj : j ≤ D.R.m) (x : ((D.fm u).lat j).V),
    x ∈ ((D.fm u).lat j).L ↔ eMu0 u j hj x ∈ ((fm u D.what₂.mu0).lat j).L
  eMu0_emb : ∀ u j (hj : j ≤ D.R.m) (x : ((D.fm u).lat j).V),
    HEq ((fm u D.what₂.mu0).emb j (eMu0 u j hj x)) ((D.fm u).emb j x)

structure LocalToGlobal₂ (D : D7) (Gt : GatTies D) (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    [Fact (D.what₂.places.resChar w).Prime]
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}
    (Ch : Chain Lv) where

  fl_t : Fl.t = D.R.t
  fl_m : Fl.mm = D.R.m

  lam : (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w]

  iK : (D.gat u w h).Kf →+* ℂ_[D.what₂.places.resChar w]

  iw : ∀ j (v : Fin (Fl.Pj j).nV), D.host.E →+* (Fl.Pj j).Qq v

  glob : ∀ j, Lv.comp j → (Fl.Pj j).Tup → Submodule (𝓞 D.host.E) (Fin ((Fl.Pj j).m + 1) → D.host.E)

  cls : ∀ j, Lv.comp j → (Fl.Pj j).Tup → (D.chTw u (D.what₂.muAt w)).cls j

  Th : ∀ j, Lv.comp j × (Fl.Pj j).Tup → Lv.comp (j + 1) × (Fl.Pj (j + 1)).Tup →
    MvPowerSeries (D.what₂.Tau × Fin ((Fl.Pj (j + 1)).m + 1) × Fin ((Fl.Pj j).m + 1)) ℂ_[D.what₂.places.resChar w]

  cmp : ∀ j, ((Tw.fm u (D.what₂.muAt w)).lat j).V →ₛₗ[c.embW u w h] Lv.Fm j

end Formalism.BasicNotions

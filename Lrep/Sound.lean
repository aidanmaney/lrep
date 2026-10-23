/-
Soundness of effect inference and claim checking.

The main results:

* `infer_sound`: every event of every run of a section is covered by an effect or call that
  `infer` reports, with an abstract resource that describes it.
* `check_sound`: if `check` accepts a `never` or `only` claim, no run of the section
  performs an event the claim rules out (`Violates`).

The one assumption: each op performs only its declared effects
(`Allowed`, `ResultOK` in `Lrep/Semantics.lean`).
-/
import Lrep.Semantics

namespace Lrep

/-! ## Resources -/

theorem segPrefix_trans {a b c : List String} :
    segPrefix a b = true → segPrefix b c = true → segPrefix a c = true := by
  induction a generalizing b c with
  | nil => simp [segPrefix]
  | cons x xs ih =>
    cases b with
    | nil => simp [segPrefix]
    | cons y ys =>
      cases c with
      | nil => simp [segPrefix]
      | cons z zs =>
        simp only [segPrefix, Bool.and_eq_true, beq_iff_eq]
        intro ⟨h1, h2⟩ ⟨h3, h4⟩
        exact ⟨h1.trans h3, ih h2 h4⟩

/-- Two prefixes of one path are comparable. -/
theorem segPrefix_total {a b c : List String} :
    segPrefix a c = true → segPrefix b c = true → segPrefix a b = true ∨ segPrefix b a = true := by
  induction a generalizing b c with
  | nil => simp [segPrefix]
  | cons x xs ih =>
    cases b with
    | nil => simp [segPrefix]
    | cons y ys =>
      cases c with
      | nil => simp [segPrefix]
      | cons z zs =>
        simp only [segPrefix, Bool.and_eq_true, beq_iff_eq]
        intro ⟨h1, h2⟩ ⟨h3, h4⟩
        rcases ih h2 h4 with h | h
        · exact Or.inl ⟨h1.trans h3.symm, h⟩
        · exact Or.inr ⟨h3.trans h1.symm, h⟩

theorem segPrefix_refl (a : List String) : segPrefix a a = true := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [segPrefix, ih]

theorem segPrefix_nil {a : List String} : segPrefix a [] = true ↔ a = [] := by
  cases a <;> simp [segPrefix]

/-- `covers` is sound: what `s` describes, `r` describes too. -/
theorem covers_sound {r s : Res} {c : CRes} : covers r s = true → approx s c → approx r c := by
  intro hc ha
  match r, s, c with
  | .path a true, .path b true, .path x =>
    simp only [covers, approx, ite_true] at hc ha ⊢; exact segPrefix_trans hc ha
  | .path a true, .path b false, .path x =>
    simp only [covers, approx, ite_true] at hc ha ⊢; subst ha; exact hc
  | .path a false, .path b pb, .path x =>
    cases pb <;> simp [covers, approx] at hc ha ⊢
    subst hc; exact ha
  | .url sc h a, .url sc' h' b, .url sc'' h'' x =>
    simp only [covers, approx, Bool.and_eq_true, beq_iff_eq] at hc ha ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    obtain ⟨h4, h5, h6⟩ := ha
    exact ⟨h1.trans h4, h2.trans h5, segPrefix_trans h3 h6⟩
  | .url sc h a, .url sc' h' b, .host sc'' h'' =>
    simp only [covers, approx, Bool.and_eq_true, beq_iff_eq] at hc ha ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    obtain ⟨h4, h5, h6⟩ := ha
    subst h6
    exact ⟨h1.trans h4, h2.trans h5, segPrefix_nil.mp h3⟩
  | .url sc h [], .host sc' h', .host sc'' h'' =>
    simp only [covers, approx, Bool.and_eq_true, beq_iff_eq] at hc ha ⊢
    exact ⟨hc.1.trans ha.1, hc.2.trans ha.2, trivial⟩
  | .host sc h, .host sc' h', .host sc'' h'' =>
    simp only [covers, approx, Bool.and_eq_true, beq_iff_eq] at hc ha ⊢
    exact ⟨hc.1.trans ha.1, hc.2.trans ha.2⟩
  | .port a, .port b, .port x =>
    simp only [covers, approx, beq_iff_eq] at hc ha ⊢; exact hc.trans ha
  | .cmd a, .cmd b, .cmd x =>
    simp only [covers, approx, beq_iff_eq] at hc ha ⊢; exact hc.trans ha
  | .top, _, _ => simp [covers] at hc
  | .path _ _, .url .., _ | .path _ _, .host .., _ | .path _ _, .port _, _ | .path _ _, .cmd _, _
  | .path _ _, .top, _ | .url .., .path .., _ | .url .., .port _, _ | .url .., .cmd _, _
  | .url .., .top, _ | .host .., .path .., _ | .host .., .url .., _ | .host .., .port _, _
  | .host .., .cmd _, _ | .host .., .top, _ | .port _, .path .., _ | .port _, .url .., _
  | .port _, .host .., _ | .port _, .cmd _, _ | .port _, .top, _ | .cmd _, .path .., _
  | .cmd _, .url .., _ | .cmd _, .host .., _ | .cmd _, .port _, _ | .cmd _, .top, _ =>
    simp [covers] at hc
  | .url _ _ (_ :: _), .host .., _ => simp [covers] at hc
  | _, .path _ true, .url .. | _, .path _ true, .host .. | _, .path _ true, .port _ | _, .path _ true, .cmd _
  | _, .path _ false, .url .. | _, .path _ false, .host .. | _, .path _ false, .port _ | _, .path _ false, .cmd _
  | _, .url .., .path _ | _, .url .., .port _ | _, .url .., .cmd _
  | _, .host .., .path _ | _, .host .., .url .. | _, .host .., .port _ | _, .host .., .cmd _
  | _, .port _, .path _ | _, .port _, .url .. | _, .port _, .host .. | _, .port _, .cmd _
  | _, .cmd _, .path _ | _, .cmd _, .url .. | _, .cmd _, .host .. | _, .cmd _, .port _ =>
    simp [approx] at ha

/-- Two resources that describe one concrete resource overlap. -/
theorem approx_overlaps {r s : Res} {c : CRes} : approx r c → approx s c → overlaps r s = true := by
  intro hr hs
  match r, s, c with
  | .top, _, _ => simp [overlaps]
  | .path _ _, .top, _ | .url .., .top, _ | .host .., .top, _ | .port _, .top, _ | .cmd _, .top, _ =>
    simp [overlaps]
  | .path a true, .path b true, .path x =>
    simp only [approx] at hr hs
    rcases segPrefix_total hr hs with h | h <;> simp [overlaps, covers, h]
  | .path a true, .path b false, .path x =>
    simp only [approx] at hr hs; subst hs; simp [overlaps, covers, hr]
  | .path a false, .path b true, .path x =>
    simp only [approx] at hr hs; subst hr; simp [overlaps, covers, hs]
  | .path a false, .path b false, .path x =>
    simp only [approx] at hr hs; subst hr; subst hs; simp [overlaps, covers]
  | .url sc h a, .url sc' h' b, .url sc'' h'' x =>
    simp only [approx] at hr hs
    obtain ⟨h1, h2, h3⟩ := hr; obtain ⟨h4, h5, h6⟩ := hs
    subst h1 h2 h4 h5
    rcases segPrefix_total h3 h6 with h | h <;> simp [overlaps, covers, h]
  | .url sc h a, .url sc' h' b, .host sc'' h'' =>
    simp only [approx] at hr hs
    obtain ⟨h1, h2, h3⟩ := hr; obtain ⟨h4, h5, h6⟩ := hs
    subst h1 h2 h3 h4 h5 h6; simp [overlaps, covers, segPrefix]
  | .url sc h a, .host sc' h', .host sc'' h'' =>
    simp only [approx] at hr hs
    obtain ⟨h1, h2, h3⟩ := hr; obtain ⟨h4, h5⟩ := hs
    subst h1 h2 h3 h4 h5; simp [overlaps, covers]
  | .host sc h, .url sc' h' b, .host sc'' h'' =>
    simp only [approx] at hr hs
    obtain ⟨h1, h2⟩ := hr; obtain ⟨h4, h5, h6⟩ := hs
    subst h1 h2 h4 h5 h6; simp [overlaps, covers]
  | .host sc h, .host sc' h', .host sc'' h'' =>
    simp only [approx] at hr hs
    obtain ⟨h1, h2⟩ := hr; obtain ⟨h4, h5⟩ := hs
    subst h1 h2 h4 h5; simp [overlaps, covers]
  | .port a, .port b, .port x =>
    simp only [approx] at hr hs; subst hr hs; simp [overlaps, covers]
  | .cmd a, .cmd b, .cmd x =>
    simp only [approx] at hr hs; subst hr hs; simp [overlaps, covers]
  | .path _ true, _, .url .. | .path _ true, _, .host .. | .path _ true, _, .port _ | .path _ true, _, .cmd _
  | .path _ false, _, .url .. | .path _ false, _, .host .. | .path _ false, _, .port _ | .path _ false, _, .cmd _
  | .url .., _, .path _ | .url .., _, .port _ | .url .., _, .cmd _
  | .host .., _, .path _ | .host .., _, .url .. | .host .., _, .port _ | .host .., _, .cmd _
  | .port _, _, .path _ | .port _, _, .url .. | .port _, _, .host .. | .port _, _, .cmd _
  | .cmd _, _, .path _ | .cmd _, _, .url .. | .cmd _, _, .host .. | .cmd _, _, .port _ =>
    simp [approx] at hr
  | _, .path _ true, .url .. | _, .path _ true, .host .. | _, .path _ true, .port _ | _, .path _ true, .cmd _
  | _, .path _ false, .url .. | _, .path _ false, .host .. | _, .path _ false, .port _ | _, .path _ false, .cmd _
  | _, .url .., .path _ | _, .url .., .port _ | _, .url .., .cmd _
  | _, .host .., .path _ | _, .host .., .url .. | _, .host .., .port _ | _, .host .., .cmd _
  | _, .port _, .path _ | _, .port _, .url .. | _, .port _, .host .. | _, .port _, .cmd _
  | _, .cmd _, .path _ | _, .cmd _, .url .. | _, .cmd _, .host .. | _, .cmd _, .port _ =>
    simp [approx] at hs

/-- A connect effect's host is described by the URL's abstract host. -/
theorem forKind_approx {k : Kind} {r : RVal} {c : CRes} :
    approx r.res c → approx (forKind k r).res (forKindC k c) := by
  intro h
  rcases r with ⟨res, o, t⟩
  cases k <;> cases res <;> cases c <;> simp_all [forKind, forKindC, approx]

/-! ## Values -/

/-- The concrete environment is described by the abstract one: every concrete binding's
resources are described by some abstract resource bound to the same id. -/
def EnvRel (ρ : CEnv) (σ : REnv) : Prop :=
  ∀ id vs, (id, vs) ∈ ρ → ∀ c ∈ vs, ∃ r ∈ lookupAll σ id, approx r.res c

theorem mem_of_lookup {ρ : CEnv} {id : Nat} {vs : List CRes} :
    ρ.lookup id = some vs → (id, vs) ∈ ρ := by
  induction ρ with
  | nil => simp [List.lookup]
  | cons p ps ih =>
    rcases p with ⟨k, v⟩
    simp only [List.lookup]
    split
    · rename_i h; intro e; simp at e h; subst e h; simp
    · intro e; exact List.mem_cons_of_mem _ (ih e)

theorem lookupAll_cons {σ : REnv} {id k : Nat} {rs : List RVal} {r : RVal} :
    r ∈ lookupAll σ id → r ∈ lookupAll ((k, rs) :: σ) id := by
  simp only [lookupAll, List.flatMap_cons, List.mem_append]
  exact Or.inr

theorem lookupAll_append {σ δ : REnv} {id : Nat} {r : RVal} :
    r ∈ lookupAll σ id → r ∈ lookupAll (δ ++ σ) id := by
  simp only [lookupAll, List.flatMap_append, List.mem_append]
  exact Or.inr

theorem EnvRel.cons {ρ : CEnv} {σ : REnv} {id : Nat} {vs : List CRes} {rs : List RVal} :
    EnvRel ρ σ → (∀ c ∈ vs, ∃ r ∈ rs, approx r.res c) → EnvRel ((id, vs) :: ρ) ((id, rs) :: σ) := by
  intro h hv k ws hm c hc
  rcases List.mem_cons.mp hm with e | e
  · cases e
    obtain ⟨r, hr, ha⟩ := hv c hc
    exact ⟨r, by simp [lookupAll, hr], ha⟩
  · obtain ⟨r, hr, ha⟩ := h k ws e c hc
    exact ⟨r, lookupAll_cons hr, ha⟩

theorem EnvRel.extend {ρ : CEnv} {σ : REnv} (δ : REnv) : EnvRel ρ σ → EnvRel ρ (δ ++ σ) := by
  intro h k ws hm c hc
  obtain ⟨r, hr, ha⟩ := h k ws hm c hc
  exact ⟨r, lookupAll_append hr, ha⟩

/-- Evaluation is sound: a value's concrete resources are described by `valRes`. -/
theorem eval_sound {ρ : CEnv} {σ : REnv} (hrel : EnvRel ρ σ) {v : CVal} {cs : List CRes} :
    Eval ρ v cs → ∀ c ∈ cs, ∃ r ∈ valRes σ v, approx r.res c := by
  intro he
  induction he with
  | lit h => simpa [valRes] using h
  | qty => simp
  | const h => simpa [valRes] using h
  | ref =>
    rename_i id _
    intro c hc
    cases hl : List.lookup id ρ with
    | none => simp [hl] at hc
    | some vs =>
      simp [hl] at hc
      obtain ⟨r, hr, ha⟩ := hrel id vs (mem_of_lookup hl) c hc
      exact ⟨r, by simpa [valRes] using hr, ha⟩
  | list f _ ih =>
    intro c hc
    rcases List.mem_flatMap.mp hc with ⟨v, hv, hcv⟩
    obtain ⟨r, hr, ha⟩ := ih v hv c hcv
    refine ⟨r, ?_, ha⟩
    simp only [valRes, List.mem_flatMap]
    exact ⟨⟨v, hv⟩, List.mem_attach _ _, hr⟩
  | unknown => intro c _; exact ⟨{ res := .top }, by simp [valRes], trivial⟩

theorem labelC_sound {ρ : CEnv} {σ : REnv} (hrel : EnvRel ρ σ) {args : List CArg}
    {cargs : CArg → List CRes} (hev : ∀ a ∈ args, Eval ρ a.val (cargs a)) (l : String) :
    ∀ c ∈ labelC args cargs l, ∃ r ∈ argRes σ args l, approx r.res c := by
  intro c hc
  simp only [labelC, List.mem_flatMap, List.mem_filter] at hc
  obtain ⟨a, ⟨ha, hl⟩, hca⟩ := hc
  obtain ⟨r, hr, hap⟩ := eval_sound hrel (hev a ha) c hca
  refine ⟨r, ?_, hap⟩
  simp only [argRes, List.mem_flatMap, List.mem_filter]
  exact ⟨a, ⟨ha, hl⟩, hr⟩

/-- An allowed effect is one `declEffects` reports, with a describing resource. -/
theorem declEffects_sound {ρ : CEnv} {σ : REnv} (hrel : EnvRel ρ σ) {decls : List EffDecl}
    {args : List CArg} {cargs : CArg → List CRes} (hev : ∀ a ∈ args, Eval ρ a.val (cargs a))
    (site : Span) {e : CEff} :
    Allowed decls (labelC args cargs) e →
    ∃ a ∈ declEffects σ decls args site, a.kind = e.kind ∧ approx a.res e.res := by
  rintro ⟨d, hd, hk, htgt⟩
  have hres : ∃ r ∈ (match d.on with
      | .object | .subject => argRes σ args ""
      | .label l => argRes σ args l
      | .top => [({ res := .top } : RVal)]), approx (forKind e.kind r).res e.res := by
    rcases htgt with ht | ⟨c, hc, he⟩
    · rw [ht]; exact ⟨{ res := .top }, by simp, by simp [forKind, approx]⟩
    · rw [he]
      cases hon : d.on with
      | object | subject =>
        rw [hon] at hc
        obtain ⟨r, hr, ha⟩ := labelC_sound hrel hev "" c hc
        exact ⟨r, hr, forKind_approx ha⟩
      | label l =>
        rw [hon] at hc
        obtain ⟨r, hr, ha⟩ := labelC_sound hrel hev l c hc
        exact ⟨r, hr, forKind_approx ha⟩
      | top => rw [hon] at hc; simp [targetC] at hc
  obtain ⟨r, hr, ha⟩ := hres
  refine ⟨{ kind := e.kind, res := (forKind e.kind r).res, site,
            origin := (forKind e.kind r).origin, text := (forKind e.kind r).text }, ?_, rfl, ha⟩
  simp only [declEffects, List.mem_flatMap]
  refine ⟨d, hd, ?_⟩
  rw [hk]
  exact List.mem_map.mpr ⟨r, hr, rfl⟩

/-! ## Inference -/

/-- An event is covered when inference reports it: an effect of the same kind on a
describing resource, or a call of the op with describing arguments. -/
def Covered (inf : Inferred) : Event → Prop
  | .eff e => ∃ a ∈ inf.effects, a.kind = e.kind ∧ approx a.res e.res
  | .call op args => op.isPrimitive = true ∨ ∃ t ∈ inf.calls, t.op.base = op.base ∧
      ∀ l, ∀ c ∈ args l, ∃ r ∈ (t.args.lookup l).getD [], approx r.res c

theorem Covered.left {a b : Inferred} {ev : Event} : Covered a ev → Covered (a.append b) ev := by
  cases ev with
  | eff e => rintro ⟨x, hx, h⟩; exact ⟨x, by simp [Inferred.append, hx], h⟩
  | call op args =>
    rintro (h | ⟨t, ht, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨t, by simp [Inferred.append, ht], h⟩

theorem Covered.right {a b : Inferred} {ev : Event} : Covered b ev → Covered (a.append b) ev := by
  cases ev with
  | eff e => rintro ⟨x, hx, h⟩; exact ⟨x, by simp [Inferred.append, hx], h⟩
  | call op args =>
    rintro (h | ⟨t, ht, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨t, by simp [Inferred.append, ht], h⟩

mutual
/-- Inference only adds bindings. -/
theorem inferStmt_env (lex : Lexicon) : ∀ (σ : REnv) (s : CStmt), ∃ δ, (inferStmt lex σ s).2 = δ ++ σ
  | σ, .call id op args site => ⟨[_], by simp [inferStmt]; rfl⟩
  | σ, .ite .. => ⟨[], by simp [inferStmt]⟩
  | σ, .loop .. => ⟨[], by simp [inferStmt]⟩
  | σ, .try body h => by
    obtain ⟨d1, h1⟩ := inferStmts_env lex σ body
    obtain ⟨d2, h2⟩ := inferStmts_env lex (inferStmts lex σ body).2 h
    exact ⟨d2 ++ d1, by simp only [inferStmt]; rw [h2, h1]; simp⟩

theorem inferStmts_env (lex : Lexicon) : ∀ (σ : REnv) (ss : List CStmt), ∃ δ, (inferStmts lex σ ss).2 = δ ++ σ
  | σ, [] => ⟨[], by simp [inferStmts]⟩
  | σ, s :: rest => by
    obtain ⟨d1, h1⟩ := inferStmt_env lex σ s
    obtain ⟨d2, h2⟩ := inferStmts_env lex (inferStmt lex σ s).2 rest
    exact ⟨d2 ++ d1, by simp only [inferStmts]; rw [h2, h1]; simp⟩
end

theorem lookup_labels {args : List CArg} {l : String} (f : String → List RVal) :
    (∃ a ∈ args, a.label = l) → (args.map fun a => (a.label, f a.label)).lookup l = some (f l) := by
  induction args with
  | nil => simp
  | cons a as ih =>
    rintro ⟨x, hx, hl⟩
    simp only [List.map_cons, List.lookup]
    by_cases h : l = a.label
    · subst h; simp
    · have : (l == a.label) = false := by simpa using h
      rw [this]
      rcases List.mem_cons.mp hx with e | e
      · subst e; exact absurd hl.symm h
      · exact ih ⟨x, e, hl⟩

theorem labelC_nonempty {args : List CArg} {cargs : CArg → List CRes} {l : String} {c : CRes} :
    c ∈ labelC args cargs l → ∃ a ∈ args, a.label = l := by
  simp only [labelC, List.mem_flatMap, List.mem_filter, beq_iff_eq]
  rintro ⟨a, ⟨ha, hl⟩, _⟩
  exact ⟨a, ha, hl⟩

theorem result_sound {lex : Lexicon} {ρ : CEnv} {σ : REnv} (hr : EnvRel ρ σ) {op : OpDef}
    {args : List CArg} {cargs : CArg → List CRes} (hev : ∀ a ∈ args, Eval ρ a.val (cargs a))
    {v : CRes} (hok : ResultOK lex op (labelC args cargs) v) :
    ∃ r ∈ resultRes lex σ op args, approx r.res v := by
  unfold ResultOK at hok
  unfold resultRes
  cases hret : op.returns with
  | none => simp [hret] at hok
  | some r =>
    simp only [hret] at hok ⊢
    obtain ⟨hhas, hk⟩ := hok
    simp only [hhas, ite_true]
    cases hro : r.resource <;> simp only [hro] at hk ⊢
    · exact labelC_sound hr hev "" v hk
    · exact labelC_sound hr hev _ v hk
    · exact ⟨{ res := .top }, by simp, trivial⟩

/-- The heart of the proof: every event of a run is covered by inference, and the
environments stay related. -/
theorem run_sound {lex : Lexicon} {ρ : CEnv} {ss : List CStmt} {tr : List Event} {ρ' : CEnv}
    (h : Run lex ρ ss tr ρ') : ∀ σ, EnvRel ρ σ →
    (∀ ev ∈ tr, Covered (inferStmts lex σ ss).1 ev) ∧ EnvRel ρ' (inferStmts lex σ ss).2 := by
  induction h with
  | nil => intro σ hr; exact ⟨by simp, by simpa [inferStmts] using hr⟩
  | @stop ρ ss =>
    intro σ hr
    obtain ⟨δ, hδ⟩ := inferStmts_env lex σ ss
    exact ⟨by simp, by rw [hδ]; exact hr.extend δ⟩
  | @call ρ id op args site rest t ρ' cargs es vs hev hall hres _ ih =>
    intro σ hr
    have hr1 : EnvRel ((id, vs) :: ρ) ((inferStmt lex σ (.call id op args site)).2) := by
      simp only [inferStmt]
      exact hr.cons fun c hc => result_sound hr hev (hres c hc)
    obtain ⟨ihc, ihr⟩ := ih _ hr1
    refine ⟨?_, by simpa [inferStmts] using ihr⟩
    intro ev hev'
    simp only [inferStmts]
    rcases List.mem_append.mp hev' with hev' | hev'
    · rcases List.mem_append.mp hev' with hev' | hev'
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hev'
        apply Covered.left
        obtain ⟨a, ha, hk, hap⟩ := declEffects_sound hr hev site (hall e he)
        exact ⟨a, by simp [inferStmt, ha], hk, hap⟩
      · simp at hev'; subst hev'
        apply Covered.left
        by_cases hp : op.isPrimitive = true
        · exact Or.inl hp
        · refine Or.inr ⟨⟨op, site, args.map fun a => (a.label, argRes σ args a.label)⟩,
            by simp [inferStmt, hp], rfl, ?_⟩
          intro l c hc
          rw [lookup_labels (argRes σ args) (labelC_nonempty hc)]
          exact labelC_sound hr hev l c hc
    · exact Covered.right (ihc ev hev')
  | @ite ρ all tests thn els rest tt tb t ρb ρ' branch htests hbr _ _ ihb ihr =>
    intro σ hr
    obtain ⟨ihbc, _⟩ := ihb σ hr
    obtain ⟨ihrc, ihrr⟩ := ihr σ hr
    refine ⟨?_, by simpa [inferStmts, inferStmt] using ihrr⟩
    intro ev hev
    simp only [inferStmts]
    rcases List.mem_append.mp hev with hev | hev
    · apply Covered.left
      rcases List.mem_append.mp hev with hev | hev
      · obtain ⟨x, hx, hte⟩ := htests ev hev
        cases ev with
        | call _ _ => exact hte.elim
        | eff e =>
          obtain ⟨cargs, hev2, hal⟩ := hte
          obtain ⟨a, ha, hk, hap⟩ := declEffects_sound hr hev2 x.site hal
          refine ⟨a, ?_, hk, hap⟩
          simp only [inferStmt, Inferred.append, List.mem_append, List.mem_flatMap]
          exact Or.inl ⟨x, hx, ha⟩
      · have hc := ihbc ev hev
        let te := tests.flatMap fun x => declEffects σ x.pred.effects x.args x.site
        have key : (inferStmt lex σ (.ite all tests thn els)).1 =
            (⟨te, []⟩ : Inferred).append ((inferStmts lex σ thn).1.append (inferStmts lex σ els).1) := rfl
        rw [key]
        rcases hbr with rfl | rfl
        · exact Covered.right (Covered.left hc)
        · exact Covered.right (Covered.right hc)
    · exact Covered.right (by simpa [inferStmt] using ihrc ev hev)
  | loopDone _ ih =>
    intro σ hr
    obtain ⟨ihc, ihr⟩ := ih σ hr
    refine ⟨fun ev hev => ?_, by simpa [inferStmts, inferStmt] using ihr⟩
    simp only [inferStmts]
    exact Covered.right (by simpa [inferStmt] using ihc ev hev)
  | @loopStep ρ elem coll body rest cs es t1 ρ1 t2 ρ' hcoll hes _ _ ihb ihl =>
    intro σ hr
    have hr1 : EnvRel ((elem, es) :: ρ) ((elem, valRes σ coll) :: σ) :=
      hr.cons fun c hc => eval_sound hr hcoll c (hes c hc)
    obtain ⟨ihbc, _⟩ := ihb _ hr1
    obtain ⟨ihlc, ihlr⟩ := ihl σ hr
    refine ⟨?_, ihlr⟩
    intro ev hev
    rcases List.mem_append.mp hev with hev | hev
    · simp only [inferStmts]
      apply Covered.left
      simpa [inferStmt] using ihbc ev hev
    · exact ihlc ev hev
  | @«try» ρ body h rest t1 ρ1 t2 ρ2 t3 ρ' _ _ _ ihb ihh ihr =>
    intro σ hr
    obtain ⟨ihbc, ihbr⟩ := ihb σ hr
    obtain ⟨ihhc, ihhr⟩ := ihh _ ihbr
    obtain ⟨ihrc, ihrr⟩ := ihr _ ihhr
    refine ⟨?_, by simpa [inferStmts, inferStmt] using ihrr⟩
    intro ev hev
    simp only [inferStmts]
    rcases List.mem_append.mp hev with hev | hev
    · rcases List.mem_append.mp hev with hev | hev
      · exact Covered.left (by simpa [inferStmt] using Covered.left (b := (inferStmts lex (inferStmts lex σ body).2 h).1) (ihbc ev hev))
      · exact Covered.left (by simpa [inferStmt] using Covered.right (a := (inferStmts lex σ body).1) (ihhc ev hev))
    · exact Covered.right (by simpa [inferStmt] using ihrc ev hev)

/-! ## Qualifiers -/

/-- A location qualifier's check is sound: if every abstract resource of a value lies within
the qualifier's regions, so does every concrete resource the value has at runtime. -/
theorem qual_within_sound {ρ : CEnv} {σ : REnv} (hr : EnvRel ρ σ) {v : CVal} {cs : List CRes}
    (he : Eval ρ v cs) {W : List Res} (hok : ∀ r ∈ valRes σ v, ∃ w ∈ W, covers w r.res = true) :
    ∀ c ∈ cs, ∃ w ∈ W, approx w c := by
  intro c hc
  obtain ⟨r, hrm, ha⟩ := eval_sound hr he c hc
  obtain ⟨w, hw, hcov⟩ := hok r hrm
  exact ⟨w, hw, covers_sound hcov ha⟩

/-! ## Claims -/

/-- Soundness of claim checking: if `check` accepts a `never` or `only` claim against a
section's inferred effects, no run of the section performs an event the claim rules out. -/
theorem check_sound {lex : Lexicon} {ss : List CStmt} {tr : List Event} {ρ' : CEnv}
    (σ : REnv) (c : CClaim) (hrun : Run lex [] ss tr ρ')
    (hold : (check σ (inferStmts lex [] ss).1 c).holds = true) :
    ∀ ev ∈ tr, ¬ Violates σ c ev := by
  intro ev hev hv
  have hcov := (run_sound hrun [] (by intro _ _ h; simp at h)).1 ev hev
  generalize (inferStmts lex [] ss).1 = inf at hcov hold
  unfold check at hold
  cases hk : c.op.names.bind Kind.ofString? with
  | some k =>
    simp only [hk, List.isEmpty_iff, List.filter_eq_nil_iff, List.mem_filter] at hold
    cases ev with
    | call _ _ => simp [Violates, hk] at hv
    | eff e =>
      simp only [Violates, hk] at hv
      obtain ⟨hke, hw⟩ := hv
      obtain ⟨a, ha, hka, hap⟩ := hcov
      have hbad := hold a ⟨ha, by simp [hka, hke]⟩
      by_cases hn : c.word = "never"
      · simp only [hn, ite_true] at hw
        simp only [hn, beq_self_eq_true, ite_true, Bool.or_eq_true, List.isEmpty_iff,
          List.any_eq_true, not_or, not_exists, not_and] at hbad
        rcases hw with h0 | ⟨r, hr, hra⟩
        · exact hbad.1 h0
        · exact hbad.2 r hr (approx_overlaps hra hap)
      · simp only [hn, ite_false] at hw
        have hn' : (c.word == "never") = false := by simpa using hn
        simp only [hn', Bool.false_eq_true, ite_false, Bool.not_eq_true', List.any_eq_false] at hbad
        exact hbad fun r hr => by
          cases h : covers r a.res with
          | false => simp
          | true => exact (hw ⟨r, hr, covers_sound h hap⟩).elim
  | none =>
    simp only [hk, List.isEmpty_iff, List.flatMap_eq_nil_iff, List.mem_filter] at hold
    cases ev with
    | eff _ => simp [Violates, hk] at hv
    | call op args =>
      simp only [Violates, hk] at hv
      obtain ⟨hprim, hbase, hw⟩ := hv
      rcases hcov with hp | ⟨t, ht, htb, hcargs⟩
      · simp [hp] at hprim
      have hbad := hold t ⟨ht, by simp [htb, hbase]⟩
      by_cases hn : c.word = "never"
      · simp only [hn, ite_true] at hw
        rcases hw with h0 | ⟨p, hp, x, hx, r, hr, hra⟩
        · simp [hn, h0] at hbad
        · have hne : ¬ ((c.word == "never" && (claimArgRes σ c).isEmpty) = true) := by
            simp only [hn, beq_self_eq_true, Bool.true_and, List.isEmpty_iff]
            intro h; simp [h] at hp
          simp only [hne, Bool.false_eq_true, ite_false, List.flatMap_eq_nil_iff, List.map_eq_nil_iff,
            List.filter_eq_nil_iff] at hbad
          obtain ⟨r', hr', hra'⟩ := hcargs p.1 x hx
          have := hbad p hp r' hr'
          simp only [hn, beq_self_eq_true, ite_true, List.any_eq_true, not_exists, not_and] at this
          exact this r hr (approx_overlaps hra hra')
      · simp only [hn, ite_false] at hw
        obtain ⟨p, hp, x, hx, hnot⟩ := hw
        have hn' : (c.word == "never") = false := by simpa using hn
        simp only [hn', Bool.false_and, Bool.false_eq_true, ite_false, List.flatMap_eq_nil_iff,
          List.map_eq_nil_iff, List.filter_eq_nil_iff] at hbad
        obtain ⟨r', hr', hra'⟩ := hcargs p.1 x hx
        have := hbad p hp r' hr'
        simp only [Bool.false_eq_true, ite_false, Bool.not_eq_true', List.any_eq_false] at this
        exact this fun r hr => by
          cases h : covers r r'.res with
          | false => simp
          | true => exact (hnot ⟨r, hr, covers_sound h hra'⟩).elim

end Lrep

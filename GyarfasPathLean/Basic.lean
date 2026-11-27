import FormalConjectures.Wikipedia.GyarfasSumnerConjecture

/-!
# Gyárfás's theorem: `P_t`-free graphs are χ-bounded

For every `t`, there is a function `f` such that every finite graph `G` with no induced path on
`t` vertices satisfies `χ(G) ≤ f(ω(G))` (Gyárfás, 1987). This is the case of paths in the
Gyárfás–Sumner conjecture.

## Proof (Gyárfás's path argument)

Induction on the clique bound `k`. Let `c` colours suffice for any set of neighbours of a vertex
(their cliques are smaller). Suppose a set `S` cannot be coloured with `t c + 1` colours. Take a
component that cannot, a vertex `x` in it, and a component `C` of the rest that cannot be
coloured with `t c` colours; it touches the neighbourhood of `x`.

Now grow an induced path `x = p₀, p₁, …`. At each step, `C` splits into the neighbours `A` of
the last path vertex, which need at most `c` colours, and the rest `D`. Some component `Q` of `D`
needs `c` fewer colours than `C`. Walking inside `C` from `Q` to `A` gives a vertex `u ∈ A`
adjacent to `Q`. Then `u` extends the induced path and `Q` replaces `C`. After `t - 1` steps
the path has `t` vertices, a contradiction.

This gives `f(0) = 0` and `f(k + 1) = t f(k) + 1`.

The main theorem `Gyarfas.chiBounded_pathGraph` has exactly the type of
`GyarfasSumnerConjecture.gyarfas_sumner_conjecture.variants.path` in Google DeepMind's
formal-conjectures repository (`FormalConjectures/Wikipedia/GyarfasSumnerConjecture.lean`).

## Reference

* A. Gyárfás, *Problems from the world surrounding perfect graphs*, Zastos. Mat. 19 (1987),
  413–441.
-/

open SimpleGraph Finset

namespace Gyarfas

variable {V : Type*} (G : SimpleGraph V)

/-- `S` can be properly coloured with colours `0, …, m - 1`. -/
def ColOn (S : Finset V) (m : ℕ) : Prop :=
  ∃ c : V → ℕ, (∀ v ∈ S, c v < m) ∧ ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v

variable {G}

lemma ColOn.mono {S T : Finset V} {m m' : ℕ} (h : ColOn G T m) (hST : S ⊆ T) (hm : m ≤ m') :
    ColOn G S m' := by
  obtain ⟨c, hc, hadj⟩ := h
  exact ⟨c, fun v hv => (hc v (hST hv)).trans_le hm,
    fun u hu v hv => hadj u (hST hu) v (hST hv)⟩

lemma ColOn.union [DecidableEq V] {S T : Finset V} {a b : ℕ} (hS : ColOn G S a) (hT : ColOn G T b) :
    ColOn G (S ∪ T) (a + b) := by
  classical
  obtain ⟨c, hc, hadj⟩ := hS
  obtain ⟨d, hd, hadj'⟩ := hT
  refine ⟨fun v => if v ∈ S then c v else a + d v, fun v hv => ?_, fun u hu v hv huv => ?_⟩
  · by_cases h : v ∈ S
    · simp only [h, if_true]; have := hc v h; omega
    · simp only [h, if_false]
      have := hd v ((mem_union.mp hv).resolve_left h); omega
  · by_cases h1 : u ∈ S <;> by_cases h2 : v ∈ S <;> simp only [h1, h2, if_true, if_false]
    · exact hadj u h1 v h2 huv
    · have := hc u h1; omega
    · have := hc v h2; omega
    · have := hadj' u ((mem_union.mp hu).resolve_left h1) v ((mem_union.mp hv).resolve_left h2)
        huv
      omega

lemma colOn_singleton (v : V) : ColOn G {v} 1 :=
  ⟨fun _ => 0, by simp, fun u hu w hw h => by
    simp only [mem_singleton] at hu hw; subst hu hw; exact absurd rfl h.ne⟩

lemma colOn_univ_chromaticNumber_le [Fintype V] {m : ℕ} (h : ColOn G univ m) : G.chromaticNumber ≤ m := by
  obtain ⟨c, hc, hadj⟩ := h
  exact Colorable.chromaticNumber_le
    ⟨Coloring.mk (fun v => (⟨c v, hc v (mem_univ v)⟩ : Fin m)) fun {u v} huv h =>
      hadj u (mem_univ u) v (mem_univ v) huv (congrArg Fin.val h)⟩

/- ### Connectivity inside a vertex set -/

/-- `y` can be reached from `x` by a walk whose vertices all lie in `C` (or `x = y`). -/
def Reach (G : SimpleGraph V) (C : Finset V) : V → V → Prop :=
  Relation.ReflTransGen fun a b => a ∈ C ∧ b ∈ C ∧ G.Adj a b

lemma reach_symm {C : Finset V} {x y : V} (h : Reach G C x y) : Reach G C y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, hbc.2.2.symm⟩ ih

open Classical in
/-- The component of `x` inside `C`. -/
noncomputable def comp (G : SimpleGraph V) (C : Finset V) (x : V) : Finset V :=
  C.filter (Reach G C x)

lemma mem_comp {C : Finset V} {x y : V} : y ∈ comp G C x ↔ y ∈ C ∧ Reach G C x y := by
  classical
  simp [comp]

lemma self_mem_comp {C : Finset V} {x : V} (hx : x ∈ C) : x ∈ comp G C x :=
  mem_comp.mpr ⟨hx, Relation.ReflTransGen.refl⟩

lemma comp_subset {C : Finset V} {x : V} : comp G C x ⊆ C := fun _ h => (mem_comp.mp h).1

lemma comp_closed {C : Finset V} {x z w : V} (hz : z ∈ comp G C x) (hw : w ∈ C)
    (hzw : G.Adj z w) : w ∈ comp G C x := by
  obtain ⟨hzC, hxz⟩ := mem_comp.mp hz
  exact mem_comp.mpr ⟨hw, hxz.tail ⟨hzC, hw, hzw⟩⟩

lemma reach_comp_of_reach {C : Finset V} {x z w : V} (hz : z ∈ comp G C x)
    (h : Reach G C z w) : Reach G (comp G C x) z w := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hzb hbw ih =>
    have hb : _ ∈ comp G C x := mem_comp.mpr ⟨hbw.1, (mem_comp.mp hz).2.trans hzb⟩
    exact ih.tail ⟨hb, comp_closed hb hbw.2.1 hbw.2.2, hbw.2.2⟩

lemma reach_comp {C : Finset V} {x z w : V} (hz : z ∈ comp G C x) (hw : w ∈ comp G C x) :
    Reach G (comp G C x) z w :=
  reach_comp_of_reach hz ((reach_symm (mem_comp.mp hz).2).trans (mem_comp.mp hw).2)

lemma comp_eq_of_mem {C : Finset V} {x y : V} (hy : y ∈ comp G C x) : comp G C y = comp G C x := by
  ext w
  simp only [mem_comp]
  have hxy := (mem_comp.mp hy).2
  exact ⟨fun ⟨hw, h⟩ => ⟨hw, hxy.trans h⟩, fun ⟨hw, h⟩ => ⟨hw, (reach_symm hxy).trans h⟩⟩

open Classical in
/-- If every component of `D` can be coloured with `m` colours, so can `D`. -/
lemma colOn_of_comp {D : Finset V} {m : ℕ} (h : ∀ x ∈ D, ColOn G (comp G D x) m) :
    ColOn G D m := by
  let F : Finset V → V → ℕ := fun T => if hT : ColOn G T m then hT.choose else fun _ => 0
  have hF : ∀ x ∈ D, (∀ v ∈ comp G D x, F (comp G D x) v < m) ∧
      ∀ u ∈ comp G D x, ∀ v ∈ comp G D x, G.Adj u v →
        F (comp G D x) u ≠ F (comp G D x) v := by
    intro x hx
    simp only [F, dif_pos (h x hx)]
    exact (h x hx).choose_spec
  refine ⟨fun v => F (comp G D v) v, fun v hv => (hF v hv).1 v (self_mem_comp hv),
    fun u hu v hv huv => ?_⟩
  have hvu : v ∈ comp G D u := comp_closed (self_mem_comp hu) hv huv
  simp only
  rw [comp_eq_of_mem hvu]
  exact (hF u hu).2 u (self_mem_comp hu) v hvu huv

/-- A walk inside `C` from a vertex of `Q` to a vertex outside `Q` leaves `Q` along an edge. -/
lemma exists_exit {C Q : Finset V} {x y : V} (h : Reach G C x y) (hx : x ∈ Q) (hy : y ∉ Q) :
    ∃ q ∈ Q, ∃ u, u ∉ Q ∧ u ∈ C ∧ G.Adj q u := by
  induction h with
  | refl => exact absurd hx hy
  | @tail b c _ hbc ih =>
    by_cases hb : b ∈ Q
    · exact ⟨b, hb, c, hy, hbc.2.1, hbc.2.2⟩
    · exact ih hb

/- ### Induced paths -/

/-- `p 0, …, p (j - 1)` is an induced path in `G`. -/
def IndPath (G : SimpleGraph V) (j : ℕ) (p : ℕ → V) : Prop :=
  (∀ a < j, ∀ b < j, G.Adj (p a) (p b) ↔ (a + 1 = b ∨ b + 1 = a)) ∧
    ∀ a < j, ∀ b < j, p a = p b → a = b

lemma IndPath.isIndContained {t : ℕ} {p : ℕ → V} (h : IndPath G t p) : pathGraph t ⊴ G :=
  ⟨{ toFun := fun i => p i
     inj' := fun a b hab => Fin.ext (h.2 a a.2 b b.2 hab)
     map_rel_iff' := fun {a b} => by
       simp only [pathGraph_adj]
       exact h.1 a a.2 b b.2 }⟩

lemma indPath_one (x : V) : IndPath G 1 (fun _ => x) :=
  ⟨fun a ha b hb => by
    simp only [show a = 0 by omega, show b = 0 by omega, G.irrefl, false_iff]; omega,
   fun a ha b hb _ => by omega⟩

lemma IndPath.extend {j : ℕ} {p : ℕ → V} (h : IndPath G j p) (hj : 1 ≤ j) {u : V}
    (hu : ∀ a < j, u ≠ p a) (hadj : G.Adj (p (j - 1)) u) (hna : ∀ a, a + 1 < j → ¬ G.Adj u (p a)) :
    IndPath G (j + 1) (fun i => if i = j then u else p i) := by
  constructor
  · intro a ha b hb
    by_cases haj : a = j <;> by_cases hbj : b = j <;> simp only [haj, hbj, if_true, if_false]
    · subst haj hbj; simp only [G.irrefl, false_iff]; omega
    · subst haj
      by_cases hb1 : b + 1 = a
      · subst hb1; simp only [Nat.add_sub_cancel] at hadj; simp [hadj.symm]
      · simp only [hna b (by omega), false_iff]; omega
    · subst hbj
      by_cases ha1 : a + 1 = b
      · subst ha1; simp only [Nat.add_sub_cancel] at hadj; simp [hadj]
      · have := hna a (by omega)
        exact ⟨fun h' => absurd h'.symm this, fun h' => by omega⟩
    · exact h.1 a (by omega) b (by omega)
  · intro a ha b hb hab
    by_cases haj : a = j <;> by_cases hbj : b = j <;> simp only [haj, hbj, if_true, if_false] at hab
    · omega
    · exact absurd hab (hu b (by omega))
    · exact absurd hab.symm (hu a (by omega))
    · exact h.2 a (by omega) b (by omega) hab

/- ### Gyárfás's path argument -/

/-- The growing step. We have an induced path `p 0, …, p (j - 1)` and a set `C` that cannot be
coloured with `d * c` colours, avoids the path and the neighbours of `p 0, …, p (j - 2)`, and
every component of which touches the neighbourhood of `p (j - 1)`. Then the path extends into
`C`, and after `d` more steps we find an induced path on `t = j + d` vertices. -/
lemma grow {t c : ℕ} (hfree : ¬ pathGraph t ⊴ G) {S : Finset V}
    (hN : ∀ v ∈ S, ∀ T ⊆ S, (∀ w ∈ T, G.Adj v w) → ColOn G T c) :
    ∀ d j (p : ℕ → V) (C : Finset V), j + d = t → 1 ≤ j → IndPath G j p → C ⊆ S →
      (∀ a < j, p a ∈ S) →
      (∀ x ∈ C, (∀ a < j, x ≠ p a) ∧ ∀ a, a + 1 < j → ¬ G.Adj x (p a)) →
      (∀ x ∈ C, ∃ y ∈ C, Reach G C x y ∧ G.Adj (p (j - 1)) y) →
      ¬ ColOn G C (d * c) → False := by
  classical
  intro d
  induction d with
  | zero =>
    intro j p C hjt _ hp _ _ _ _ _
    simp only [add_zero] at hjt
    subst hjt
    exact hfree hp.isIndContained
  | succ d ih =>
    intro j p C hjt hj hp hCS hpS hi hii hnot
    set w := p (j - 1) with hw
    have hwS : w ∈ S := hpS (j - 1) (by omega)
    set A := C.filter (G.Adj w) with hA_def
    set D := C.filter (fun z => ¬ G.Adj w z) with hD_def
    have hA : ColOn G A c :=
      hN w hwS A ((filter_subset _ _).trans hCS) fun _ h => (mem_filter.mp h).2
    have hD : ¬ ColOn G D (d * c) := by
      intro h
      apply hnot
      refine (hA.union h).mono (fun z hz => ?_) (by rw [Nat.succ_mul]; omega)
      by_cases hwz : G.Adj w z
      · exact mem_union_left _ (mem_filter.mpr ⟨hz, hwz⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨hz, hwz⟩)
    obtain ⟨x, hxD, hxQ⟩ : ∃ x ∈ D, ¬ ColOn G (comp G D x) (d * c) := by
      by_contra hall
      push Not at hall
      exact hD (colOn_of_comp hall)
    set Q := comp G D x with hQ_def
    have hxC : x ∈ C := (mem_filter.mp hxD).1
    obtain ⟨y, hyC, hxy, hwy⟩ := hii x hxC
    have hyQ : y ∉ Q := fun hy => (mem_filter.mp (comp_subset hy)).2 hwy
    obtain ⟨q, hqQ, u, huQ, huC, hqu⟩ := exists_exit hxy (self_mem_comp hxD) hyQ
    have huA : G.Adj w u := by
      by_contra h
      exact huQ (comp_closed hqQ (mem_filter.mpr ⟨huC, h⟩) hqu)
    have hQD : Q ⊆ D := comp_subset
    have hQC : Q ⊆ C := hQD.trans (filter_subset _ _)
    refine ih (j + 1) (fun i => if i = j then u else p i) Q (by omega) (by omega)
      (hp.extend hj (hi u huC).1 huA (hi u huC).2) (hQC.trans hCS) ?_ ?_ ?_ hxQ
    · intro a _
      by_cases haj : a = j
      · simp only [haj, if_true]; exact hCS huC
      · simp only [haj, if_false]; exact hpS a (by omega)
    · intro z hz
      have hzC := hQC hz
      refine ⟨fun a ha => ?_, fun a ha => ?_⟩
      · by_cases haj : a = j
        · simp only [haj, if_true]; exact fun h => huQ (h ▸ hz)
        · simp only [haj, if_false]; exact (hi z hzC).1 a (by omega)
      · have haj : a ≠ j := by omega
        simp only [haj, if_false]
        by_cases ha' : a + 1 < j
        · exact (hi z hzC).2 a ha'
        · have : a = j - 1 := by omega
          subst this
          exact fun h => (mem_filter.mp (hQD hz)).2 h.symm
    · intro z hz
      refine ⟨q, hqQ, reach_comp hz hqQ, ?_⟩
      simp only [Nat.add_sub_cancel, if_true]
      exact hqu.symm

lemma start {t c : ℕ} (hfree : ¬ pathGraph t ⊴ G) (ht : 1 ≤ t) {S : Finset V}
    (hN : ∀ v ∈ S, ∀ T ⊆ S, (∀ w ∈ T, G.Adj v w) → ColOn G T c)
    (hS : ¬ ColOn G S (t * c + 1)) : False := by
  classical
  obtain ⟨x, hxS, hx⟩ : ∃ x ∈ S, ¬ ColOn G (comp G S x) (t * c + 1) := by
    by_contra hall
    push Not at hall
    exact hS (colOn_of_comp hall)
  set C₀ := comp G S x with hC₀
  set E := C₀.erase x with hE_def
  have hE : ¬ ColOn G E (t * c) := by
    intro h
    apply hx
    refine ((colOn_singleton x).union h).mono (fun z hz => ?_) (by omega)
    by_cases hzx : z = x
    · exact mem_union_left _ (mem_singleton.mpr hzx)
    · exact mem_union_right _ (mem_erase.mpr ⟨hzx, hz⟩)
  obtain ⟨y, hyE, hy⟩ : ∃ y ∈ E, ¬ ColOn G (comp G E y) (t * c) := by
    by_contra hall
    push Not at hall
    exact hE (colOn_of_comp hall)
  set Q := comp G E y with hQ_def
  have hQE : Q ⊆ E := comp_subset
  have hEC : E ⊆ C₀ := erase_subset _ _
  have hQS : Q ⊆ S := hQE.trans (hEC.trans comp_subset)
  refine grow hfree hN (t - 1) 1 (fun _ => x) Q (by omega) le_rfl (indPath_one x) hQS
    (fun _ _ => hxS) (fun z hz => ⟨fun a _ => (mem_erase.mp (hQE hz)).1, fun a ha => by omega⟩)
    (fun z hz => ?_) (fun h => hy (h.mono subset_rfl (Nat.mul_le_mul_right _ (by omega))))
  have hz0 : z ∈ C₀ := hEC (hQE hz)
  have hzx : Reach G C₀ z x := reach_comp hz0 (self_mem_comp hxS)
  have hxQ : x ∉ Q := fun h => (mem_erase.mp (hQE h)).1 rfl
  obtain ⟨q, hqQ, u, huQ, huC, hqu⟩ := exists_exit hzx hz hxQ
  have hux : u = x := by
    by_contra h
    exact huQ (comp_closed hqQ (mem_erase.mpr ⟨h, huC⟩) hqu)
  subst hux
  exact ⟨q, hqQ, reach_comp hz hqQ, hqu.symm⟩

/-- The χ-bounding function: `f 0 = 0` and `f (k + 1) = t f k + 1`. -/
def bound (t : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => t * bound t k + 1

lemma colOn_bound {t : ℕ} (hfree : ¬ pathGraph t ⊴ G) :
    ∀ (k : ℕ) (S : Finset V), (∀ s ⊆ S, G.IsClique (s : Set V) → s.card ≤ k) →
      ColOn G S (bound t k) := by
  classical
  have ht : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h
      exact absurd ⟨⟨⟨Fin.elim0, fun a => a.elim0⟩, fun {a} => a.elim0⟩⟩ hfree
    · exact h
  intro k
  induction k with
  | zero =>
    intro S hS
    refine ⟨fun _ => 0, fun v hv => ?_, fun u hu _ _ _ => ?_⟩ <;>
    · exfalso
      first
      | have := hS {v} (by simpa using hv) (by simp)
      | have := hS {u} (by simpa using hu) (by simp)
      simp at this
  | succ k ih =>
    intro S hS
    by_contra hcol
    refine start hfree ht (fun v hv T hT hvT => ih T fun s hs hcl => ?_) hcol
    have hvs : v ∉ s := fun h => G.irrefl (hvT v (hs h))
    have hcl' : G.IsClique ((insert v s : Finset V) : Set V) := by
      rw [coe_insert]
      exact hcl.insert fun b hb _ => hvT b (hs hb)
    have := hS (insert v s) (insert_subset hv (hs.trans hT)) hcl'
    rw [card_insert_of_notMem hvs] at this
    omega

/-- **Gyárfás's theorem** (1987): for every `n`, graphs with no induced path on `n` vertices are
χ-bounded. -/
theorem chiBounded_pathGraph (n : ℕ) :
    ∃ f : ℕ → ℕ, GyarfasSumnerConjecture.IsChiBoundedBy (pathGraph n) f := by
  refine ⟨bound n, fun {V} _ _ G _ hfree => ?_⟩
  exact colOn_univ_chromaticNumber_le
    (colOn_bound hfree G.cliqueNum univ fun s _ hs => hs.card_le_cliqueNum)

example : type_of% @GyarfasSumnerConjecture.gyarfas_sumner_conjecture.variants.path :=
  @chiBounded_pathGraph

end Gyarfas

import PEqualNP.Defs

-- A chain of vertex restrictions forces distinct binary OR gates in a shared circuit.
-- Each restriction distinguishes an edge input and the remaining vertex set from
-- a singleton. Free conjunctions preserve the resulting implication. A binary OR
-- can break it only when both operands are live before the deletion and at least
-- one dies afterwards. Such an OR can be used at only one stage of the chain.

namespace PEqualNP.Outside.OrChain

abbrev Input (n : ℕ) := Fin n → Bool
abbrev Wire (n : ℕ) := Input n → Bool
abbrev Pair (n : ℕ) := Wire n × Wire n
abbrev Row := Finset ℕ × Finset ℕ
def zero {n} : Wire n := fun _ => false
def initial (n) : List (Wire n) := List.ofFn (fun i : Fin n => fun x : Input n => x i) ++ [zero]
def branch {n} (w : List (Wire n)) (s : Finset ℕ) : Wire n :=
  fun x => decide (∀ i ∈ s, (w.getD i zero) x = true)
def join {n} (p : Pair n) : Wire n := fun x => p.1 x || p.2 x
def wires {n} (es : List (Pair n)) := initial n ++ es.map join
def pair {n} (es : List (Pair n)) (r : Row) : Pair n := (branch (wires es) r.1, branch (wires es) r.2)
def events (n) (R : List Row) : List (Pair n) := R.foldl (fun es r => es ++ [pair es r]) []
def run {n} (R : List Row) (o : Finset ℕ) (x : Input n) : Bool :=
  let ws := R.foldl (fun w (r : Row) => w ++ [decide (∀ i ∈ r.1, w.getD i false = true) ||
        decide (∀ i ∈ r.2, w.getD i false = true)]) (List.ofFn x ++ [false])
  decide (∀ i ∈ o, ws.getD i false = true)

theorem es_snoc (n) (R : List Row) (r : Row) : events n (R ++ [r]) =
    events n R ++ [pair (events n R) r] := by simp [events,List.foldl_append]
theorem w_snoc {n} (es : List (Pair n)) (e : Pair n) : wires (es ++ [e]) = wires es ++ [join e] := by
  simp [wires]
theorem es_length (n) (R : List Row) : (events n R).length = R.length := by
  induction R using List.reverseRecOn with
  | nil => rfl
  | append_singleton R r ih => simp [es_snoc,ih]

theorem read_wire {n} (ws : List (Wire n)) (x : Input n) (i : ℕ) :
    (ws.map (fun f => f x)).getD i false = (ws.getD i zero) x := by
  by_cases h : i < ws.length
  · simp [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_none (Nat.le_of_not_gt h),zero]

theorem interpret {n} (R : List Row) (out : Finset ℕ) (x : Input n) :
    branch (wires (events n R)) out x = run R out x := by
  let step (w : List Bool) (r : Row) := w ++ [decide (∀ i ∈ r.1, w.getD i false = true) ||
      decide (∀ i ∈ r.2, w.getD i false = true)]
  have same : (wires (events n R)).map (fun f => f x) = R.foldl step (List.ofFn x ++ [false]) := by
    induction R using List.reverseRecOn with
    | nil => simp [events,wires,initial,zero,Function.comp_def]
    | append_singleton R r ih =>
      simp only [es_snoc,w_snoc,List.map_append,List.map_cons,List.map_nil,List.foldl_append,List.foldl_cons,List.foldl_nil]
      rw [← ih]; simp only [step,pair,join,branch,read_wire]
  change _ = decide (∀ i ∈ out, (R.foldl step (List.ofFn x ++ [false])).getD i false = true)
  rw [← same]; simp only [read_wire,branch]

def Inc {n} (x y : Input n) : Prop := ∀ i, x i = true → y i = true
def Mono {n} (f : Wire n) : Prop := ∀ x y, Inc x y → f x = true → f y = true
def Good {n} (a b d : Input n) (f : Wire n) : Prop := f a = true → f d = true → f b = true
def Charge {n} (c d : Input n) (e : Pair n) : Prop :=
  e.1 c = true ∧ e.2 c = true ∧ (e.1 d = false ∨ e.2 d = false)

theorem getD_prop {n} {P : Wire n → Prop} {ws : List (Wire n)}
    (all : ∀ f ∈ ws, P f) (z : P zero) (i : ℕ) : P (ws.getD i zero) := by
  by_cases h : i < ws.length
  · simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h] using all ws[i] (List.getElem_mem h)
  · simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_gt h)] using z
theorem initial_prop {n} {P : Wire n → Prop} (raw : ∀ i : Fin n, P (fun x => x i)) (z : P zero) :
    ∀ f ∈ initial n, P f := by
  intro f hf
  rcases List.mem_append.mp hf with hf|hf
  · obtain ⟨i,hi⟩ := List.mem_ofFn.mp hf
    subst f; exact raw i
  · simpa [List.mem_singleton.mp hf] using z
theorem monoB {n} {w : List (Wire n)} (m : ∀ f ∈ w, Mono f) (s : Finset ℕ) : Mono (branch w s) := by
  intro x y xy hx
  exact decide_eq_true (fun i hi => getD_prop m (by simp [Mono,zero]) i x y xy ((of_decide_eq_true hx) i hi))
theorem goodB {n} {w : List (Wire n)} {a b d : Input n} (m : ∀ f ∈ w, Good a b d f) (s : Finset ℕ) :
    Good a b d (branch w s) := by
  intro ha hd
  exact decide_eq_true (fun i hi => getD_prop m (by simp [Good,zero]) i ((of_decide_eq_true ha) i hi) ((of_decide_eq_true hd) i hi))
theorem monoJ {n} {e : Pair n} (l : Mono e.1) (r : Mono e.2) : Mono (join e) := by
  intro x y xy h
  exact Bool.or_eq_true_iff.mpr ((Bool.or_eq_true_iff.mp h).imp (l x y xy) (r x y xy))

theorem all_mono (n) (R : List Row) :
    (∀ f ∈ wires (events n R), Mono f) ∧ (∀ e ∈ events n R, Mono e.1 ∧ Mono e.2) := by
  induction R using List.reverseRecOn with
  | nil =>
    refine ⟨?_,by simp [events]⟩
    simpa [events,wires] using initial_prop (n := n) (P := Mono) (fun i x y xy => xy i) (by simp [Mono,zero])
  | append_singleton R r ih =>
    let e := pair (events n R) r
    have l : Mono e.1 := monoB ih.1 r.1
    have h : Mono e.2 := monoB ih.1 r.2
    rw [es_snoc,w_snoc]
    refine ⟨?_,?_⟩
    · intro f hf
      rcases List.mem_append.mp hf with hf|hf
      · exact ih.1 f hf
      · rw [List.mem_singleton.mp hf]; exact monoJ l h
    · intro q hq
      rcases List.mem_append.mp hq with hq|hq
      · exact ih.2 q hq
      · rw [List.mem_singleton.mp hq]; exact ⟨l,h⟩

theorem goodJ {n} {a b c d : Input n} {e : Pair n}
    (g : Good a b d e.1 ∧ Good a b d e.2) (m : Mono e.1 ∧ Mono e.2)
    (ac : Inc a c) (dc : Inc d c) (no : ¬ Charge c d e) : Good a b d (join e) := by
  intro ha hd
  rcases Bool.or_eq_true_iff.mp ha with la|ra <;> rcases Bool.or_eq_true_iff.mp hd with ld|rd
  · exact Bool.or_eq_true_iff.mpr (Or.inl (g.1 la ld))
  · by_cases ld : e.1 d = true
    · exact Bool.or_eq_true_iff.mpr (Or.inl (g.1 la ld))
    · exact (no ⟨m.1 _ _ ac la, m.2 _ _ dc rd, Or.inl (Bool.eq_false_iff.mpr ld)⟩).elim
  · by_cases rd : e.2 d = true
    · exact Bool.or_eq_true_iff.mpr (Or.inr (g.2 ra rd))
    · exact (no ⟨m.1 _ _ dc ld, m.2 _ _ ac ra, Or.inr (Bool.eq_false_iff.mpr rd)⟩).elim
  · exact Bool.or_eq_true_iff.mpr (Or.inr (g.2 ra rd))

theorem all_good {n} (R : List Row) {a b c d : Input n}
    (ac : Inc a c) (dc : Inc d c) (raw : ∀ i, a i = true → d i = true → b i = true)
    (no : ∀ e ∈ events n R, ¬ Charge c d e) : ∀ f ∈ wires (events n R), Good a b d f := by
  induction R using List.reverseRecOn with
  | nil => simpa [events,wires] using initial_prop (n := n) (P := Good a b d) raw (by simp [Good,zero])
  | append_singleton R r ih =>
    rw [es_snoc] at no ⊢
    rw [w_snoc]
    have old := ih (fun e he => no e (List.mem_append_left _ he))
    intro f hf
    rcases List.mem_append.mp hf with hf|hf
    · exact old f hf
    · rw [List.mem_singleton.mp hf]
      apply goodJ ⟨goodB old r.1,goodB old r.2⟩ _ ac dc (no _ (by simp))
      exact ⟨monoB (all_mono n R).1 _,monoB (all_mono n R).1 _⟩

theorem count_charges {n k : ℕ} (R : List Row) (o : Finset ℕ) (A B C D : Fin k → Input n)
    (ac : ∀ t, Inc (A t) (C t)) (dc : ∀ t, Inc (D t) (C t))
    (later : ∀ i j, i < j → Inc (C j) (D i))
    (raw : ∀ t z, A t z = true → D t z = true → B t z = true)
    (a : ∀ t, run R o (A t) = true) (d : ∀ t, run R o (D t) = true)
    (b : ∀ t, run R o (B t) = false) : k ≤ R.length := by
  classical
  have exists_e (t : Fin k) : ∃ i : Fin (events n R).length, Charge (C t) (D t) ((events n R).get i) := by
    by_contra h
    have no : ∀ e ∈ events n R, ¬ Charge (C t) (D t) e := by
      intro e he hit
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp he
      exact h ⟨i,hi.symm ▸ hit⟩
    have g := goodB (all_good R (ac t) (dc t) (raw t) no) o
    have v := g ((interpret R o _).trans (a t)) ((interpret R o _).trans (d t))
    exact Bool.false_ne_true ((b t).symm.trans ((interpret R o _).symm.trans v))
  choose idx hi using exists_e
  have sep (i j : Fin k) (lt : i < j) : idx i ≠ idx j := by
    intro eq
    have hj := hi j
    rw [← eq] at hj
    have hm := (all_mono n R).2 _ (List.get_mem (events n R) (idx i))
    rcases (hi i).2.2 with l|r
    · exact Bool.false_ne_true (l.symm.trans (hm.1 _ _ (later _ _ lt) hj.1))
    · exact Bool.false_ne_true (r.symm.trans (hm.2 _ _ (later _ _ lt) hj.2.1))
  have inject : Function.Injective idx := by
    intro i j eq
    rcases lt_trichotomy i j with lt|same|gt
    · exact (sep _ _ lt eq).elim
    · exact same
    · exact (sep _ _ gt eq.symm).elim
  simpa [es_length] using Fintype.card_le_of_injective idx inject

end PEqualNP.Outside.OrChain

namespace PEqualNP.Outside.PlaneChain

abbrev Input := Fin 42 → Bool
def rank (z : Fin 42) : ℕ := if z.val < 21 then 2 * z.val else 2 * (z.val - 21) + 1
def A (t : Fin 40) : Input := fun z => decide (rank z = t.val ∨ rank z = t.val + 1)
def B (t : Fin 40) : Input := fun z => decide (rank z = t.val + 1)
def C (t : Fin 40) : Input := fun z => decide (t.val ≤ rank z)
def D (t : Fin 40) : Input := fun z => decide (t.val < rank z)
theorem A_C (t : Fin 40) (z : Fin 42) : A t z = true → C t z = true := by
  simp only [A, C, decide_eq_true_eq]
  omega
theorem D_C (t : Fin 40) (z : Fin 42) : D t z = true → C t z = true := by
  simp only [D, C, decide_eq_true_eq]
  omega
theorem later (i j : Fin 40) (lt : i < j) (z : Fin 42) : C j z = true → D i z = true := by
  simp only [C, D, decide_eq_true_eq]
  omega
theorem raw (t : Fin 40) (z : Fin 42) : A t z = true → D t z = true → B t z = true := by
  simp only [A, D, B, decide_eq_true_eq]
  omega

def graph (x : Fin 42 → Bool) : Prop :=
  ∃ p l : Fin 21, ([(p.val + 20) % 21, p.val, (p.val + 5) % 21,
    (p.val + 7) % 21, (p.val + 17) % 21] : List ℕ).contains l.val = true ∧
    x (Fin.castAdd 21 p) = true ∧ x (Fin.natAdd 21 l) = true
instance (x : Fin 42 → Bool) : Decidable (graph x) := inferInstanceAs (Decidable
  (∃ p l : Fin 21, ([(p.val + 20) % 21, p.val, (p.val + 5) % 21,
    (p.val + 7) % 21, (p.val + 17) % 21] : List ℕ).contains l.val = true ∧
    x (Fin.castAdd 21 p) = true ∧ x (Fin.natAdd 21 l) = true))
set_option maxHeartbeats 1600000 in
theorem yesA : ∀ t : Fin 40, graph (A t) := by decide +kernel
theorem yesD (t : Fin 40) : graph (D t) := by
  refine ⟨20,20,by decide,?_,?_⟩
  · change decide (t.val < 40) = true
    exact decide_eq_true t.isLt
  · change decide (t.val < 41) = true
    exact decide_eq_true (by have := t.isLt; omega)
set_option maxHeartbeats 1600000 in
theorem noB : ∀ t : Fin 40, ¬ graph (B t) := by decide +kernel

end PEqualNP.Outside.PlaneChain

namespace PEqualNP.Outside.PlaneChain

open PEqualNP.Outside.OrChain

set_option maxHeartbeats 2400000 in
theorem assigned_40 :
  ∀ (x1 : List (Finset ℕ × Finset ℕ)) (x2 : Finset ℕ),   have x3 : Fin (21 : ℕ) → Fin (21 : ℕ) → Bool := fun (x3 x4 : Fin (21 : ℕ)) => [(↑x3 + (20 : ℕ)) % (21 : ℕ), ↑x3, (↑x3 + (5 : ℕ)) % (21 : ℕ), (↑x3 + (7 : ℕ)) % (21 : ℕ), (↑x3 + (17 : ℕ)) % (21 : ℕ)].contains ↑x4;   have x4 : (Fin (42 : ℕ) → Bool) → Bool := fun (x4 : Fin (42 : ℕ) → Bool) =>     have x5 : List Bool := List.foldl (fun (x5 : List Bool) (x6 : Finset ℕ × Finset ℕ) => x5 ++ [Decidable.decide (∀ x7 ∈ x6.1, x5.getD x7 Bool.false = Bool.true) || Decidable.decide (∀ x7 ∈ x6.2, x5.getD x7 Bool.false = Bool.true)]) (List.ofFn x4 ++ [Bool.false]) x1;     Decidable.decide (∀ x6 ∈ x2, x5.getD x6 Bool.false = Bool.true);   have x5 : (Fin (42 : ℕ) → Bool) → Prop := fun (x5 : Fin (42 : ℕ) → Bool) => ∀ (x6 x7 : Fin (21 : ℕ)), x3 x6 x7 = Bool.true → x5 (Fin.castAdd (21 : ℕ) x6) = Bool.false ∨ x5 (Fin.natAdd (21 : ℕ) x7) = Bool.false;   (∀ (x6 : ℕ) (x7 : x6 < x1.length), ∀ x8 ∈ x1[x6].1 ∪ x1[x6].2, x8 < (43 : ℕ) + x6) → (∀ x7 ∈ x2, x7 < (43 : ℕ) + x1.length) → (∀ (x8 x9 : Fin (21 : ℕ)), x3 x8 x9 = Bool.true → (x4 fun (x11 : Fin (42 : ℕ)) => Decidable.decide (x11 = Fin.castAdd (21 : ℕ) x8 ∨ x11 = Fin.natAdd (21 : ℕ) x9)) = Bool.true) → (∀ (x9 : Fin (42 : ℕ) → Bool), x5 x9 → (∀ (x11 : Fin (42 : ℕ) → Bool), x5 x11 → (∀ (x13 : Fin (42 : ℕ)), x9 x13 = Bool.true → x11 x13 = Bool.true) → x11 = x9) → x4 x9 = Bool.false) → (40 : ℕ) ≤ x1.length := by
  classical
  intro R o
  dsimp only
  intro _ _ hpos hneg
  let ev := @run 42
  let adj := fun (p l : Fin 21) => [(p.val + 20) % 21, p.val, (p.val + 5) % 21,
      (p.val + 7) % 21, (p.val + 17) % 21].contains l.val
  let F := graph
  have output_mono (x y : Fin 42 → Bool) (hxy : x ≤ y) (hx : ev R o x = true) : ev R o y = true := by
    have inc : Inc x y := by
      intro i hi
      have h := hxy i
      cases hy : y i with
      | false =>
        rw [hi,hy] at h
        exact False.elim ((by decide : ¬ (true ≤ false)) h)
      | true => rfl
    exact (interpret R o y).symm.trans ((monoB (all_mono 42 R).1 o) x y inc ((interpret R o x).trans hx))
  have exactR (x : Fin 42 → Bool) : ev R o x = true ↔ F x := by
    constructor
    · intro hx
      by_contra hn
      obtain ⟨y,hxy,hm⟩ := exists_maximal_ge_of_wellFoundedGT (fun z => ¬ F z) x hn
      have ind (z : Fin 42 → Bool) : ¬ F z ↔ ∀ p l : Fin 21, adj p l = true →
          z (Fin.castAdd 21 p) = false ∨ z (Fin.natAdd 21 l) = false := by
        constructor
        · intro hn p l hpl
          by_cases hp : z (Fin.castAdd 21 p) = true
          · exact Or.inr (Bool.eq_false_iff.mpr (fun hl => hn ⟨p,l,hpl,hp,hl⟩))
          · exact Or.inl (Bool.eq_false_iff.mpr hp)
        · rintro h ⟨p,l,hpl,hp,hl⟩
          rcases h p l hpl with hq | hq
          · exact Bool.false_ne_true (hq.symm.trans hp)
          · exact Bool.false_ne_true (hq.symm.trans hl)
      have leB {a b : Bool} (h : a = true → b = true) : a ≤ b := by
        cases a <;> cases b <;> simp_all
      have hy := hneg y ((ind y).1 hm.1) (by
        intro z hz h
        have hyz : y ≤ z := fun i => leB (h i)
        exact le_antisymm (hm.2 ((ind z).2 hz) hyz) hyz)
      exact Bool.false_ne_true (hy.symm.trans (output_mono x y hxy hx))
    · rintro ⟨p,l,h,ha,hb⟩
      apply output_mono _ _ _ (hpos p l h)
      intro i
      change decide (i = Fin.castAdd 21 p ∨ i = Fin.natAdd 21 l) ≤ x i
      by_cases f : i = Fin.castAdd 21 p ∨ i = Fin.natAdd 21 l
      · rw [decide_eq_true f]
        rcases f with rfl | rfl
        · rw [ha]
        · rw [hb]
      · rw [decide_eq_false f]
        exact bot_le

  apply count_charges R o A B C D A_C D_C later raw
  · exact fun t => (exactR _).mpr (yesA t)
  · exact fun t => (exactR _).mpr (yesD t)
  · exact fun t => Bool.eq_false_iff.mpr (fun h => noB t ((exactR _).mp h))

end PEqualNP.Outside.PlaneChain

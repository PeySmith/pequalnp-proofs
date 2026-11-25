import PEqualNP.Defs

-- The per-flag sensitivity argument in upstream pull request 5877 accounts for 33 ORs.
-- At equality all paid rows are false on each diagonal flag. Each row then first accepts
-- at most two incidence edges, and the final free conjunction at most one additional edge.
-- The 105 required edges rule out equality. The last theorem uses the posted hypotheses.

namespace PEqualNP.Outside.PlaneFlag

abbrev V := Fin 42
abbrev Input := V → Bool
abbrev Wire := Input → Bool
abbrev Row := Finset ℕ × Finset ℕ

def N (p : Input) : Finset V := Finset.univ.filter (fun i => p i = false)
def one (p : Input) (i : V) : Input := fun j => p j || decide (j = i)
def outsideN (p : Input) : Input := p
def zeroWire : Wire := fun _ => false
def inputWires : List Wire := List.ofFn (fun j : V => fun x : Input => x j) ++ [zeroWire]
def conjunction (w : List Wire) (s : Finset ℕ) : Wire :=
  fun x => decide (∀ i ∈ s, (w.getD i zeroWire) x = true)
def gate (w : List Wire) (r : Row) : Wire := fun x => conjunction w r.1 x || conjunction w r.2 x
def history (R : List Row) : List Wire :=
  R.foldl (fun acc r => acc ++ [gate (inputWires ++ acc) r]) []
def wires (R : List Row) := inputWires ++ history R
theorem history_snoc (R : List Row) (r : Row) : history (R ++ [r]) = history R ++ [gate (wires R) r] := by
  simp [history, wires, List.foldl_append]
theorem wires_snoc (R : List Row) (r : Row) : wires (R ++ [r]) = wires R ++ [gate (wires R) r] := by
  simp [wires, history_snoc]
theorem history_length (R : List Row) : (history R).length = R.length := by
  induction R using List.reverseRecOn with
  | nil => rfl
  | append_singleton R r ih => simp [history_snoc, ih]

def MonoColor (p : Input) (c : V → V) (f : Wire) : Prop :=
  f (outsideN p) = false → ∀ i j, f (one p i) = true → f (one p j) = true → c i = c j
def Charged (p : Input) (f : Wire) : Prop :=
  f (outsideN p) = false ∧ ∃ i j : V, i ≠ j ∧ f (one p i) = true ∧ f (one p j) = true
noncomputable def charges (p : Input) (fs : List Wire) : ℕ := by
  classical exact (fs.filter fun f => decide (Charged p f)).length

theorem getD_prop {P : Wire → Prop} {ws : List Wire}
    (all : ∀ f ∈ ws, P f) (zero : P zeroWire) (i : ℕ) : P (ws.getD i zeroWire) := by
  by_cases h : i < ws.length
  · simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h] using all ws[i] (List.getElem_mem h)
  · simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_gt h)] using zero
theorem mono_zero (p : Input) (c : V → V) : MonoColor p c zeroWire := by simp [MonoColor,zeroWire]
theorem mono_inputs (p : Input) : ∀ f ∈ inputWires, MonoColor p id f := by
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · obtain ⟨v,hv⟩ := List.mem_ofFn.mp hf
    subst f
    intro d i j hi hj
    have hzero : p v = false := d
    have hvi : v = i := by simpa [one,hzero] using hi
    have hvj : v = j := by simpa [one,hzero] using hj
    exact hvi.symm.trans hvj
  · have eq := List.mem_singleton.mp hf
    subst f
    exact mono_zero p _
theorem mono_and {cs : V → V} {p : Input} {ws : List Wire} (all : ∀ f ∈ ws, MonoColor p cs f)
    (s : Finset ℕ) : MonoColor p cs (conjunction ws s) := by
  classical
  intro off i j hi hj
  have no : ¬ ∀ n ∈ s, (ws.getD n zeroWire) (outsideN p) = true :=
    of_decide_eq_false off
  push Not at no
  obtain ⟨n,hn,bad⟩ := no
  have unlit : (ws.getD n zeroWire) (outsideN p) = false := by simpa using bad
  exact getD_prop all (mono_zero p cs) n unlit i j
    ((of_decide_eq_true hi) n hn) ((of_decide_eq_true hj) n hn)

theorem one_color {p : Input} {c : V → V} {f : Wire} (m : MonoColor p c f) (off : f (outsideN p) = false) :
    ∃ a : V, ∀ i, f (one p i) = true → c i = a := by
  by_cases h : ∃ i, f (one p i) = true
  · obtain ⟨i,hi⟩ := h
    exact ⟨c i,fun j hj => m off j i hj hi⟩
  · exact ⟨0, fun i hi => (h ⟨i,hi⟩).elim⟩

def identify (a b z : V) : V := if z=b then a else z
theorem image_loss (T : Finset V) (a b : V) : T.card ≤ (T.image (identify a b)).card + 1 := by
  have sub : T ⊆ insert b (T.image (identify a b)) := by
    intro x hx
    by_cases eq : x = b
    · simp [eq]
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x,hx,by simp [identify,eq]⟩)
  exact (Finset.card_le_card sub).trans (Finset.card_insert_le _ _)

theorem recolor {p : Input} {c : V → V} {ws : List Wire} (all : ∀ f ∈ ws, MonoColor p c f)
    (r : Row) (ch : Charged p (gate ws r)) :
    ∃ c' : V → V, ((N p).image c).card ≤ ((N p).image c').card + 1 ∧
       ∀ f ∈ ws ++ [gate ws r], MonoColor p c' f := by
  have off := Bool.or_eq_false_iff.mp ch.1
  obtain ⟨a,ha⟩ := one_color (mono_and all r.1) off.1
  obtain ⟨b,hb⟩ := one_color (mono_and all r.2) off.2
  let c' := identify a b ∘ c
  refine ⟨c', ?_, ?_⟩
  · simpa only [c',Finset.image_image,Function.comp_def] using image_loss ((N p).image c) a b
  · intro f hf
    rcases List.mem_append.mp hf with hf|hf
    · intro d i j hi hj
      exact congrArg (identify a b) (all f hf d i j hi hj)
    · have eq := List.mem_singleton.mp hf
      subst f
      have colored (i : V) (hi : gate ws r (one p i) = true) : c' i = a := by
        rcases Bool.or_eq_true_iff.mp hi with u|v
        · simp [c',Function.comp_def,ha i u,identify]
        · simp [c',Function.comp_def,hb i v,identify]
      exact fun _ i j hi hj => (colored i hi).trans (colored j hj).symm
theorem uncharged {p : Input} {c : V → V} {f : Wire} (h : ¬ Charged p f) : MonoColor p c f := by
  intro off i j hi hj
  by_cases e : i=j
  · simp [e]
  · exact (h ⟨off,i,j,e,hi,hj⟩).elim
theorem colors (p : Input) (R : List Row) :
    ∃ c : V → V, (N p).card ≤ ((N p).image c).card + charges p (history R) ∧
      ∀ f ∈ wires R, MonoColor p c f := by
  classical
  induction R using List.reverseRecOn with
  | nil =>
    refine ⟨id, ?_, ?_⟩
    · simp [history,charges]
    · simpa [wires,history] using mono_inputs p
  | append_singleton R r ih =>
    obtain ⟨c,ct,all⟩ := ih
    rw [history_snoc,wires_snoc]
    by_cases hit : Charged p (gate (wires R) r)
    · obtain ⟨c',le,news⟩ := recolor all r hit
      refine ⟨c',?_,news⟩
      have inc : charges p (history R ++ [gate (wires R) r]) = charges p (history R) + 1 := by
        simp [charges,hit]
      omega
    · refine ⟨c,?_,?_⟩
      · simpa [charges,hit] using ct
      · intro f hf
        rcases List.mem_append.mp hf with hf|hf
        · exact all f hf
        · have eq := List.mem_singleton.mp hf
          subst f; exact uncharged hit

def eval (R : List Row) (out : Finset ℕ) (x : Input) : Bool :=
  let ws := R.foldl (fun (w : List Bool) (r : Row) => w ++ [
    decide (∀ i ∈ r.1, w.getD i false = true) || decide (∀ i ∈ r.2, w.getD i false = true)])
    (List.ofFn x ++ [false])
  decide (∀ i ∈ out, ws.getD i false = true)
theorem read_wire (ws : List Wire) (x : Input) (i : ℕ) :
    (ws.map (fun f => f x)).getD i false = (ws.getD i zeroWire) x := by
  by_cases h : i < ws.length
  · simp [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_none (Nat.le_of_not_gt h),zeroWire]

theorem interpret (R : List Row) (out : Finset ℕ) (x : Input) :
    conjunction (wires R) out x = eval R out x := by
  let step (w : List Bool) (r : Row) := w ++ [decide (∀ i ∈ r.1, w.getD i false = true) ||
                                               decide (∀ i ∈ r.2, w.getD i false = true)]
  have same : (wires R).map (fun f => f x) = R.foldl step (List.ofFn x ++ [false]) := by
    induction R using List.reverseRecOn with
    | nil => simp [wires,history,inputWires,zeroWire]
    | append_singleton R r ih =>
      simp only [wires_snoc,List.map_append,List.map_cons,List.map_nil,List.foldl_append,List.foldl_cons,List.foldl_nil]
      rw [← ih]
      simp only [step,gate,conjunction,read_wire]
  change _ = decide (∀ i ∈ out, (R.foldl step (List.ofFn x ++ [false])).getD i false = true)
  rw [← same]
  simp only [read_wire,conjunction]


theorem flag_sensitivity (R : List Row) (o : Finset ℕ) (p : Input)
    (neg : eval R o p = false)
    (lit : ∀ i ∈ N p, eval R o (one p i) = true) :
    (N p).card ≤ 1 + charges p (history R) := by
  classical
  obtain ⟨c,ct,all⟩ := colors p R
  obtain ⟨a,ha⟩ := one_color (mono_and all o) ((interpret R o p).trans neg)
  have sub : (N p).image c ⊆ {a} := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_singleton.mpr (ha i ((interpret R o _).trans (lit i hi)))
  have card := Finset.card_le_card sub
  rw [Finset.card_singleton] at card
  omega

theorem all_off_if_33 (R : List Row) (o : Finset ℕ) (p : Input)
    (nh : (N p).card = 34) (le : R.length ≤ 33)
    (neg : eval R o p = false) (lit : ∀ i ∈ N p, eval R o (one p i) = true) :
    ∀ f ∈ history R, f p = false := by
  classical
  have h := flag_sensitivity R o p neg lit
  have ca : charges p (history R) ≤ (history R).length :=
    List.length_filter_le _ (history R)
  have eq : ((history R).filter (fun f => decide (Charged p f))).length = (history R).length := by
    change charges p (history R) = (history R).length
    rw [history_length] at ca ⊢
    omega
  intro f hf
  have all : ∀ w ∈ history R, decide (Charged p w) = true := List.length_filter_eq_length_iff.mp eq
  exact (of_decide_eq_true (all f hf)).1


abbrev Pnt := Fin 21
def pt (p : Pnt) : V := Fin.castAdd 21 p
def ln (l : Pnt) : V := Fin.natAdd 21 l
def inc (p l : Pnt) : Bool := ([(p.val + 20) % 21, p.val, (p.val + 5) % 21,
  (p.val + 7) % 21, (p.val + 17) % 21] : List ℕ).contains l.val
abbrev E := {e : Pnt × Pnt // inc e.1 e.2 = true}
def edge (e : E) : Input := fun i => decide (i = pt e.val.1 ∨ i = ln e.val.2)
def flag (p : Pnt) : Input := fun i =>
  if h : i.val < 21 then (inc ⟨i.val, h⟩ p && decide (i.val ≠ p.val))
  else (inc p ⟨i.val - 21, by have := i.isLt; omega⟩ && decide (i.val ≠ p.val + 21))
def graph (x : Input) : Prop := ∃ p l : Pnt, inc p l = true ∧ x (pt p) = true ∧ x (ln l) = true
instance (x : Input) : Decidable (graph x) := inferInstanceAs (Decidable (∃ _p _l : Pnt, _))
theorem edge_count : Fintype.card E = 105 := by decide +kernel
theorem geometry_size : ∀ p : Pnt, (N (flag p)).card = 34 := by decide +kernel
theorem geometry_cover : ∀ i : V, ∃ p : Pnt, flag p i = true := by decide +kernel
set_option maxHeartbeats 1200000 in
theorem geometry_false : ∀ p : Pnt, ¬ graph (flag p) := by decide +kernel
set_option maxHeartbeats 6400000 in
theorem geometry_flip : ∀ (p : Pnt) (i : V), flag p i = false → graph (one (flag p) i) := by decide +kernel
theorem graph_edge (e : E) : graph (edge e) := by
  exact ⟨e.val.1,e.val.2,e.property,by simp [edge],by simp [edge]⟩
theorem point_line_ne (p l : Pnt) : pt p ≠ ln l := by
  intro h
  have w := congrArg Fin.val h
  change p.val = 21 + l.val at w
  have := p.isLt
  omega
theorem edge_common (e f : E) (ne : e ≠ f) : ∃ p, ∀ i, edge e i = true → edge f i = true → flag p i = true := by
  by_cases ep : e.val.1 = f.val.1
  · obtain ⟨b,hb⟩ := geometry_cover (pt e.val.1)
    refine ⟨b, ?_⟩
    intro i he hf
    rcases of_decide_eq_true he with h | h
    · simpa [h] using hb
    · rcases of_decide_eq_true hf with k | k
      · simpa [k,← ep] using hb
      · have vl := congrArg Fin.val (h.symm.trans k)
        have same : e.val.2 = f.val.2 := by
          apply Fin.ext
          change 21 + e.val.2.val = 21 + f.val.2.val at vl
          omega
        exact (ne (Subtype.ext (Prod.ext ep same))).elim
  · obtain ⟨b,hb⟩ := geometry_cover (ln e.val.2)
    refine ⟨b, ?_⟩
    intro i he hf
    rcases of_decide_eq_true he with h | h
    · rcases of_decide_eq_true hf with k | k
      · exact (ep (Fin.ext (congrArg (fun v : V => v.val) (h.symm.trans k)))).elim
      · exact (point_line_ne _ _ (h.symm.trans k)).elim
    · simpa [h] using hb

noncomputable def active (fs : List Wire) : Finset E := by
  classical exact Finset.univ.filter (fun e => ∃ f ∈ fs, f (edge e) = true)
noncomputable def born (fs : List Wire) (a : Wire) : Finset E := by
  classical exact Finset.univ.filter (fun e => a (edge e) = true ∧ e ∉ active fs)
theorem active_spec (fs : List Wire) (e : E) :
    e ∈ active fs ↔ ∃ f ∈ fs, f (edge e) = true := by classical simp [active]
theorem born_spec (fs : List Wire) (a : Wire) (e : E) :
    e ∈ born fs a ↔ a (edge e) = true ∧ e ∉ active fs := by classical simp [born]
theorem born_operand (fs : List Wire) (s : Finset ℕ)
    (off : ∀ p, conjunction (inputWires ++ fs) s (flag p) = false) :
    (born fs (conjunction (inputWires ++ fs) s)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro e he f hf
  by_contra ne
  obtain ⟨b, common⟩ := edge_common e f ne
  obtain ⟨elit,enew⟩ := (born_spec _ _ _).mp he
  obtain ⟨flit,_⟩ := (born_spec _ _ _).mp hf
  let P : Wire → Prop := fun w => w (edge e) = true → w (edge f) = true → w (flag b) = true
  have zero : P zeroWire := by simp [P,zeroWire]
  have al : ∀ w ∈ inputWires ++ fs, P w := by
    intro w hw
    rcases List.mem_append.mp hw with raw | gen
    · rcases List.mem_append.mp raw with inp | z
      · obtain ⟨i, hi⟩ := List.mem_ofFn.mp inp
        subst w
        exact common i
      · obtain rfl := List.mem_singleton.mp z
        exact zero
    · exact fun hit _ => (enew ((active_spec fs e).mpr ⟨w,gen,hit⟩)).elim
  have yes : conjunction (inputWires ++ fs) s (flag b) = true := by
    apply decide_eq_true
    intro i hi
    exact getD_prop al zero i ((of_decide_eq_true elit) i hi) ((of_decide_eq_true flit) i hi)
  exact Bool.false_ne_true ((off b).symm.trans yes)
theorem active_snoc_bound (fs : List Wire) (r : Row)
    (off : ∀ p, gate (inputWires ++ fs) r (flag p) = false) :
    (active (fs ++ [gate (inputWires ++ fs) r])).card ≤ (active fs).card + 2 := by
  classical
  let left := conjunction (inputWires ++ fs) r.1
  let right := conjunction (inputWires ++ fs) r.2
  have bl := born_operand fs r.1 (fun p => (Bool.or_eq_false_iff.mp (off p)).1)
  have br := born_operand fs r.2 (fun p => (Bool.or_eq_false_iff.mp (off p)).2)
  have sub : active (fs ++ [gate (inputWires ++ fs) r]) ⊆ (active fs ∪ born fs left) ∪ born fs right := by
    intro e he
    by_cases old : e ∈ active fs
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ old)
    obtain ⟨w,hw,hit⟩ := (active_spec _ _).mp he
    rcases List.mem_append.mp hw with prior | fresh
    · exact (old ((active_spec _ _).mpr ⟨w,prior,hit⟩)).elim
    obtain rfl := List.mem_singleton.mp fresh
    rcases Bool.or_eq_true_iff.mp hit with a | b
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ ((born_spec _ _ _).mpr ⟨a,old⟩))
    · exact Finset.mem_union_right _ ((born_spec _ _ _).mpr ⟨b,old⟩)
  have h := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  have k := Finset.card_union_le (active fs) (born fs left)
  change (born fs left).card ≤ 1 at bl
  change (born fs right).card ≤ 1 at br
  omega
theorem active_bound (R : List Row)
    (off : ∀ w ∈ history R, ∀ p, w (flag p) = false) :
    (active (history R)).card ≤ 2 * R.length := by
  classical
  induction R using List.reverseRecOn with
  | nil => simp [active,history]
  | append_singleton R r ih =>
    rw [history_snoc] at off ⊢
    have old := ih (fun w hw => off w (List.mem_append_left _ hw))
    have last : gate (wires R) r ∈ history R ++ [gate (wires R) r] := by simp
    have fresh := active_snoc_bound (history R) r (off _ last)
    change (active (history R ++ [gate (wires R) r])).card ≤ _ at fresh
    simp only [List.length_append,List.length_cons,List.length_nil] at *
    omega

theorem incidence_34 (R : List Row) (o : Finset ℕ)
    (correct : ∀ x, eval R o x = true ↔ graph x) : 34 ≤ R.length := by
  classical
  by_contra h
  have le : R.length ≤ 33 := by omega
  have neg (p) : eval R o (flag p) = false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    exact geometry_false p ((correct _).mp yes)
  have saturated (p) := all_off_if_33 R o (flag p) (geometry_size p) le (neg p)
    (fun i hi => (correct _).mpr (geometry_flip p i (by simpa [N] using hi)))
  have small := active_bound R (fun w hw p => saturated p w hw)
  have rem := born_operand (history R) o (fun p => (interpret R o (flag p)).trans (neg p))
  have sub : (Finset.univ : Finset E) ⊆
        active (history R) ∪ born (history R) (conjunction (wires R) o) := by
    intro e _
    by_cases old : e ∈ active (history R)
    · exact Finset.mem_union_left _ old
    · exact Finset.mem_union_right _ ((born_spec _ _ _).mpr ⟨(interpret R o _).trans ((correct _).mpr (graph_edge e)),old⟩)
  have lim := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  rw [Finset.card_univ,edge_count] at lim
  change (born (history R) (conjunction (wires R) o)).card ≤ 1 at rem
  omega

set_option maxHeartbeats 2400000 in
theorem assigned_34 : ∀ (x1 : List (Finset ℕ × Finset ℕ)) (x2 : Finset ℕ),   have x3 : Fin (21 : ℕ) → Fin (21 : ℕ) → Bool := fun (x3 x4 : Fin (21 : ℕ)) => [(↑x3 + (20 : ℕ)) % (21 : ℕ), ↑x3, (↑x3 + (5 : ℕ)) % (21 : ℕ), (↑x3 + (7 : ℕ)) % (21 : ℕ), (↑x3 + (17 : ℕ)) % (21 : ℕ)].contains ↑x4;   have x4 : (Fin (42 : ℕ) → Bool) → Bool := fun (x4 : Fin (42 : ℕ) → Bool) =>     have x5 : List Bool := List.foldl (fun (x5 : List Bool) (x6 : Finset ℕ × Finset ℕ) => x5 ++ [Decidable.decide (∀ x7 ∈ x6.1, x5.getD x7 Bool.false = Bool.true) || Decidable.decide (∀ x7 ∈ x6.2, x5.getD x7 Bool.false = Bool.true)]) (List.ofFn x4 ++ [Bool.false]) x1;     Decidable.decide (∀ x6 ∈ x2, x5.getD x6 Bool.false = Bool.true);   have x5 : (Fin (42 : ℕ) → Bool) → Prop := fun (x5 : Fin (42 : ℕ) → Bool) => ∀ (x6 x7 : Fin (21 : ℕ)), x3 x6 x7 = Bool.true → x5 (Fin.castAdd (21 : ℕ) x6) = Bool.false ∨ x5 (Fin.natAdd (21 : ℕ) x7) = Bool.false;   (∀ (x6 : ℕ) (x7 : x6 < x1.length), ∀ x8 ∈ x1[x6].1 ∪ x1[x6].2, x8 < (43 : ℕ) + x6) → (∀ x7 ∈ x2, x7 < (43 : ℕ) + x1.length) → (∀ (x8 x9 : Fin (21 : ℕ)), x3 x8 x9 = Bool.true → (x4 fun (x11 : Fin (42 : ℕ)) => Decidable.decide (x11 = Fin.castAdd (21 : ℕ) x8 ∨ x11 = Fin.natAdd (21 : ℕ) x9)) = Bool.true) → (∀ (x9 : Fin (42 : ℕ) → Bool), x5 x9 → (∀ (x11 : Fin (42 : ℕ) → Bool), x5 x11 → (∀ (x13 : Fin (42 : ℕ)), x9 x13 = Bool.true → x11 x13 = Bool.true) → x11 = x9) → x4 x9 = Bool.false) → (34 : ℕ) ≤ x1.length := by
  classical
  intro R o
  dsimp only
  intro _ _ hpos hneg
  let w := fun (R : List (Finset ℕ × Finset ℕ)) (x : Fin 42 → Bool) =>
      R.foldl (fun w r => w ++ [decide (∀ i ∈ r.1, w.getD i false = true) ||
        decide (∀ i ∈ r.2, w.getD i false = true)]) (List.ofFn x ++ [false])
  let ev := fun (R : List (Finset ℕ × Finset ℕ)) (o : Finset ℕ) (x : Fin 42 → Bool) =>
      decide (∀ i ∈ o, (w R x).getD i false = true)
  let adj := fun (p l : Fin 21) => [(p.val + 20) % 21, p.val, (p.val + 5) % 21,
      (p.val + 7) % 21, (p.val + 17) % 21].contains l.val
  let F := fun (x : Fin 42 → Bool) => ∃ p l : Fin 21, adj p l = true ∧
      x (Fin.castAdd 21 p) = true ∧ x (Fin.natAdd 21 l) = true
  let lew := fun (a b : List Bool) => a.length = b.length ∧
    ∀ i : ℕ, a.getD i false = true → b.getD i false = true
  have mono (x y : Fin 42 → Bool) (hxy : x ≤ y) (r : List (Finset ℕ × Finset ℕ)) :
      lew (w r x) (w r y) := by
    have base : lew (List.ofFn x ++ [false]) (List.ofFn y ++ [false]) := by
      refine ⟨by simp, ?_⟩
      intro i hi
      by_cases h : i < 42
      · have raw (z : Fin 42 → Bool) (j : Fin 42) : (List.ofFn z ++ [false]).getD j.val false = z j := by
          simp only [List.getD_eq_getElem?_getD,List.getElem?_append,List.length_ofFn,ite_eq_left j.isLt,
            List.getElem?_ofFn,dite_eq_left j.isLt,Option.getD_some]
        let j : Fin 42 := ⟨i,h⟩
        have hx : x j = true := (raw x j).symm.trans hi
        apply (raw y j).trans
        cases hy : y j
        · have hbad := hxy j
          rw [hx,hy] at hbad
          exact False.elim ((by decide : ¬ (true ≤ false)) hbad)
        · rfl
      · simpa only [List.getD_eq_getElem?_getD,List.getElem?_append,List.length_ofFn,ite_eq_right h] using hi
    let step := fun (a : List Bool) (u : Finset ℕ × Finset ℕ) =>
      a ++ [decide (∀ i ∈ u.1, a.getD i false = true) || decide (∀ i ∈ u.2, a.getD i false = true)]
    have advance (a b : List Bool) (hab : lew a b) (u : Finset ℕ × Finset ℕ) :
        lew (step a u) (step b u) := by
      refine ⟨by simp [step, hab.1], ?_⟩
      intro i hi
      by_cases h : i < a.length
      · have hb : i < b.length := hab.1 ▸ h
        simpa [step,List.getD_eq_getElem?_getD,List.getElem?_append,h,hb] using
          (hab.2 i (by simpa [step,List.getD_eq_getElem?_getD,List.getElem?_append,h] using hi))
      · have hb : ¬i < b.length := hab.1 ▸ h
        by_cases he : i = a.length
        · subst i
          have hp : (∀ i ∈ u.1, a.getD i false = true) ∨ (∀ i ∈ u.2, a.getD i false = true) := by
            simpa [step,List.getD_eq_getElem?_getD,List.getElem?_append] using hi
          have hq : (∀ i ∈ u.1, b.getD i false = true) ∨ (∀ i ∈ u.2, b.getD i false = true) :=
            hp.imp (fun h i hi => hab.2 i (h i hi)) (fun h i hi => hab.2 i (h i hi))
          simpa [step,List.getD_eq_getElem?_getD,List.getElem?_append,hab.1] using hq
        · have ht : (step a u).length ≤ i := by simp [step]; omega
          simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none ht] at hi
    have go (q : List (Finset ℕ × Finset ℕ)) (a b : List Bool) (h : lew a b) :
        lew (q.foldl step a) (q.foldl step b) := by
      induction q generalizing a b with
      | nil => simpa using h
      | cons u q ih => exact ih _ _ (advance a b h u)
    exact go r _ _ base
  have output_mono (x y : Fin 42 → Bool) (hxy : x ≤ y) (hx : ev R o x = true) : ev R o y = true :=
    decide_eq_true (fun i hi => (mono x y hxy R).2 i ((of_decide_eq_true hx) i hi))
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
  exact incidence_34 R o exactR

end PEqualNP.Outside.PlaneFlag

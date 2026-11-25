import PEqualNP.Defs

-- A binary OR can merge at most two classes of singleton inputs. A final free conjunction
-- that rejects zero and accepts every singleton forces all 21 classes to merge.

namespace PEqualNP.Outside.PlaneAggregator

abbrev V := Fin 21
abbrev Input := V → Bool
abbrev Wire := Input → Bool
abbrev Row := Finset ℕ × Finset ℕ

def N (_p : V) : Finset V := Finset.univ
def one (l : V) : Input := fun j => decide (j = l)
def outsideN (p : V) : Input := fun l => decide (l ∉ N p)
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

def Safe (f : Wire) : Prop := ∀ p l, l ∉ N p → f (one l) = true → f (outsideN p) = true
def MonoColor (p : V) (c : V → V) (f : Wire) : Prop :=
  f (outsideN p) = false → ∀ i j, f (one i) = true → f (one j) = true → c i = c j
def Charged (p : V) (f : Wire) : Prop :=
  f (outsideN p) = false ∧ ∃ i j : V, i ≠ j ∧ f (one i) = true ∧ f (one j) = true
noncomputable def charges (p : V) (fs : List Wire) : ℕ := by
  classical exact (fs.filter fun f => decide (Charged p f)).length

theorem getD_prop {P : Wire → Prop} {ws : List Wire}
    (all : ∀ f ∈ ws, P f) (zero : P zeroWire) (i : ℕ) : P (ws.getD i zeroWire) := by
  by_cases h : i < ws.length
  · simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h] using all ws[i] (List.getElem_mem h)
  · simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_gt h)] using zero
theorem safe_zero : Safe zeroWire := by simp [Safe,zeroWire]
theorem mono_zero (p : V) (c : V → V) : MonoColor p c zeroWire := by simp [MonoColor,zeroWire]
theorem safe_inputs : ∀ f ∈ inputWires, Safe f := by
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · obtain ⟨j,hj⟩ := List.mem_ofFn.mp hf
    subst f
    intro p l hn hit
    have hjl : j = l := by simpa [one] using hit
    simpa [outsideN,hjl] using hn
  · have eq := List.mem_singleton.mp hf
    subst f; exact safe_zero
theorem mono_inputs (p : V) : ∀ f ∈ inputWires, MonoColor p id f := by
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · obtain ⟨v,hv⟩ := List.mem_ofFn.mp hf
    subst f
    intro d i j hi hj
    have hvi : v = i := by simpa [one] using hi
    have hvj : v = j := by simpa [one] using hj
    exact hvi.symm.trans hvj
  · have eq := List.mem_singleton.mp hf
    subst f
    exact mono_zero p _
theorem safe_and {ws : List Wire} (all : ∀ f ∈ ws, Safe f) (s : Finset ℕ) : Safe (conjunction ws s) := by
  intro p l hn hit
  apply decide_eq_true
  intro i hi
  exact getD_prop all safe_zero i p l hn ((of_decide_eq_true hit) i hi)
theorem safe_gate {ws : List Wire} (all : ∀ f ∈ ws, Safe f) (r : Row) : Safe (gate ws r) := by
  intro p l hn hit
  rcases Bool.or_eq_true_iff.mp hit with a|b
  · exact Bool.or_eq_true_iff.mpr (.inl (safe_and all r.1 p l hn a))
  · exact Bool.or_eq_true_iff.mpr (.inr (safe_and all r.2 p l hn b))
theorem safe_wires (R : List Row) : ∀ f ∈ wires R, Safe f := by
  induction R using List.reverseRecOn with
  | nil => simpa [wires,history] using safe_inputs
  | append_singleton R r ih =>
    rw [wires_snoc]
    intro f hf
    rcases List.mem_append.mp hf with a|b
    · exact ih f a
    · have eq := List.mem_singleton.mp b
      subst f; exact safe_gate ih r

theorem mono_and {cs : V → V} {p : V} {ws : List Wire} (all : ∀ f ∈ ws, MonoColor p cs f)
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

theorem one_color {p : V} {c : V → V} {f : Wire} (m : MonoColor p c f) (off : f (outsideN p) = false) :
    ∃ a : V, ∀ i, f (one i) = true → c i = a := by
  by_cases h : ∃ i, f (one i) = true
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

theorem recolor {p : V} {c : V → V} {ws : List Wire} (all : ∀ f ∈ ws, MonoColor p c f)
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
      have colored (i : V) (hi : gate ws r (one i) = true) : c' i = a := by
        rcases Bool.or_eq_true_iff.mp hi with u|v
        · simp [c',Function.comp_def,ha i u,identify]
        · simp [c',Function.comp_def,hb i v,identify]
      exact fun _ i j hi hj => (colored i hi).trans (colored j hj).symm
theorem uncharged {p : V} {c : V → V} {f : Wire} (h : ¬ Charged p f) : MonoColor p c f := by
  intro off i j hi hj
  by_cases e : i=j
  · simp [e]
  · exact (h ⟨off,i,j,e,hi,hj⟩).elim
theorem colors (p : V) (R : List Row) :
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

theorem aggregator_tests (R : List Row) (o : Finset ℕ)
    (neg : eval R o (fun _ => false) = false)
    (pos : ∀ l : V, eval R o (one l) = true) : 20 ≤ R.length := by
  classical
  obtain ⟨c,ct,all⟩ := colors 0 R
  have no : conjunction (wires R) o (outsideN 0) = false := by
    rw [interpret]
    have eq0 : outsideN 0 = (fun _ => false) := by
      funext i
      change decide (i ∉ (Finset.univ : Finset V)) = false
      simp
    rw [eq0]
    exact neg
  obtain ⟨a,ha⟩ := one_color (mono_and all o) no
  have sub : (N 0).image c ⊆ {a} := by
    intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_singleton.mpr (ha i ((interpret R o (one i)).trans (pos i)))
  have card := Finset.card_le_card sub
  rw [Finset.card_singleton] at card
  have n : (N 0).card = 21 := by decide
  rw [n] at ct
  have h : charges 0 (history R) ≤ (history R).length := List.length_filter_le _ _
  rw [history_length] at h
  omega

theorem aggregator_lower_bound :
  let ev := fun (A : List (Finset ℕ × Finset ℕ)) (c : Finset ℕ) (x : Fin 21 → Bool) =>
    let w := A.foldl (fun w r => w ++ [decide (∀ i ∈ r.1, w.getD i false = true) ||
                                        decide (∀ i ∈ r.2, w.getD i false = true)]) (List.ofFn x ++ [false])
    decide (∀ i ∈ c, w.getD i false = true)
  ∀ A c, ev A c (fun _ => false) = false →
    (∀ l : Fin 21, ev A c (fun j => decide (j = l)) = true) → 20 ≤ A.length := by
  dsimp only
  intro A c neg pos
  exact aggregator_tests A c neg pos
end PEqualNP.Outside.PlaneAggregator

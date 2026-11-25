import InducedCut
import RebuiltPrefix

namespace Checkpoint132.Induced
open Finset Checkpoint125 Checkpoint125.Binary Checkpoint130.Cut Checkpoint131.Rebuild
open PEqualNP.Outside.L_meta_3004_aux.Controls

def renamed (q : List ℕ) (v : V) : V := Fin.ofNat 14 (q.getD v.val 0)

def MapOK (t u : ℕ) (q : List ℕ) : Prop :=
  (∀ a : Slot t,u.testBit (renamed q a.val).val=true) ∧
  (∀ b : Slot u,∃ a : Slot t,renamed q a.val=b.val) ∧
  ∀ a b : Slot t, G.Adj (renamed q a.val) (renamed q b.val) ↔ adj a b
instance (t u) (q) : Decidable (MapOK t u q) := by unfold MapOK; infer_instance

theorem floorMono {t k ℓ} (ok : Floor t ℓ) (bound : k≤ℓ) : Floor t k :=
  fun gs e hb hr fit => bound.trans (ok gs e hb hr fit)

theorem relabel {t u k} (q : List ℕ) (valid : MapOK t u q) (floor : Floor u k) : Floor t k := by
  intro gs e hb hr fit
  let f (a : Slot t) : Slot u := ⟨renamed q a.val,valid.1 a⟩
  have onto (b : Slot u) : ∃ a,f a=b := by
    obtain ⟨a,eq⟩ := valid.2.1 b
    exact ⟨a,Subtype.ext eq⟩
  have truth (z : Slot u→Bool) : accepts (fun a => z (f a)) ↔ accepts z := by
    constructor
    · rintro ⟨a,b,edge,ha,hb⟩
      exact ⟨f a,f b,(valid.2.2 _ _).mpr edge,ha,hb⟩
    · rintro ⟨a,b,edge,ha,hb⟩
      obtain ⟨x,rfl⟩ := onto a
      obtain ⟨y,rfl⟩ := onto b
      exact ⟨x,y,(valid.2.2 _ _).mp edge,ha,hb⟩
  let atom (a : Slot t) := Binary.Tree.leaf (f a)
  have av (a) : Ready [] (atom a) := Or.inl ⟨_,rfl⟩
  have ok : Fits pv nv (graft atom e) :=
    ⟨fun r => (graftTruth atom (pv r) e).mpr (fit.1 ⟨_,(truth r.val).mpr r.property⟩),
     fun r h => fit.2 ⟨_,fun good => r.property ((truth r.val).mp good)⟩ ((graftTruth atom (nv r) e).mp h)⟩
  have lower := floor _ _ (graftBuilt atom (base:=[]) trivial av hb) (graftReady atom av hr) ok
  simpa using lower

structure Choice where
  domain : ℕ
  source : ℕ
  floor : ℕ
  hot : ℕ
  perm : List ℕ
  deriving DecidableEq, Inhabited

def Verified (t : ℕ) (r : Choice) := Good t r.domain r.hot ∧ hasEdge r.domain ∧ MapOK r.domain r.source r.perm
instance (t) (r) : Decidable (Verified t r) := by unfold Verified; infer_instance

def pick {t} (lookup : List ℕ) (op : Bool) (x y : Slot t) :=
  lookup.getD ((if op then 196 else 0)+14*x.val.val+y.val.val) 0

def Covered (t k : ℕ) (choices : List Choice) (lookup : List ℕ) : Prop :=
  ∀ (op : Bool) (x y : Slot t), x≠y →
    let i := pick lookup op x y
    let r := choices.getD i default
    i<choices.length ∧ outside r.domain x y ∧ k≤1+r.floor+price r.domain r.hot op x y
instance (t k) (choices) (lookup) : Decidable (Covered t k choices lookup) := by unfold Covered; infer_instance

theorem certified {t k} (choices : List Choice) (lookup : List ℕ)
    (lower : ∀ r∈choices,Floor r.source r.floor) (valid : ∀ r∈choices,Verified t r)
    (cover : Covered t k choices lookup) : Floor t k := by
  apply fromChoices
  intro op x y ne
  let i := pick lookup op x y
  let r := choices.getD i default
  obtain ⟨lt,out,bound⟩ := cover op x y ne
  have mem : r∈choices := by
    change choices.getD i default ∈ choices
    rw [List.getD_eq_getElem _ _ (show i<choices.length from lt)]
    exact List.getElem_mem _
  obtain ⟨good,edge,eq⟩ := valid r mem
  exact ⟨r.domain,r.hot,r.floor,good,edge,out,relabel r.perm eq (lower r mem),bound⟩

#print axioms relabel
#print axioms certified
end Checkpoint132.Induced

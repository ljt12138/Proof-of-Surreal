import data.list

inductive bintree : Type  
| single : bintree
| node_left : bintree → bintree
| node_right : bintree → bintree
| node : bintree → bintree → bintree

open bintree

notation `●` := single
notation `⟦` t `∣⟧` := node_left t
notation `⟦∣` t `⟧` := node_right t
notation `⟦` t `,` t' `⟧` := node t t'

@[simp]
def height : bintree → ℕ 
| ● := 1 
| ⟦ t ∣⟧ := 1 + height t
| ⟦∣ t ⟧ := 1 + height t
| ⟦t, t'⟧ := 1 + max (height t) (height t')

-- grow is inductively defined, slightly different from the report 

inductive grow : bintree → bintree → Prop 
| single_grow : ∀ t : bintree, grow ● t 
| left_grow : ∀ t t' : bintree, grow t t' → grow ⟦t ∣⟧ ⟦t' ∣⟧
| right_grow : ∀ t t' : bintree, grow t t' → grow ⟦∣ t⟧ ⟦∣ t'⟧
| full_grow : ∀ t1 t2 t1' t2' : bintree, grow t1 t1' → grow t2 t2' → 
                                      grow ⟦t1, t2⟧ ⟦t1', t2'⟧ 

notation t `↣` t' := grow t t'

inductive independent_list : list bintree → bintree → Prop
| nil : ∀ (t : bintree), independent_list [] t
| cons : ∀ (t t' : bintree) (l : list bintree), t ≠ t' → 
           independent_list l t' → independent_list (t :: l) t'

-- set is replaced by list, for simplicty
-- `grow_list l t` means that there is some t' ∈ l such that t' grows to t

inductive grow_list : list bintree → bintree → Prop 
| head_grow : ∀ (t t' : bintree) (l : list bintree), (t ↣ t') → grow_list (t :: l) t'
| tail_grow : ∀ (t t' : bintree) (l : list bintree), grow_list l t' → grow_list (t :: l) t'  

notation t `↦` t' := grow_list t t'

-- `grow_some l l'` means that there is some t ∈ l' such that grow_list l t

inductive grow_some : list bintree → list bintree → Prop
| head_grow : ∀ (t : bintree) (l l' : list bintree), (l ↦ t) → grow_some l (t :: l')
| tail_grow : ∀ (t : bintree) (l l' : list bintree), (grow_some l l') → grow_some l (t :: l)

inductive non_isomorphic : list bintree → Prop 
| nil : non_isomorphic []
| cons : ∀ (l : list bintree) (t : bintree), non_isomorphic l → independent_list l t 
                                       → non_isomorphic (t :: l) 

-- a list of bintree l is called /complete/, 
--  if for any sufficiently long non-isomorphic list l' of bintree, 
--  there exists a bintree t ∈ l' such that l ↦ t 

inductive almost_complete : list bintree → Prop
| cmp_rule : ∀ (l : list bintree), 
               (∃ l' : list bintree, (∀ t, ¬(l ↦ t) → t ∈ l')) → almost_complete l

-- branch is a property over bintree, see branch.lean for lemmas

inductive is_branch : bintree → Prop
| single : is_branch ●
| left_nl : ∀ t : bintree, is_branch t → is_branch ⟦t ∣⟧ 
| left_l : ∀ t : bintree, is_branch t → is_branch ⟦t, ●⟧
| right_nl : ∀ t : bintree, is_branch t → is_branch ⟦∣ t⟧
| right_l : ∀ t : bintree, is_branch t → is_branch ⟦●, t⟧

inductive is_son : bintree → bintree → Prop
| left_left : ∀ t : bintree, is_son t ⟦t ∣⟧
| left_full : ∀ t t' : bintree, is_son t ⟦t, t'⟧
| right_right : ∀ t : bintree, is_son t ⟦∣ t⟧
| right_full : ∀ t t' : bintree, is_son t ⟦t', t⟧ 

notation `⟨` b `⟩` := is_branch b


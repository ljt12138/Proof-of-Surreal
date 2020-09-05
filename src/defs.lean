import data.list

inductive tree : Type  
| single : tree
| node_left : tree → tree
| node_right : tree → tree
| node : tree → tree → tree

open tree

notation `●` := single
notation `⟦` t `∣⟧` := node_left t
notation `⟦∣` t `⟧` := node_right t
notation `⟦` t `,` t' `⟧` := node t t'

def height : tree → ℕ 
| ● := 1 
| ⟦ t ∣⟧ := 1 + height t
| ⟦∣ t ⟧ := 1 + height t
| ⟦t, t'⟧ := 1 + max (height t) (height t')

-- grow is inductively defined, slightly different from the report 

inductive grow : tree → tree → Prop 
| single_grow : ∀ t : tree, grow ● t 
| left_grow : ∀ t t' : tree, grow t t' → grow ⟦t ∣⟧ ⟦t' ∣⟧
| right_grow : ∀ t t' : tree, grow t t' → grow ⟦∣ t⟧ ⟦∣ t'⟧
| full_grow : ∀ t1 t2 t1' t2' : tree, grow t1 t1' → grow t2 t2' → 
                                      grow ⟦t1, t2⟧ ⟦t1', t2'⟧ 

notation t `↣` t' := grow t t'

inductive independent_list : list tree → tree → Prop
| nil : ∀ (t : tree), independent_list [] t
| cons : ∀ (t t' : tree) (l : list tree), t ≠ t' → 
           independent_list l t' → independent_list (t :: l) t'

-- set is replaced by list, for simplicty
-- `grow_list l t` means that there is some t' ∈ l such that t' grows to t

inductive grow_list : list tree → tree → Prop 
| head_grow : ∀ (t t' : tree) (l : list tree), (t ↣ t') → grow_list (t :: l) t'
| tail_grow : ∀ (t t' : tree) (l : list tree), grow_list l t' → grow_list (t :: l) t'  

notation t `↦` t' := grow_list t t'

-- `grow_some l l'` means that there is some t ∈ l' such that grow_list l t

inductive grow_some : list tree → list tree → Prop
| head_grow : ∀ (t : tree) (l l' : list tree), (l ↦ t) → grow_some l (t :: l')
| tail_grow : ∀ (t : tree) (l l' : list tree), (grow_some l l') → grow_some l (t :: l)

inductive non_isomorphic : list tree → Prop 
| nil : non_isomorphic []
| cons : ∀ (l : list tree) (t : tree), non_isomorphic l → independent_list l t 
                                       → non_isomorphic (t :: l) 

-- a list of tree l is called /complete/, 
--  if for any sufficiently long non-isomorphic list l' of tree, 
--  there exists a tree t ∈ l' such that l ↦ t 

inductive almost_complete : list tree → Prop
| cmp_rule : ∀ (l : list tree), 
               (∃ l' : list tree, (∀ t, ¬(l ↦ t) → t ∈ l')) → almost_complete l

-- branch is a property over tree, see branch.lean for lemmas

inductive is_branch : tree → Prop
| single : is_branch ●
| left_nl : ∀ t : tree, is_branch t → is_branch ⟦t ∣⟧ 
| left_l : ∀ t : tree, is_branch t → is_branch ⟦t, ●⟧
| right_nl : ∀ t : tree, is_branch t → is_branch ⟦∣ t⟧
| right_l : ∀ t : tree, is_branch t → is_branch ⟦●, t⟧

inductive is_son : tree → tree → Prop
| left_left : ∀ t : tree, is_son t ⟦t ∣⟧
| left_full : ∀ t t' : tree, is_son t ⟦t, t'⟧
| right_right : ∀ t : tree, is_son t ⟦∣ t⟧
| right_full : ∀ t t' : tree, is_son t ⟦t', t⟧ 

notation `⟨` b `⟩` := is_branch b


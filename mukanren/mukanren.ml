open Core;;

type variable = int
type 'a term = 
    | Variable of variable
    | Value of 'a
    | TermList of ('a term) list
type 'a substitution = (variable * 'a term) list;;
type 'a state = 'a substitution * int
type 
    'a immature_stream = unit -> 'a stream and 
    'a stream = 
    | Empty_stream
    | Mature_stream of 'a state * 'a stream 
    | Immature_stream of 'a immature_stream
type 'a goal = 'a state -> 'a stream

let walk (var : 'a term) (substitution : 'a substitution) =
    match var with 
    | Variable v -> 
        (match List.Assoc.find substitution v ~equal:Int.equal with
        | Some term -> term
        | _ -> Variable v)
    | nonvariable -> nonvariable

let empty_state : 'a state = ([], 0)
let ext_s (var : variable) (term : 'a term) (subst : 'a substitution) = (var, term) :: subst 

let rec term_equal term1 term2 = 
    match term1, term2 with 
    | Variable v1, Variable v2 -> v1 = v2
    | Value v1, Value v2 -> Poly.(=) v1 v2
    | TermList v1, TermList v2 -> List.equal term_equal v1 v2
    | _ -> false

let rec unify u v subst = 
    let u_term = walk u subst in 
    let v_term = walk v subst in 
    match u_term, v_term with 
    | Variable u_var, Variable v_var when u_var = v_var -> subst
    | Variable u_var, v_term -> ext_s u_var v_term subst
    | u_term, Variable v_var -> ext_s v_var u_term subst
    | TermList [], _ | _, TermList [] -> []
    | TermList u_list, TermList v_list ->
        let subst' = unify (List.hd_exn u_list) (List.hd_exn v_list) subst in
        let subst'' = unify (TermList (List.tl_exn u_list)) (TermList (List.tl_exn v_list)) subst' in
        subst''
    | u_term, v_term when term_equal u_term v_term -> subst
    | _ -> []

let mzero = Empty_stream
let unit s_c : 'a stream = Mature_stream (s_c, mzero)
let equals u v : 'a goal = 
    fun (substitution, counter) ->
        let s = unify u v substitution in
        if List.length s > 0 then unit (s, counter)
        else Empty_stream

let call_fresh (f : int -> 'a state -> 'a stream) : 'a goal = 
    fun (substitution, counter) -> 
        f counter (substitution, counter + 1)

let rec mplus (s1 : 'a stream) (s2 : 'a stream) =
    match s1 with 
    | Empty_stream -> s2
    | Immature_stream s1 -> (Immature_stream (fun () -> mplus s2 (s1 ())))
    | Mature_stream (state, stream) -> Mature_stream (state, mplus stream s2)        

let rec bind s (g : 'a state -> 'a stream) = match s with 
    | Empty_stream -> mzero
    | Immature_stream s -> Immature_stream (fun () -> bind (s ()) g)
    | Mature_stream (state, stream) -> mplus (g state) (bind stream g)

let disj (g1 : 'a state -> 'a stream) (g2 : 'a state -> 'a stream) = 
    fun sc -> mplus (g1 sc) (g2 sc)
let conj (g1 : 'a state -> 'a stream) (g2 : 'a state -> 'a stream) = 
    fun sc -> bind (g1 sc) g2 